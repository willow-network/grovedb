use std::collections::{BTreeMap, BTreeSet};

use grovedb_merk::{
    proofs::{
        query::{PathKey, VerifyOptions},
        ProofRules, Query,
    },
    tree::{combine_hash, value_hash, NULL_HASH},
    CryptoHash, TreeFeatureType, TreeType,
};
use grovedb_version::{
    check_grovedb_v0, version::GroveVersion, TryFromVersioned, TryIntoVersioned,
};

#[cfg(feature = "proof_debug")]
use crate::operations::proof::util::{
    hex_to_ascii, path_as_slices_hex_to_ascii, path_hex_to_ascii,
};
use crate::{
    operations::proof::{
        envelope_depth_within,
        util::{ProvedPathKeyOptionalValue, ProvedPathKeyValues},
        GroveDBProof, GroveDBProofV0, LayerProof, ProveOptions, MAX_STRICT_PROOF_DEPTH,
        MAX_V310_PROOF_DEPTH,
    },
    query_result_type::PathKeyOptionalElementTrio,
    Element, Error, GroveDb, PathQuery,
};

/// The longest proof envelope strict verification decodes (upstream GroveDB's
/// bound).
const STRICT_MAX_PROOF_BYTES: usize = 256 * 1024 * 1024;

/// The claim limit for decoding `len` bytes: the smallest power of two at
/// least 32 times `len`, and at least 1 KiB; `None` past the largest class
/// [`decode_in_class`] has.
///
/// grovedb 3.1.0 decodes proofs and elements with no limit, and bincode
/// 2.0.0-rc.3 resizes a byte string to its claimed length (zeroing it) before
/// reading it: a few bytes claiming an enormous length abort the process, and
/// a fixed large limit still lets each few bytes force a large zeroed
/// allocation. bincode also claims `len * size_of::<T>()` for a container of
/// `T` before reading it, and releases that claim one element at a time as it
/// decodes them. The containers a proof envelope and an element decode are
/// byte strings (one byte claimed per byte read), `Vec<Vec<u8>>` (a reference
/// path: 24 bytes claimed per segment, each at least 1 serialized byte) and
/// `BTreeMap<Vec<u8>, LayerProof>` (the lower layers: 72 bytes claimed per
/// entry, each at least 3 serialized bytes), so at most 24 bytes are claimed
/// per serialized byte, and a decode that the input can satisfy claims at
/// most 25 times the input's length. A claim past 32 times it cannot be
/// satisfied, and a lying length can make the decoder allocate at most about
/// 64 times the input.
fn claim_class(len: usize) -> Option<usize> {
    let class = len
        .saturating_mul(32)
        .max(1 << 10)
        .checked_next_power_of_two()?;
    (class <= MAX_CLAIM_CLASS).then_some(class)
}

#[cfg(target_pointer_width = "64")]
const MAX_CLAIM_CLASS: usize = 1 << 33;
#[cfg(not(target_pointer_width = "64"))]
const MAX_CLAIM_CLASS: usize = 1 << 31;

/// Decodes `bytes` with GroveDB's bincode configuration under
/// `min(claim_class(len), cap)`, for [`ProofRules::Strict`]. `cap` must be a
/// power of two of at least 1 KiB.
fn decode_bounded<T: bincode::Decode>(
    bytes: &[u8],
    cap: usize,
) -> Result<(T, usize), bincode::error::DecodeError> {
    let class = claim_class(bytes.len()).map_or(cap, |c| c.min(cap));
    decode_in_class(bytes, class)
}

/// Decodes `bytes` as grovedb 3.1.0 does, for [`ProofRules::V310`], except
/// under the claim limit [`claim_class`] gives. A decode that 3.1.0 completes
/// claims at most 25 times the input's length, under that limit, so it
/// decodes identically; one that claims more cannot be satisfied by the
/// input, so 3.1.0 fails on it too (or, allocating the claim, aborts), and
/// this returns an error instead. Past the largest class (inputs over 256 MiB
/// on 64-bit targets) it decodes with no limit, as 3.1.0.
fn decode_v310<T: bincode::Decode>(
    bytes: &[u8],
) -> Result<(T, usize), bincode::error::DecodeError> {
    match claim_class(bytes.len()) {
        Some(class) => decode_in_class(bytes, class),
        None => bincode::decode_from_slice(
            bytes,
            bincode::config::standard()
                .with_big_endian()
                .with_no_limit(),
        ),
    }
}

/// Strict caps on a decode's claim limit: the envelope's (upstream GroveDB's
/// bound) and an element's (the merk decoder's value cap).
const STRICT_ENVELOPE_CLAIM_CAP: usize = 1 << 28;
const STRICT_ELEMENT_CLAIM_CAP: usize = 1 << 26;

macro_rules! decode_in_classes {
    ($bytes:expr, $class:expr, $($bits:literal)*) => {
        match $class {
            $(
                c if c == 1usize << $bits => bincode::decode_from_slice(
                    $bytes,
                    bincode::config::standard()
                        .with_big_endian()
                        .with_limit::<{ 1usize << $bits }>(),
                ),
            )*
            _ => Err(bincode::error::DecodeError::LimitExceeded),
        }
    };
}

#[cfg(target_pointer_width = "64")]
fn decode_in_class<T: bincode::Decode>(
    bytes: &[u8],
    class: usize,
) -> Result<(T, usize), bincode::error::DecodeError> {
    decode_in_classes!(
        bytes, class,
        10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33
    )
}

#[cfg(not(target_pointer_width = "64"))]
fn decode_in_class<T: bincode::Decode>(
    bytes: &[u8],
    class: usize,
) -> Result<(T, usize), bincode::error::DecodeError> {
    decode_in_classes!(
        bytes, class,
        10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31
    )
}

impl GroveDb {
    /// Decodes a proof envelope. Under either rule set the envelope's nesting
    /// is checked first, without recursion ([`envelope_depth_within`]), since
    /// bincode decodes each level of nesting one stack frame deeper.
    /// [`ProofRules::V310`] is then 3.1.0's decode, trailing bytes ignored,
    /// under [`decode_v310`]'s claim limit. [`ProofRules::Strict`] refuses an
    /// envelope over [`STRICT_MAX_PROOF_BYTES`], decodes with
    /// [`decode_bounded`], and refuses trailing bytes.
    fn decode_proof_with_rules(proof: &[u8], rules: ProofRules) -> Result<GroveDBProof, Error> {
        let decode_error = |e| Error::CorruptedData(format!("unable to decode proof: {}", e));
        let max_depth = match rules {
            ProofRules::V310 => MAX_V310_PROOF_DEPTH,
            ProofRules::Strict => MAX_STRICT_PROOF_DEPTH,
        };
        if !envelope_depth_within(proof, max_depth) {
            return Err(Error::CorruptedData(format!(
                "unable to decode proof: its layers nest more than {} deep",
                max_depth
            )));
        }
        match rules {
            ProofRules::V310 => Ok(decode_v310(proof).map_err(decode_error)?.0),
            ProofRules::Strict => {
                if proof.len() > STRICT_MAX_PROOF_BYTES {
                    return Err(Error::CorruptedData(format!(
                        "unable to decode proof: {} bytes; at most {} are verified",
                        proof.len(),
                        STRICT_MAX_PROOF_BYTES
                    )));
                }
                let (grovedb_proof, used) =
                    decode_bounded(proof, STRICT_ENVELOPE_CLAIM_CAP).map_err(decode_error)?;
                if used != proof.len() {
                    return Err(Error::CorruptedData(format!(
                        "unable to decode proof: {} trailing bytes after the encoded proof",
                        proof.len() - used
                    )));
                }
                Ok(grovedb_proof)
            }
        }
    }

    /// Decodes a proved element as [`Element::deserialize`] does, with a
    /// claim limit: [`decode_v310`]'s under [`ProofRules::V310`] (where 3.1.0
    /// decodes one: each element in a visited layer's result set), and
    /// [`decode_bounded`]'s under [`ProofRules::Strict`]. A node value that
    /// claims a length it doesn't carry is refused instead of allocated.
    fn deserialize_element(
        bytes: &[u8],
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<Element, Error> {
        check_grovedb_v0!(
            "Element::deserialize",
            grove_version.grovedb_versions.element.deserialize
        );
        let decoded = match rules {
            ProofRules::V310 => decode_v310(bytes),
            ProofRules::Strict => decode_bounded(bytes, STRICT_ELEMENT_CLAIM_CAP),
        };
        Ok(decoded
            .map_err(|e| Error::CorruptedData(format!("unable to deserialize element {}", e)))?
            .0)
    }

    /// Verifies `proof` for `query` with the given options, under
    /// [`ProofRules::Strict`] (see [`GroveDb::verify_query`]).
    pub fn verify_query_with_options(
        proof: &[u8],
        query: &PathQuery,
        options: VerifyOptions,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        Self::verify_query_with_options_and_rules(
            proof,
            query,
            options,
            ProofRules::Strict,
            grove_version,
        )
    }

    /// [`GroveDb::verify_query_with_options`] under the given rules.
    pub fn verify_query_with_options_and_rules(
        proof: &[u8],
        query: &PathQuery,
        options: VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_query_with_options",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_query_with_options
        );
        if options.absence_proofs_for_non_existing_searched_keys {
            // must have a limit
            query.query.limit.ok_or(Error::NotSupported(
                "limits must be set in verify_query_with_absence_proof".to_string(),
            ))?;
        }

        // must have no offset
        if query.query.offset.is_some() {
            return Err(Error::NotSupported(
                "offsets in path queries are not supported for proofs".to_string(),
            ));
        }

        let grovedb_proof = Self::decode_proof_with_rules(proof, rules)?;

        let (root_hash, _, result) =
            Self::verify_proof_internal(&grovedb_proof, query, options, rules, grove_version)?;

        Ok((root_hash, result))
    }

    /// The point of this query is to get the parent tree information which will
    /// be present because we are querying in a subtree
    pub fn verify_query_get_parent_tree_info_with_options(
        proof: &[u8],
        query: &PathQuery,
        options: VerifyOptions,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, TreeFeatureType, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_query_get_parent_tree_info_with_options",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_query_get_parent_tree_info_with_options
        );

        if query.query.query.has_subquery() {
            return Err(Error::NotSupported(
                "getting the parent tree info is not available when using subqueries".to_string(),
            ));
        }
        if options.absence_proofs_for_non_existing_searched_keys {
            // must have a limit
            query.query.limit.ok_or(Error::NotSupported(
                "limits must be set in verify_query_with_absence_proof".to_string(),
            ))?;
        }

        // must have no offset
        if query.query.offset.is_some() {
            return Err(Error::NotSupported(
                "offsets in path queries are not supported for proofs".to_string(),
            ));
        }

        let grovedb_proof = Self::decode_proof_with_rules(proof, ProofRules::Strict)?;

        let (root_hash, tree_feature_type, result) = Self::verify_proof_internal(
            &grovedb_proof,
            query,
            options,
            ProofRules::Strict,
            grove_version,
        )?;

        let tree_feature_type = tree_feature_type.ok_or(Error::InvalidProof(
            query.clone(),
            "query had no parent tree info, maybe it was for for root tree".to_string(),
        ))?;

        Ok((root_hash, tree_feature_type, result))
    }

    /// Verifies `proof` for `query` and returns the raw proved path/key/value
    /// rows, under [`ProofRules::Strict`] (see [`GroveDb::verify_query`]).
    pub fn verify_query_raw(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, ProvedPathKeyValues), Error> {
        Self::verify_query_raw_with_rules(proof, query, ProofRules::Strict, grove_version)
    }

    /// [`GroveDb::verify_query_raw`] exactly as grovedb 3.1.0 ran it: the
    /// large-value opcodes are unknown opcodes, `Hash` nodes may take
    /// children, and none of the strict element checks run. For replaying
    /// verdicts reached with 3.1.0; anything else should call
    /// [`GroveDb::verify_query_raw`].
    ///
    /// It differs from 3.1.0 only where 3.1.0 can abort the process, as
    /// [`GroveDb::verify_query_v310`] does.
    pub fn verify_query_raw_v310(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, ProvedPathKeyValues), Error> {
        Self::verify_query_raw_with_rules(proof, query, ProofRules::V310, grove_version)
    }

    /// [`GroveDb::verify_query_raw`] under the given rules.
    pub fn verify_query_raw_with_rules(
        proof: &[u8],
        query: &PathQuery,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, ProvedPathKeyValues), Error> {
        check_grovedb_v0!(
            "verify_query_raw",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_query_raw
        );
        let grovedb_proof = Self::decode_proof_with_rules(proof, rules)?;

        let (root_hash, _, result) = Self::verify_proof_raw_internal(
            &grovedb_proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: false,
                verify_proof_succinctness: false,
                include_empty_trees_in_result: true,
            },
            rules,
            grove_version,
        )?;

        Ok((root_hash, result))
    }

    pub(crate) fn verify_proof_internal(
        proof: &GroveDBProof,
        query: &PathQuery,
        options: VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<
        (
            CryptoHash,
            Option<TreeFeatureType>,
            Vec<PathKeyOptionalElementTrio>,
        ),
        Error,
    > {
        match proof {
            GroveDBProof::V0(proof_v0) => {
                Self::verify_proof_v0_internal(proof_v0, query, options, rules, grove_version)
            }
        }
    }

    fn verify_proof_v0_internal(
        proof: &GroveDBProofV0,
        query: &PathQuery,
        options: VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<
        (
            CryptoHash,
            Option<TreeFeatureType>,
            Vec<PathKeyOptionalElementTrio>,
        ),
        Error,
    > {
        let mut result = Vec::new();
        let mut limit = query.query.limit;
        let mut last_tree_feature_type = None;
        let root_hash = Self::verify_layer_proof(
            &proof.root_layer,
            &proof.prove_options,
            query,
            &mut limit,
            &[],
            &mut result,
            &mut last_tree_feature_type,
            &options,
            rules,
            grove_version,
        )?;

        if options.absence_proofs_for_non_existing_searched_keys {
            // must have a limit
            let max_results = query.query.limit.ok_or(Error::NotSupported(
                "limits must be set in verify_query_with_absence_proof".to_string(),
            ))? as usize;

            let terminal_keys = query.terminal_keys(max_results, grove_version)?;

            // convert the result set to a btree map
            let mut result_set_as_map: BTreeMap<PathKey, Option<Element>> = result
                .into_iter()
                .map(|(path, key, element)| ((path, key), element))
                .collect();
            #[cfg(feature = "proof_debug")]
            {
                println!(
                    "terminal keys are [{}] \n result set is [{}]",
                    terminal_keys
                        .iter()
                        .map(|(path, key)| format!(
                            "path: {} key: {}",
                            path_hex_to_ascii(path),
                            hex_to_ascii(key)
                        ))
                        .collect::<Vec<_>>()
                        .join(", "),
                    result_set_as_map
                        .iter()
                        .map(|((path, key), e)| {
                            let element_string = if let Some(e) = e {
                                e.to_string()
                            } else {
                                "None".to_string()
                            };
                            format!(
                                "path: {} key: {} element: {}",
                                path_hex_to_ascii(path),
                                hex_to_ascii(key),
                                element_string,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            result = terminal_keys
                .into_iter()
                .map(|terminal_key| {
                    let element = result_set_as_map.remove(&terminal_key).flatten();
                    (terminal_key.0, terminal_key.1, element)
                })
                .collect();
        }

        Ok((root_hash, last_tree_feature_type, result))
    }

    pub(crate) fn verify_proof_raw_internal(
        proof: &GroveDBProof,
        query: &PathQuery,
        options: VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Option<TreeFeatureType>, ProvedPathKeyValues), Error> {
        match proof {
            GroveDBProof::V0(proof_v0) => {
                Self::verify_proof_raw_internal_v0(proof_v0, query, options, rules, grove_version)
            }
        }
    }

    fn verify_proof_raw_internal_v0(
        proof: &GroveDBProofV0,
        query: &PathQuery,
        options: VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Option<TreeFeatureType>, ProvedPathKeyValues), Error> {
        let mut result = Vec::new();
        let mut limit = query.query.limit;
        let mut last_tree_feature_type = None;
        let root_hash = Self::verify_layer_proof(
            &proof.root_layer,
            &proof.prove_options,
            query,
            &mut limit,
            &[],
            &mut result,
            &mut last_tree_feature_type,
            &options,
            rules,
            grove_version,
        )?;
        Ok((root_hash, last_tree_feature_type, result))
    }

    fn verify_layer_proof<T>(
        layer_proof: &LayerProof,
        prove_options: &ProveOptions,
        query: &PathQuery,
        limit_left: &mut Option<u16>,
        current_path: &[&[u8]],
        result: &mut Vec<T>,
        last_parent_tree_type: &mut Option<TreeFeatureType>,
        options: &VerifyOptions,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<CryptoHash, Error>
    where
        T: TryFromVersioned<ProvedPathKeyOptionalValue>,
        Error: From<<T as TryFromVersioned<ProvedPathKeyOptionalValue>>::Error>,
    {
        check_grovedb_v0!(
            "verify_layer_proof",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_layer_proof
        );
        let internal_query = query
            .query_items_at_path(current_path, grove_version)?
            .ok_or(Error::CorruptedPath(format!(
                "verify raw: path {} should be part of path_query {}",
                current_path
                    .iter()
                    .map(hex::encode)
                    .collect::<Vec<_>>()
                    .join("/"),
                query
            )))?;

        let level_query = Query {
            items: internal_query.items.to_vec(),
            left_to_right: internal_query.left_to_right,
            ..Default::default()
        };

        let (root_hash, merk_result) = level_query
            .execute_proof_with_rules(
                &layer_proof.merk_proof,
                *limit_left,
                internal_query.left_to_right,
                rules,
                |value, supplied_value_hash| match rules {
                    ProofRules::Strict => Self::check_supplied_value_hash_strict(
                        value,
                        supplied_value_hash,
                        grove_version,
                    ),
                    ProofRules::V310 => Ok(()),
                },
            )
            .unwrap()
            .map_err(|e| {
                eprintln!("{e}");
                Error::InvalidProof(
                    query.clone(),
                    format!("Invalid proof verification parameters: {}", e),
                )
            })?;
        #[cfg(feature = "proof_debug")]
        {
            println!(
                "current path {} \n merk result is {}",
                path_as_slices_hex_to_ascii(current_path),
                merk_result
            );
        }

        let mut verified_keys = BTreeSet::new();

        if merk_result.result_set.is_empty() {
            if prove_options.decrease_limit_on_empty_sub_query_result {
                limit_left.iter_mut().for_each(|limit| *limit -= 1);
            }
        } else {
            for proved_key_value in merk_result.result_set {
                let mut path = current_path.to_vec();
                let key = &proved_key_value.key;
                let hash = &proved_key_value.proof;
                if let Some(value_bytes) = &proved_key_value.value {
                    let element = Self::deserialize_element(value_bytes, rules, grove_version)?;

                    if rules == ProofRules::Strict {
                        Self::check_proved_element_strict(
                            query,
                            current_path,
                            key,
                            hash,
                            value_bytes,
                            &element,
                            layer_proof,
                        )?;
                    }

                    verified_keys.insert(key.clone());

                    if let Some(lower_layer) = layer_proof.lower_layers.get(key) {
                        #[cfg(feature = "proof_debug")]
                        {
                            println!("lower layer had key {}", hex_to_ascii(key));
                        }
                        match element {
                            Element::Tree(Some(_), _)
                            | Element::SumTree(Some(_), ..)
                            | Element::BigSumTree(Some(_), ..)
                            | Element::CountTree(Some(_), ..)
                            | Element::CountSumTree(Some(_), ..) => {
                                path.push(key);
                                *last_parent_tree_type = element.tree_feature_type();
                                if query.query_items_at_path(&path, grove_version)?.is_none() {
                                    // We are actually looking for the tree
                                    let path_key_optional_value =
                                        ProvedPathKeyOptionalValue::from_proved_key_value(
                                            path.iter().map(|p| p.to_vec()).collect(),
                                            proved_key_value,
                                        );
                                    #[cfg(feature = "proof_debug")]
                                    {
                                        println!(
                                            "pushing {} limit left after is {:?}",
                                            &path_key_optional_value, limit_left
                                        );
                                    }
                                    result.push(
                                        path_key_optional_value
                                            .try_into_versioned(grove_version)?,
                                    );

                                    limit_left.iter_mut().for_each(|limit| *limit -= 1);
                                    if limit_left == &Some(0) {
                                        break;
                                    }
                                } else {
                                    if query.should_add_parent_tree_at_path(
                                        current_path,
                                        grove_version,
                                    )? {
                                        let path_key_optional_value =
                                            ProvedPathKeyOptionalValue::from_proved_key_value(
                                                path.iter().map(|p| p.to_vec()).collect(),
                                                proved_key_value.clone(),
                                            );

                                        result.push(
                                            path_key_optional_value
                                                .try_into_versioned(grove_version)?,
                                        );
                                    }
                                    let lower_hash = Self::verify_layer_proof(
                                        lower_layer,
                                        prove_options,
                                        query,
                                        limit_left,
                                        &path,
                                        result,
                                        last_parent_tree_type,
                                        options,
                                        rules,
                                        grove_version,
                                    )?;
                                    let combined_root_hash =
                                        combine_hash(value_hash(value_bytes).value(), &lower_hash)
                                            .value()
                                            .to_owned();
                                    if hash != &combined_root_hash {
                                        return Err(Error::InvalidProof(
                                            query.clone(),
                                            format!(
                                                "Mismatch in lower layer hash, expected {}, got {}",
                                                hex::encode(hash),
                                                hex::encode(combined_root_hash)
                                            ),
                                        ));
                                    }
                                    if limit_left == &Some(0) {
                                        break;
                                    }
                                }
                            }
                            Element::Tree(None, _)
                            | Element::SumTree(None, ..)
                            | Element::BigSumTree(None, ..)
                            | Element::CountTree(None, ..)
                            | Element::CountSumTree(None, ..)
                            | Element::SumItem(..)
                            | Element::Item(..)
                            | Element::Reference(..) => {
                                return Err(Error::InvalidProof(
                                    query.clone(),
                                    "Proof has lower layer for a non Tree.".to_string(),
                                ));
                            }
                        }
                    } else if element.is_any_item()
                        || !internal_query.has_subquery_or_matching_in_path_on_key(key)
                            && (options.include_empty_trees_in_result
                                || !matches!(element, Element::Tree(None, _)))
                    {
                        let path_key_optional_value =
                            ProvedPathKeyOptionalValue::from_proved_key_value(
                                path.iter().map(|p| p.to_vec()).collect(),
                                proved_key_value,
                            );
                        #[cfg(feature = "proof_debug")]
                        {
                            println!(
                                "pushing {} limit left after is {:?}",
                                &path_key_optional_value, limit_left
                            );
                        }
                        result.push(path_key_optional_value.try_into_versioned(grove_version)?);

                        limit_left.iter_mut().for_each(|limit| *limit -= 1);
                        if limit_left == &Some(0) {
                            break;
                        }
                    } else {
                        // A subquery applies to the key and the proof has no
                        // layer below it. For a tree with a root key, 3.1.0
                        // skips the key silently, so a prover could drop
                        // every row under it (or present an item as such a
                        // tree) at the honest root; strict refuses it.
                        if rules == ProofRules::Strict
                            && matches!(
                                element,
                                Element::Tree(Some(_), _)
                                    | Element::SumTree(Some(_), ..)
                                    | Element::BigSumTree(Some(_), ..)
                                    | Element::CountTree(Some(_), ..)
                                    | Element::CountSumTree(Some(_), ..)
                            )
                        {
                            return Err(Error::InvalidProof(
                                query.clone(),
                                format!(
                                    "Proof has no lower layer for the non-empty tree at key {}, \
                                     which the query's subquery descends",
                                    hex::encode(key)
                                ),
                            ));
                        }
                        #[cfg(feature = "proof_debug")]
                        {
                            println!(
                                "we have subquery on key {} with value {}: {}",
                                hex_to_ascii(key),
                                element,
                                level_query
                            )
                        }
                    }
                }
            }
        }

        Ok(root_hash)
    }

    /// Strict rule, run (through merk) on every `KVValueHash` node: the
    /// prover supplies such a node's value hash instead of the verifier
    /// computing it, which is legitimate only for elements committed under a
    /// combined value hash (trees and references). An `Item` or `SumItem` is
    /// committed as `value_hash(bytes)`, so its bytes must hash to the
    /// supplied value hash. This refuses the KV→KVValueHash forgery
    /// (upstream dashpay/grovedb `da308f7f`): `KVValueHash(k, forged,
    /// value_hash(real))` hashes like `KV(k, real)` and would otherwise
    /// return `forged` at the honest root. It recomputes the hash rather than
    /// refusing items outright because the 3.1.0 prover sends a `SumItem`
    /// (and an item past the limit) as `KVValueHash`, with an honest hash.
    ///
    /// Likewise an empty tree (any tree element with no root key) is committed
    /// as `combine_hash(value_hash(bytes), NULL_HASH)`, so its bytes must give
    /// the supplied value hash that way; otherwise any key, an item's included,
    /// could be presented as an empty tree (a forged absence, at the root the
    /// proof claims). A tree element with a root key cannot be bound here: its
    /// value hash combines its bytes with the subtree's root, which the proof
    /// carries only as a lower layer (checked when present). A value that
    /// doesn't decode as an element is refused.
    fn check_supplied_value_hash_strict(
        value: &[u8],
        supplied_value_hash: &CryptoHash,
        grove_version: &GroveVersion,
    ) -> Result<(), grovedb_merk::error::Error> {
        let refuse = |m: String| Err(grovedb_merk::error::Error::InvalidProofError(m));
        let element = match Self::deserialize_element(value, ProofRules::Strict, grove_version) {
            Ok(element) => element,
            // Every value in a GroveDB merk tree is a serialized element.
            Err(e) => return refuse(format!("KVValueHash node value is not an element: {e}")),
        };
        match element {
            Element::Item(..) | Element::SumItem(..)
                if value_hash(value).value() != supplied_value_hash =>
            {
                refuse(
                    "KVValueHash node carries an item element whose bytes do not hash to its \
                     value hash"
                        .to_string(),
                )
            }
            Element::Tree(None, _)
            | Element::SumTree(None, ..)
            | Element::BigSumTree(None, ..)
            | Element::CountTree(None, ..)
            | Element::CountSumTree(None, ..)
                if &combine_hash(value_hash(value).value(), &NULL_HASH).unwrap()
                    != supplied_value_hash =>
            {
                refuse(
                    "KVValueHash node carries an empty tree element not bound to its value hash"
                        .to_string(),
                )
            }
            _ => Ok(()),
        }
    }

    /// Strict rules, run on every proved element the verifier processes:
    ///
    /// 1. No `Reference` element. The prover resolves every reference it
    ///    returns into a `KVRefValueHash` node carrying the referenced element,
    ///    so a `Reference` here came in a `KVValueHash` node whose value hash
    ///    the verifier cannot check against its bytes (a forged reference
    ///    standing in for the real one).
    /// 2. No tree element under the plain `value_hash` of its bytes (a `KV`
    ///    node): every tree is committed under a combined hash, so such a row
    ///    can only be a forgery that grinds the 63-byte `value_hash` /
    ///    `combine_hash` ambiguity. (3.1.0's non-batch insert of an empty
    ///    `CountSumTree` is the one exception, so strict refuses that element.)
    /// 3. On the query's `path` (a layer above `query.path`, where the merk
    ///    query is the single next path segment), the element must be a tree:
    ///    - a non-tree element (`Item`, `SumItem`, `Reference`) is refused. It
    ///      would cut the descent short and, at the honest root, turn into a
    ///      forged absence (for example a 63-byte item whose `value_hash`
    ///      equals a subtree's combined value hash);
    ///    - a tree with a root key must have a lower layer in the proof, or the
    ///      subtree's results silently vanish;
    ///    - an empty tree must be bound to its committed value hash,
    ///      `combine_hash(value_hash(bytes), NULL_HASH)`; otherwise a prover
    ///      could present a non-empty subtree as an empty one.
    ///
    /// Subquery positions (below `query.path`) are not covered by rule 3:
    /// there, 3.1.0's honest prover returns non-tree elements as results. The
    /// empty-tree binding holds at every position (it runs on every
    /// `KVValueHash` node, see `check_supplied_value_hash_strict`). A tree
    /// element with a root key returned as a result row, with no lower layer,
    /// stays unbound at any position: 3.1.0's proof format doesn't carry the
    /// subtree root its value hash combines.
    fn check_proved_element_strict(
        query: &PathQuery,
        current_path: &[&[u8]],
        key: &[u8],
        value_hash_in_proof: &CryptoHash,
        value_bytes: &[u8],
        element: &Element,
        layer_proof: &LayerProof,
    ) -> Result<(), Error> {
        if let Element::Reference(..) = element {
            return Err(Error::InvalidProof(
                query.clone(),
                format!(
                    "Proof presents an unresolved reference element at key {}",
                    hex::encode(key)
                ),
            ));
        }
        if element.is_any_tree() && value_hash_in_proof == value_hash(value_bytes).value() {
            return Err(Error::InvalidProof(
                query.clone(),
                format!(
                    "Proof presents a tree element at key {} under the plain hash of its bytes",
                    hex::encode(key)
                ),
            ));
        }
        let depth = current_path.len();
        if depth >= query.path.len() {
            return Ok(());
        }
        match element {
            Element::Tree(Some(_), _)
            | Element::SumTree(Some(_), ..)
            | Element::BigSumTree(Some(_), ..)
            | Element::CountTree(Some(_), ..)
            | Element::CountSumTree(Some(_), ..) => {
                if !layer_proof.lower_layers.contains_key(key) {
                    return Err(Error::InvalidProof(
                        query.clone(),
                        format!(
                            "Proof has no lower layer for path segment {} ({}) of the query path",
                            depth,
                            hex::encode(key)
                        ),
                    ));
                }
            }
            Element::Tree(None, _)
            | Element::SumTree(None, ..)
            | Element::BigSumTree(None, ..)
            | Element::CountTree(None, ..)
            | Element::CountSumTree(None, ..) => {
                let empty_tree_value_hash =
                    combine_hash(value_hash(value_bytes).value(), &NULL_HASH).unwrap();
                if value_hash_in_proof != &empty_tree_value_hash {
                    return Err(Error::InvalidProof(
                        query.clone(),
                        format!(
                            "Empty tree at path segment {} ({}) of the query path is not bound to \
                             its value hash",
                            depth,
                            hex::encode(key)
                        ),
                    ));
                }
            }
            Element::Item(..) | Element::SumItem(..) | Element::Reference(..) => {
                return Err(Error::InvalidProof(
                    query.clone(),
                    format!(
                        "Proof presents a non-tree element at path segment {} ({}) of the query \
                         path",
                        depth,
                        hex::encode(key)
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Verifies `proof` for `query` against the root hash it returns.
    ///
    /// Runs under [`ProofRules::Strict`], as do all the `verify_*` entry
    /// points without `_v310` in their name. Beyond what grovedb 3.1.0
    /// checks, strict verification:
    /// - decodes the large-value opcodes (values of 64 KiB or more);
    /// - refuses a child under a `Hash` node (its hash excludes children);
    /// - refuses a `KVValueHash` node carrying an `Item`/`SumItem` whose bytes
    ///   do not hash to the node's value hash (the KV→KVValueHash forgery), an
    ///   empty tree not bound to its value hash, or a value that isn't an
    ///   element, wherever the node is;
    /// - refuses a tree element proved under the plain hash of its bytes;
    /// - refuses an unresolved `Reference` element among the proved elements;
    /// - on `query.path`, refuses a non-tree element, a non-empty tree with no
    ///   lower layer, and an empty tree not bound to its value hash;
    /// - below `query.path`, refuses a tree with a root key that a subquery
    ///   descends but that has no lower layer. This refuses some honest limited
    ///   subquery proofs from 3.1.0's prover, whose limit accounting differs
    ///   from the verifier's (it stops early), and every subquery into a
    ///   non-empty `CountSumTree` (its prover never descends one);
    /// - decodes the envelope and each element with a claim bound of about 32
    ///   times its length (capped at 256 MiB and 64 MiB; where 3.1.0,
    ///   unbounded, aborts the process on a lying length), refuses an envelope
    ///   over 256 MiB or nested more than [`MAX_STRICT_PROOF_DEPTH`] deep, and
    ///   refuses trailing bytes after the envelope.
    ///
    /// Not bound, by either rule set: the bytes of a tree element with a root
    /// key returned as a result with no lower layer (3.1.0's proof format
    /// doesn't carry the subtree root its value hash combines).
    ///
    /// [`GroveDb::verify_query_v310`] reproduces 3.1.0 exactly.
    pub fn verify_query(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        Self::verify_query_with_rules(proof, query, ProofRules::Strict, grove_version)
    }

    /// [`GroveDb::verify_query`] exactly as grovedb 3.1.0 ran it: the
    /// large-value opcodes are unknown opcodes, `Hash` nodes may take
    /// children, and none of the strict element checks run. For replaying
    /// verdicts reached with 3.1.0; anything else should call
    /// [`GroveDb::verify_query`].
    ///
    /// It differs from 3.1.0 only where 3.1.0 can abort the process: an
    /// envelope nested more than [`MAX_V310_PROOF_DEPTH`] deep, and a length
    /// claim no input could satisfy (see [`decode_v310`]), are errors here.
    pub fn verify_query_v310(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        Self::verify_query_with_rules(proof, query, ProofRules::V310, grove_version)
    }

    /// [`GroveDb::verify_query`] under the given rules.
    pub fn verify_query_with_rules(
        proof: &[u8],
        query: &PathQuery,
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_query",
            grove_version.grovedb_versions.operations.proof.verify_query
        );
        Self::verify_query_with_options_and_rules(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: false,
                verify_proof_succinctness: true,
                include_empty_trees_in_result: false,
            },
            rules,
            grove_version,
        )
    }

    pub fn verify_subset_query(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_subset_query",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_subset_query
        );
        Self::verify_query_with_options(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: false,
                verify_proof_succinctness: false,
                include_empty_trees_in_result: false,
            },
            grove_version,
        )
    }

    /// The point of this query is to get the parent tree information which will
    /// be present because we are querying in a subtree
    pub fn verify_query_get_parent_tree_info(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, TreeFeatureType, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_query_get_parent_tree_info",
            grove_version.grovedb_versions.operations.proof.verify_query
        );
        Self::verify_query_get_parent_tree_info_with_options(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: false,
                verify_proof_succinctness: true,
                include_empty_trees_in_result: false,
            },
            grove_version,
        )
    }

    /// The point of this query is to get the parent tree information which will
    /// be present because we are querying in a subtree
    pub fn verify_subset_query_get_parent_tree_info(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, TreeFeatureType, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_subset_query_get_parent_tree_info",
            grove_version.grovedb_versions.operations.proof.verify_query
        );
        Self::verify_query_get_parent_tree_info_with_options(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: false,
                verify_proof_succinctness: false,
                include_empty_trees_in_result: false,
            },
            grove_version,
        )
    }

    pub fn verify_query_with_absence_proof(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_query_with_absence_proof",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_query_with_absence_proof
        );
        Self::verify_query_with_options(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: true,
                verify_proof_succinctness: true,
                include_empty_trees_in_result: false,
            },
            grove_version,
        )
    }

    pub fn verify_subset_query_with_absence_proof(
        proof: &[u8],
        query: &PathQuery,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<PathKeyOptionalElementTrio>), Error> {
        check_grovedb_v0!(
            "verify_subset_query_with_absence_proof",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_subset_query_with_absence_proof
        );
        Self::verify_query_with_options(
            proof,
            query,
            VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: true,
                verify_proof_succinctness: false,
                include_empty_trees_in_result: false,
            },
            grove_version,
        )
    }

    /// Verify subset proof with a chain of path query functions.
    /// After subset verification with the first path query, the result if
    /// passed to the next path query generation function which generates a
    /// new path query Apply the new path query, and pass the result to the
    /// next ... This is useful for verifying proofs with multiple path
    /// queries that depend on one another.
    pub fn verify_query_with_chained_path_queries<C>(
        proof: &[u8],
        first_query: &PathQuery,
        chained_path_queries: Vec<C>,
        grove_version: &GroveVersion,
    ) -> Result<(CryptoHash, Vec<Vec<PathKeyOptionalElementTrio>>), Error>
    where
        C: Fn(Vec<PathKeyOptionalElementTrio>) -> Option<PathQuery>,
    {
        check_grovedb_v0!(
            "verify_query_with_chained_path_queries",
            grove_version
                .grovedb_versions
                .operations
                .proof
                .verify_query_with_chained_path_queries
        );
        let mut results = vec![];

        let (last_root_hash, elements) =
            Self::verify_subset_query(proof, first_query, grove_version)?;
        results.push(elements);

        // Process the chained path queries
        Self::process_chained_path_queries(
            proof,
            last_root_hash,
            chained_path_queries,
            grove_version,
            &mut results,
        )?;

        Ok((last_root_hash, results))
    }

    /// Processes each chained path query and verifies it.
    pub(in crate::operations::proof) fn process_chained_path_queries<C>(
        proof: &[u8],
        last_root_hash: CryptoHash,
        chained_path_queries: Vec<C>,
        grove_version: &GroveVersion,
        results: &mut Vec<Vec<PathKeyOptionalElementTrio>>,
    ) -> Result<(), Error>
    where
        C: Fn(Vec<PathKeyOptionalElementTrio>) -> Option<PathQuery>,
    {
        for path_query_generator in chained_path_queries {
            let new_path_query = path_query_generator(results[results.len() - 1].clone()).ok_or(
                Error::InvalidInput("one of the path query generators returns no path query"),
            )?;

            let (new_root_hash, new_elements) =
                Self::verify_subset_query(proof, &new_path_query, grove_version)?;

            if new_root_hash != last_root_hash {
                return Err(Error::InvalidProof(
                    new_path_query,
                    format!(
                        "Root hash for different path queries do not match, first is {}, this one \
                         is {}",
                        hex::encode(last_root_hash),
                        hex::encode(new_root_hash)
                    ),
                ));
            }

            results.push(new_elements);
        }

        Ok(())
    }
}
