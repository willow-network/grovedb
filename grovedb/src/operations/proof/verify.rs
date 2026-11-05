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
        util::{ProvedPathKeyOptionalValue, ProvedPathKeyValues},
        GroveDBProof, GroveDBProofV0, LayerProof, ProveOptions,
    },
    query_result_type::PathKeyOptionalElementTrio,
    Element, Error, GroveDb, PathQuery,
};

/// Under [`ProofRules::Strict`], at most this many bytes may be claimed while
/// decoding a proof envelope (upstream GroveDB's bound). grovedb 3.1.0 decodes
/// with no limit: bincode allocates a byte string at its claimed length before
/// reading it, so a few bytes claiming an enormous length abort the process.
const STRICT_PROOF_DECODE_LIMIT: usize = 256 * 1024 * 1024;

/// Under [`ProofRules::Strict`], the bound for decoding one proved element
/// (the merk decoder's own value cap).
const STRICT_ELEMENT_DECODE_LIMIT: usize = grovedb_merk::proofs::encoding::MAX_VALUE_LEN as usize;

impl GroveDb {
    /// Decodes a proof envelope. [`ProofRules::V310`] is 3.1.0's decode (no
    /// size limit, trailing bytes ignored). [`ProofRules::Strict`] bounds what
    /// the envelope may claim by [`STRICT_PROOF_DECODE_LIMIT`] and refuses
    /// trailing bytes.
    fn decode_proof_with_rules(proof: &[u8], rules: ProofRules) -> Result<GroveDBProof, Error> {
        let decode_error = |e| Error::CorruptedData(format!("unable to decode proof: {}", e));
        match rules {
            ProofRules::V310 => {
                let config = bincode::config::standard()
                    .with_big_endian()
                    .with_no_limit();
                Ok(bincode::decode_from_slice(proof, config)
                    .map_err(decode_error)?
                    .0)
            }
            ProofRules::Strict => {
                let config = bincode::config::standard()
                    .with_big_endian()
                    .with_limit::<STRICT_PROOF_DECODE_LIMIT>();
                let (grovedb_proof, used) =
                    bincode::decode_from_slice(proof, config).map_err(decode_error)?;
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

    /// Decodes a proved element. [`ProofRules::V310`] is
    /// [`Element::deserialize`]; [`ProofRules::Strict`] is the same decode
    /// bounded by [`STRICT_ELEMENT_DECODE_LIMIT`], so a node value that claims
    /// an enormous length is refused instead of aborting the process.
    fn deserialize_element(
        bytes: &[u8],
        rules: ProofRules,
        grove_version: &GroveVersion,
    ) -> Result<Element, Error> {
        match rules {
            ProofRules::V310 => Element::deserialize(bytes, grove_version),
            ProofRules::Strict => {
                check_grovedb_v0!(
                    "Element::deserialize",
                    grove_version.grovedb_versions.element.deserialize
                );
                let config = bincode::config::standard()
                    .with_big_endian()
                    .with_limit::<STRICT_ELEMENT_DECODE_LIMIT>();
                Ok(bincode::decode_from_slice(bytes, config)
                    .map_err(|e| {
                        Error::CorruptedData(format!("unable to deserialize element {}", e))
                    })?
                    .0)
            }
        }
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
    fn check_supplied_value_hash_strict(
        value: &[u8],
        supplied_value_hash: &CryptoHash,
        grove_version: &GroveVersion,
    ) -> Result<(), grovedb_merk::error::Error> {
        match Self::deserialize_element(value, ProofRules::Strict, grove_version) {
            Ok(Element::Item(..)) | Ok(Element::SumItem(..))
                if value_hash(value).value() != supplied_value_hash =>
            {
                Err(grovedb_merk::error::Error::InvalidProofError(
                    "KVValueHash node carries an item element whose bytes do not hash to its \
                     value hash"
                        .to_string(),
                ))
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
    /// 2. On the query's `path` (a layer above `query.path`, where the merk
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
    /// Subquery positions (below `query.path`) are not covered by rule 2:
    /// there, 3.1.0's honest prover returns non-tree elements as results.
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
    ///   do not hash to the node's value hash (the KV→KVValueHash forgery);
    /// - refuses an unresolved `Reference` element among the proved elements;
    /// - on `query.path`, refuses a non-tree element, a non-empty tree with no
    ///   lower layer, and an empty tree not bound to its value hash;
    /// - decodes the envelope and each proved element with a size bound (where
    ///   3.1.0, unbounded, aborts the process on a lying length) and refuses
    ///   trailing bytes after the envelope.
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
