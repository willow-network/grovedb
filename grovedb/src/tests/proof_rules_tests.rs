//! Strict vs 3.1.0 proof verification (`ProofRules`).
//!
//! Each forgery below is accepted by grovedb 3.1.0's verifier at the honest
//! root hash (asserted through the `_v310` entry points, which reproduce
//! 3.1.0) and refused by the default, strict entry points. The honest-proof
//! tests assert that strict verification accepts every shape 3.1.0's prover
//! emits, with the same results.

use grovedb_merk::{
    proofs::{encode_into, Decoder, Node, Op},
    tree::{combine_hash, kv_hash, node_hash, value_hash, NULL_HASH},
};
use grovedb_version::version::GroveVersion;

use crate::{
    operations::proof::{GroveDBProof, GroveDBProofV0, LayerProof},
    query_result_type::PathKeyOptionalElementTrio,
    reference_path::ReferencePathType,
    tests::{common::EMPTY_PATH, make_deep_tree, make_test_grovedb, TempGroveDb, TEST_LEAF},
    Element, Error, GroveDb, PathQuery, Query, SizedQuery,
};

fn config() -> impl bincode::config::Config {
    bincode::config::standard()
        .with_big_endian()
        .with_no_limit()
}

fn decode_proof(bytes: &[u8]) -> GroveDBProofV0 {
    let (GroveDBProof::V0(v0), _) = bincode::decode_from_slice(bytes, config()).unwrap();
    v0
}

fn encode_proof(v0: GroveDBProofV0) -> Vec<u8> {
    bincode::encode_to_vec(GroveDBProof::V0(v0), config()).unwrap()
}

fn ops(merk_proof: &[u8]) -> Vec<Op> {
    Decoder::new(merk_proof).map(|op| op.unwrap()).collect()
}

fn encode_ops(ops: &[Op]) -> Vec<u8> {
    let mut out = vec![];
    encode_into(ops.iter(), &mut out);
    out
}

fn layer<'a>(root: &'a mut LayerProof, path: &[&[u8]]) -> &'a mut LayerProof {
    let mut l = root;
    for seg in path {
        l = l.lower_layers.get_mut(*seg).expect("layer on path");
    }
    l
}

/// Replaces the pushed node for `key` in the merk proof of the layer at
/// `path`, re-encoding the layer.
fn replace_node(proof: &[u8], path: &[&[u8]], key: &[u8], f: impl Fn(&Node) -> Node) -> Vec<u8> {
    let mut v0 = decode_proof(proof);
    let l = layer(&mut v0.root_layer, path);
    let mut found = false;
    let new_ops: Vec<Op> = ops(&l.merk_proof)
        .into_iter()
        .map(|op| match op {
            Op::Push(ref node) | Op::PushInverted(ref node) if node_key(node) == Some(key) => {
                found = true;
                match op {
                    Op::Push(n) => Op::Push(f(&n)),
                    Op::PushInverted(n) => Op::PushInverted(f(&n)),
                    _ => unreachable!(),
                }
            }
            other => other,
        })
        .collect();
    assert!(found, "no pushed node for the key");
    l.merk_proof = encode_ops(&new_ops);
    encode_proof(v0)
}

fn node_key(node: &Node) -> Option<&[u8]> {
    match node {
        Node::KV(k, _)
        | Node::KVValueHash(k, ..)
        | Node::KVDigest(k, _)
        | Node::KVRefValueHash(k, ..)
        | Node::KVValueHashFeatureType(k, ..) => Some(k.as_slice()),
        _ => None,
    }
}

fn root_hash(db: &TempGroveDb, v: &GroveVersion) -> [u8; 32] {
    db.root_hash(None, v).unwrap().unwrap()
}

fn item_values(results: &[PathKeyOptionalElementTrio]) -> Vec<Option<Element>> {
    results.iter().map(|(_, _, e)| e.clone()).collect()
}

fn assert_strict_refuses(proof: &[u8], pq: &PathQuery, v: &GroveVersion, needle: &str) {
    let strict = GroveDb::verify_query(proof, pq, v);
    match strict {
        Err(Error::InvalidProof(_, msg)) => assert!(msg.contains(needle), "{msg}"),
        other => panic!("strict verify_query should refuse ({needle}), got {other:?}"),
    }
    let strict_raw = GroveDb::verify_query_raw(proof, pq, v);
    assert!(strict_raw.is_err(), "strict verify_query_raw should refuse");
}

/// Strict and 3.1.0 rules agree on an honest proof.
fn assert_honest(
    db: &TempGroveDb,
    pq: &PathQuery,
    v: &GroveVersion,
) -> Vec<PathKeyOptionalElementTrio> {
    let proof = db.prove_query(pq, None, v).unwrap().unwrap();
    let (strict_root, strict) = GroveDb::verify_query(&proof, pq, v).expect("strict verifies");
    let (legacy_root, legacy) = GroveDb::verify_query_v310(&proof, pq, v).expect("3.1.0 verifies");
    assert_eq!(strict_root, root_hash(db, v));
    assert_eq!(strict_root, legacy_root);
    assert_eq!(strict, legacy);
    let (r1, raw_strict) = GroveDb::verify_query_raw(&proof, pq, v).expect("strict raw");
    let (r2, raw_legacy) = GroveDb::verify_query_raw_v310(&proof, pq, v).expect("3.1.0 raw");
    assert_eq!(r1, r2);
    assert_eq!(raw_strict, raw_legacy);
    strict
}

// -------------------------------------------------------------------------
// KV -> KVValueHash (upstream da308f7f / dd99ed1d / 319dea5e)
// -------------------------------------------------------------------------

#[test]
fn kv_to_kv_value_hash_forgery_is_refused() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    let real = Element::new_item(b"real_secret_value".to_vec());
    db.insert([TEST_LEAF].as_ref(), b"mykey", real.clone(), None, None, v)
        .unwrap()
        .unwrap();
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"mykey".to_vec()),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let real_bytes = real.serialize(v).unwrap();
    let fake = Element::new_item(b"attacker_controlled".to_vec());
    let fake_bytes = fake.serialize(v).unwrap();
    let forged = replace_node(&proof, &[TEST_LEAF], b"mykey", |n| match n {
        Node::KV(k, value) => {
            assert_eq!(value, &real_bytes);
            Node::KVValueHash(
                k.clone(),
                fake_bytes.clone(),
                value_hash(&real_bytes).unwrap(),
            )
        }
        other => panic!("expected KV, got {other:?}"),
    });

    let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(root, root_hash(&db, v));
    assert_eq!(item_values(&results), vec![Some(fake)]);
    assert_strict_refuses(&forged, &pq, v, "KVValueHash node carries an item element");
}

#[test]
fn sum_item_in_kv_value_hash_is_honest_but_a_forged_sum_is_refused() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    db.insert(
        [TEST_LEAF].as_ref(),
        b"sums",
        Element::empty_sum_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    for (k, n) in [(b"a", 5i64), (b"b", 7), (b"c", -3)] {
        db.insert(
            [TEST_LEAF, b"sums"].as_ref(),
            k,
            Element::new_sum_item(n),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"sums".to_vec()],
        Query::new_single_key(b"b".to_vec()),
    );
    // 3.1.0's prover sends a SumItem as KVValueHash; strict accepts it.
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let l = decode_proof(&proof);
    let sums_layer = &l.root_layer.lower_layers[TEST_LEAF].lower_layers[b"sums".as_slice()];
    assert!(ops(&sums_layer.merk_proof)
        .iter()
        .any(|op| matches!(op, Op::Push(Node::KVValueHash(k, ..)) if k == b"b")));
    let results = assert_honest(&db, &pq, v);
    assert_eq!(item_values(&results), vec![Some(Element::new_sum_item(7))]);

    let real_bytes = Element::new_sum_item(7).serialize(v).unwrap();
    let fake_bytes = Element::new_sum_item(7_000_000).serialize(v).unwrap();
    let forged = replace_node(&proof, &[TEST_LEAF, b"sums"], b"b", |n| match n {
        Node::KVValueHash(k, _, vh) => {
            assert_eq!(vh, &value_hash(&real_bytes).unwrap());
            Node::KVValueHash(k.clone(), fake_bytes.clone(), *vh)
        }
        other => panic!("expected KVValueHash, got {other:?}"),
    });
    let (_, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(
        item_values(&results),
        vec![Some(Element::new_sum_item(7_000_000))]
    );
    assert_strict_refuses(&forged, &pq, v, "KVValueHash node carries an item element");
}

#[test]
fn kv_to_kv_ref_value_hash_is_refused_by_both_rule_sets() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    let real = Element::new_item(b"real_secret_value".to_vec());
    db.insert([TEST_LEAF].as_ref(), b"mykey", real.clone(), None, None, v)
        .unwrap()
        .unwrap();
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"mykey".to_vec()),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let real_bytes = real.serialize(v).unwrap();
    let fake_bytes = Element::new_item(b"attacker_controlled".to_vec())
        .serialize(v)
        .unwrap();
    let forged = replace_node(&proof, &[TEST_LEAF], b"mykey", |n| match n {
        Node::KV(k, _) => Node::KVRefValueHash(
            k.clone(),
            fake_bytes.clone(),
            value_hash(&real_bytes).unwrap(),
        ),
        other => panic!("expected KV, got {other:?}"),
    });
    // KVRefValueHash hashes H(value) into the node, so the root moves.
    let legacy = GroveDb::verify_query_v310(&forged, &pq, v);
    assert!(legacy.is_err() || legacy.unwrap().0 != root_hash(&db, v));
    let strict = GroveDb::verify_query(&forged, &pq, v);
    assert!(strict.is_err() || strict.unwrap().0 != root_hash(&db, v));
}

// -------------------------------------------------------------------------
// Children under a Hash node (upstream d998d764)
// -------------------------------------------------------------------------

#[test]
fn forged_row_under_hash_node_is_refused() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    for k in [b"k3", b"k5", b"k7"] {
        db.insert(
            [TEST_LEAF].as_ref(),
            k,
            Element::new_item(k.to_vec()),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"k3".to_vec()),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    // k3 is a leaf of TEST_LEAF's AVL tree: swap its KV for the opaque Hash
    // of that leaf and hang a forged KV(k3) beneath the Hash.
    let honest_bytes = Element::new_item(b"k3".to_vec()).serialize(v).unwrap();
    let leaf_hash = node_hash(
        &kv_hash(b"k3", &honest_bytes).unwrap(),
        &NULL_HASH,
        &NULL_HASH,
    )
    .unwrap();
    let fake = Element::new_item(b"forged".to_vec());
    let fake_bytes = fake.serialize(v).unwrap();
    let mut v0 = decode_proof(&proof);
    let l = layer(&mut v0.root_layer, &[TEST_LEAF]);
    let mut new_ops = vec![];
    for op in ops(&l.merk_proof) {
        match op {
            Op::Push(Node::KV(ref k, _)) if k == b"k3" => {
                new_ops.push(Op::Push(Node::Hash(leaf_hash)));
                new_ops.push(Op::Push(Node::KV(b"k3".to_vec(), fake_bytes.clone())));
                new_ops.push(Op::Child);
            }
            other => new_ops.push(other),
        }
    }
    l.merk_proof = encode_ops(&new_ops);
    let forged = encode_proof(v0);

    let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(root, root_hash(&db, v));
    assert_eq!(item_values(&results), vec![Some(fake)]);
    assert_strict_refuses(&forged, &pq, v, "opaque proof node");
}

// -------------------------------------------------------------------------
// Non-tree element / missing lower layer on the query path
// -------------------------------------------------------------------------

fn db_with_subtree(v: &GroveVersion) -> TempGroveDb {
    let db = make_test_grovedb(v);
    db.insert(
        [TEST_LEAF].as_ref(),
        b"sub",
        Element::empty_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF, b"sub"].as_ref(),
        b"x",
        Element::new_item(b"present".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF].as_ref(),
        b"empty",
        Element::empty_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF].as_ref(),
        b"item",
        Element::new_item(b"i".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db
}

fn sub_query() -> PathQuery {
    PathQuery::new(
        vec![TEST_LEAF.to_vec(), b"sub".to_vec()],
        SizedQuery::new(Query::new_single_key(b"x".to_vec()), Some(1), None),
    )
}

#[test]
fn dropped_or_renamed_lower_layer_on_the_path_is_refused() {
    let v = GroveVersion::latest();
    let db = db_with_subtree(v);
    let pq = sub_query();
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    for rename in [false, true] {
        let mut v0 = decode_proof(&proof);
        let l = layer(&mut v0.root_layer, &[TEST_LEAF]);
        let sub = l.lower_layers.remove(b"sub".as_slice()).unwrap();
        if rename {
            l.lower_layers.insert(b"XXX".to_vec(), sub);
        }
        let forged = encode_proof(v0);
        let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
        assert_eq!(root, root_hash(&db, v));
        assert!(results.is_empty(), "3.1.0 proves x absent");
        let (_, absent) = GroveDb::verify_query_with_options_and_rules(
            &forged,
            &pq,
            grovedb_merk::proofs::query::VerifyOptions {
                absence_proofs_for_non_existing_searched_keys: true,
                verify_proof_succinctness: true,
                include_empty_trees_in_result: false,
            },
            crate::ProofRules::V310,
            v,
        )
        .expect("3.1.0 absence proof accepts");
        assert_eq!(item_values(&absent), vec![None]);
        assert_strict_refuses(&forged, &pq, v, "no lower layer for path segment 1");
    }
}

#[test]
fn non_empty_subtree_presented_as_empty_tree_is_refused() {
    let v = GroveVersion::latest();
    let db = db_with_subtree(v);
    let pq = sub_query();
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let empty_bytes = Element::empty_tree().serialize(v).unwrap();
    let mut forged = replace_node(&proof, &[TEST_LEAF], b"sub", |n| match n {
        Node::KVValueHash(k, _, vh) => Node::KVValueHash(k.clone(), empty_bytes.clone(), *vh),
        other => panic!("expected KVValueHash, got {other:?}"),
    });
    let mut v0 = decode_proof(&forged);
    layer(&mut v0.root_layer, &[TEST_LEAF])
        .lower_layers
        .remove(b"sub".as_slice())
        .unwrap();
    forged = encode_proof(v0);
    let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(root, root_hash(&db, v));
    assert!(results.is_empty());
    assert_strict_refuses(&forged, &pq, v, "not bound to its value hash");
}

#[test]
fn item_standing_in_for_a_subtree_on_the_path_is_refused() {
    let v = GroveVersion::latest();
    let db = db_with_subtree(v);
    let pq = sub_query();
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let fake = Element::new_item(b"not a tree".to_vec());
    let fake_bytes = fake.serialize(v).unwrap();
    let mut forged = replace_node(&proof, &[TEST_LEAF], b"sub", |n| match n {
        Node::KVValueHash(k, _, vh) => Node::KVValueHash(k.clone(), fake_bytes.clone(), *vh),
        other => panic!("expected KVValueHash, got {other:?}"),
    });
    let mut v0 = decode_proof(&forged);
    layer(&mut v0.root_layer, &[TEST_LEAF])
        .lower_layers
        .remove(b"sub".as_slice())
        .unwrap();
    forged = encode_proof(v0);
    let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(root, root_hash(&db, v));
    // 3.1.0 returns the item as a row one level up and never reaches x.
    assert_eq!(
        results,
        vec![(vec![TEST_LEAF.to_vec()], b"sub".to_vec(), Some(fake))]
    );
    assert!(GroveDb::verify_query(&forged, &pq, v).is_err());
    assert!(GroveDb::verify_query_raw(&forged, &pq, v).is_err());
}

#[test]
fn honest_path_through_an_item_is_refused_strictly() {
    // The path itself runs through an item: 3.1.0 returns the item as a row
    // under the parent path. Strict refuses: an item is not a subtree.
    let v = GroveVersion::latest();
    let db = db_with_subtree(v);
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"item".to_vec()],
        Query::new_single_key(b"x".to_vec()),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let (_, legacy) = GroveDb::verify_query_v310(&proof, &pq, v).expect("3.1.0 accepts");
    assert_eq!(
        legacy,
        vec![(
            vec![TEST_LEAF.to_vec()],
            b"item".to_vec(),
            Some(Element::new_item(b"i".to_vec()))
        )]
    );
    assert_strict_refuses(&proof, &pq, v, "non-tree element at path segment 1");
}

#[test]
fn honest_paths_through_empty_and_missing_subtrees_verify_strictly() {
    let v = GroveVersion::latest();
    let db = db_with_subtree(v);
    for seg in [b"empty".as_slice(), b"missing".as_slice()] {
        let pq = PathQuery::new_unsized(
            vec![TEST_LEAF.to_vec(), seg.to_vec()],
            Query::new_single_key(b"x".to_vec()),
        );
        assert!(assert_honest(&db, &pq, v).is_empty());
    }
    // and an empty tree of each aggregate kind on the path
    for (k, e) in [
        (b"es".as_slice(), Element::empty_sum_tree()),
        (b"eb".as_slice(), Element::empty_big_sum_tree()),
        (b"ec".as_slice(), Element::empty_count_tree()),
    ] {
        db.insert([TEST_LEAF].as_ref(), k, e, None, None, v)
            .unwrap()
            .unwrap();
        let pq = PathQuery::new_unsized(
            vec![TEST_LEAF.to_vec(), k.to_vec()],
            Query::new_single_key(b"x".to_vec()),
        );
        assert!(assert_honest(&db, &pq, v).is_empty());
    }
}

// -------------------------------------------------------------------------
// Unresolved reference presented through KVValueHash
// -------------------------------------------------------------------------

#[test]
fn unresolved_reference_forgery_is_refused() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    let target = Element::new_item(b"target value".to_vec());
    db.insert(
        [TEST_LEAF].as_ref(),
        b"target",
        target.clone(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let reference = Element::new_reference(ReferencePathType::AbsolutePathReference(vec![
        TEST_LEAF.to_vec(),
        b"target".to_vec(),
    ]));
    db.insert(
        [TEST_LEAF].as_ref(),
        b"ref",
        reference.clone(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"ref".to_vec()),
    );
    let results = assert_honest(&db, &pq, v);
    assert_eq!(item_values(&results), vec![Some(target.clone())]);

    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let fake_ref = Element::new_reference(ReferencePathType::AbsolutePathReference(vec![
        b"elsewhere".to_vec(),
    ]));
    let fake_ref_bytes = fake_ref.serialize(v).unwrap();
    let forged = replace_node(&proof, &[TEST_LEAF], b"ref", |n| match n {
        Node::KVRefValueHash(k, referenced, node_value_hash) => {
            let committed =
                combine_hash(node_value_hash, &value_hash(referenced).unwrap()).unwrap();
            Node::KVValueHash(k.clone(), fake_ref_bytes.clone(), committed)
        }
        other => panic!("expected KVRefValueHash, got {other:?}"),
    });
    let (root, results) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!(root, root_hash(&db, v));
    assert_eq!(item_values(&results), vec![Some(fake_ref)]);
    assert_strict_refuses(&forged, &pq, v, "unresolved reference");
}

// -------------------------------------------------------------------------
// Large values (upstream 86562f65)
// -------------------------------------------------------------------------

#[test]
fn large_values_verify_strictly() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    // Item(value, None) serializes as [0, varint len, value, 0]: a 65,530-byte
    // value is a 65,535-byte merk value (the largest 3.1.0 encodes), a
    // 65,531-byte value is the first that needs a large-value opcode.
    let sizes = [65_530usize, 65_531, 512 * 1024, 1 << 20];
    for (i, len) in sizes.iter().enumerate() {
        let value: Vec<u8> = (0..*len).map(|j| ((j * 31 + i) % 256) as u8).collect();
        db.insert(
            [TEST_LEAF].as_ref(),
            format!("big{i}").as_bytes(),
            Element::new_item(value),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    db.insert(
        [TEST_LEAF].as_ref(),
        b"small",
        Element::new_item(b"s".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();

    for (i, len) in sizes.iter().enumerate() {
        let key = format!("big{i}").into_bytes();
        let pq = PathQuery::new_unsized(vec![TEST_LEAF.to_vec()], Query::new_single_key(key));
        let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
        let (root, results) = GroveDb::verify_query(&proof, &pq, v).expect("strict verifies");
        assert_eq!(root, root_hash(&db, v));
        match &results[0].2 {
            Some(Element::Item(bytes, _)) => assert_eq!(bytes.len(), *len),
            other => panic!("{other:?}"),
        }
        let (_, raw) = GroveDb::verify_query_raw(&proof, &pq, v).expect("strict raw");
        assert_eq!(raw.len(), 1);
        let legacy = GroveDb::verify_query_v310(&proof, &pq, v);
        let element_len = results[0].2.as_ref().unwrap().serialize(v).unwrap().len();
        if element_len < 65_536 {
            assert_eq!(legacy.expect("small").1, results);
        } else {
            assert!(legacy.is_err(), "3.1.0 cannot decode a large-value op");
            assert!(GroveDb::verify_query_raw_v310(&proof, &pq, v).is_err());
        }
    }

    // A range over all of them, with a limit, and through a subquery.
    let mut all = Query::new_range_full();
    all.left_to_right = true;
    let pq = PathQuery::new(
        vec![TEST_LEAF.to_vec()],
        SizedQuery::new(all, Some(3), None),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let (_, results) = GroveDb::verify_query(&proof, &pq, v).expect("strict range");
    assert_eq!(results.len(), 3);

    let mut top = Query::new_single_key(TEST_LEAF.to_vec());
    top.set_subquery(Query::new_range_full());
    let pq = PathQuery::new_unsized(vec![], top);
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let (_, results) = GroveDb::verify_query(&proof, &pq, v).expect("strict subquery");
    assert_eq!(results.len(), sizes.len() + 1);
}

// -------------------------------------------------------------------------
// Honest proofs: strict == 3.1.0
// -------------------------------------------------------------------------

#[test]
fn honest_proofs_verify_identically_under_both_rule_sets() {
    let v = GroveVersion::latest();
    let db = make_deep_tree(v);
    // references and sum trees alongside the deep tree
    db.insert(
        EMPTY_PATH,
        b"sum_leaf",
        Element::empty_sum_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    for (k, n) in [(b"s1", 1i64), (b"s2", 2), (b"s3", 3)] {
        db.insert(
            [b"sum_leaf".as_slice()].as_ref(),
            k,
            Element::new_sum_item(n),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    db.insert(
        [b"sum_leaf".as_slice()].as_ref(),
        b"st",
        Element::empty_sum_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [b"sum_leaf".as_slice(), b"st"].as_ref(),
        b"z",
        Element::new_sum_item(9),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF].as_ref(),
        b"ref_to_deep",
        Element::new_reference(ReferencePathType::AbsolutePathReference(vec![
            b"deep_leaf".to_vec(),
            b"deep_node_1".to_vec(),
            b"deeper_1".to_vec(),
            b"key1".to_vec(),
        ])),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();

    let mut queries: Vec<PathQuery> = vec![];
    // single keys, present and absent, at several depths
    queries.push(PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"innertree".to_vec()),
    ));
    queries.push(PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"ref_to_deep".to_vec()),
    ));
    queries.push(PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"innertree".to_vec()],
        Query::new_single_key(b"key2".to_vec()),
    ));
    queries.push(PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"innertree".to_vec()],
        Query::new_single_key(b"nope".to_vec()),
    ));
    queries.push(PathQuery::new_unsized(
        vec![
            b"deep_leaf".to_vec(),
            b"deep_node_1".to_vec(),
            b"deeper_1".to_vec(),
        ],
        Query::new_range_full(),
    ));
    // range queries with limits, both directions
    for ltr in [true, false] {
        let mut q = Query::new_with_direction(ltr);
        q.insert_range(b"key1".to_vec()..b"key3".to_vec());
        queries.push(PathQuery::new(
            vec![TEST_LEAF.to_vec(), b"innertree".to_vec()],
            SizedQuery::new(q, Some(2), None),
        ));
    }
    // subqueries over the deep tree, with and without limits
    for limit in [None, Some(1), Some(3), Some(100)] {
        let mut q = Query::new_range_full();
        let mut sub = Query::new_range_full();
        sub.set_subquery(Query::new_range_full());
        q.set_subquery(sub);
        queries.push(PathQuery::new(
            vec![b"deep_leaf".to_vec()],
            SizedQuery::new(q, limit, None),
        ));
    }
    // subquery path
    let mut q = Query::new_range_full();
    q.set_subquery_key(b"deeper_1".to_vec());
    q.set_subquery(Query::new_range_full());
    queries.push(PathQuery::new_unsized(vec![b"deep_leaf".to_vec()], q));
    // sum tree items and a sum tree with and without its lower layer
    queries.push(PathQuery::new_unsized(
        vec![b"sum_leaf".to_vec()],
        Query::new_range_full(),
    ));
    let mut q = Query::new_single_key(b"st".to_vec());
    q.set_subquery(Query::new_range_full());
    queries.push(PathQuery::new_unsized(vec![b"sum_leaf".to_vec()], q));
    // trees as results (no lower layer) and the whole root
    queries.push(PathQuery::new_unsized(vec![], Query::new_range_full()));

    for pq in &queries {
        assert_honest(&db, pq, v);
    }

    // absence proofs (need a limit)
    let mut q = Query::new();
    q.insert_key(b"key1".to_vec());
    q.insert_key(b"zzz".to_vec());
    let pq = PathQuery::new(
        vec![TEST_LEAF.to_vec(), b"innertree".to_vec()],
        SizedQuery::new(q, Some(5), None),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let strict = GroveDb::verify_query_with_absence_proof(&proof, &pq, v).unwrap();
    let legacy = GroveDb::verify_query_with_options_and_rules(
        &proof,
        &pq,
        grovedb_merk::proofs::query::VerifyOptions {
            absence_proofs_for_non_existing_searched_keys: true,
            verify_proof_succinctness: true,
            include_empty_trees_in_result: false,
        },
        crate::ProofRules::V310,
        v,
    )
    .unwrap();
    assert_eq!(strict, legacy);
    assert_eq!(strict.1.len(), 2);
    assert!(strict.1[1].2.is_none());
}

/// 3.1.0's non-batch `insert` has no `CountSumTree` arm, so an empty
/// `CountSumTree` inserted that way is committed under `value_hash(bytes)`
/// rather than `combine_hash(value_hash(bytes), NULL_HASH)`. Strict
/// verification binds an empty tree on the query path only under the
/// combined hash, so this documents (and pins) what it does with one.
#[test]
fn empty_count_sum_tree_on_the_path() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    db.insert(
        [TEST_LEAF].as_ref(),
        b"ecs",
        Element::empty_count_sum_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"ecs".to_vec()],
        Query::new_single_key(b"x".to_vec()),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let v0 = decode_proof(&proof);
    let bytes = Element::empty_count_sum_tree().serialize(v).unwrap();
    let vh = ops(&v0.root_layer.lower_layers[TEST_LEAF].merk_proof)
        .into_iter()
        .find_map(|op| match op {
            Op::Push(Node::KVValueHash(k, _, vh)) if k == b"ecs" => Some(vh),
            _ => None,
        })
        .expect("ecs node");
    let combined = combine_hash(&value_hash(&bytes).unwrap(), &NULL_HASH).unwrap();
    let legacy = GroveDb::verify_query_v310(&proof, &pq, v).expect("3.1.0 verifies");
    assert!(legacy.1.is_empty());
    if vh == combined {
        println!("empty CountSumTree: combined value hash; strict accepts");
        assert_eq!(GroveDb::verify_query(&proof, &pq, v).unwrap(), legacy);
    } else {
        println!("empty CountSumTree: plain value hash; strict refuses");
        assert_eq!(vh, value_hash(&bytes).unwrap(), "plain value hash");
        assert_strict_refuses(&proof, &pq, v, "not bound to its value hash");
    }
}

// -------------------------------------------------------------------------
// Bounded decoding (strict only: 3.1.0 aborts the process on these)
// -------------------------------------------------------------------------

#[test]
fn lying_lengths_and_trailing_bytes_are_refused_strictly() {
    let v = GroveVersion::latest();
    let pq = PathQuery::new_unsized(vec![], Query::new_single_key(b"k".to_vec()));

    // V0, then a root merk proof claiming 2^63 bytes.
    let mut huge_envelope = vec![0x00, 0xFD];
    huge_envelope.extend_from_slice(&(1u64 << 63).to_be_bytes());
    for r in [
        GroveDb::verify_query(&huge_envelope, &pq, v).map(|_| ()),
        GroveDb::verify_query_raw(&huge_envelope, &pq, v).map(|_| ()),
    ] {
        assert!(
            matches!(r, Err(Error::CorruptedData(ref m)) if m.contains("unable to decode proof")),
            "{r:?}"
        );
    }

    // A one-node merk proof whose item claims 2^63 bytes.
    let mut item = vec![0x00, 0xFD];
    item.extend_from_slice(&(1u64 << 63).to_be_bytes());
    let merk = encode_ops(&[Op::Push(Node::KV(b"k".to_vec(), item))]);
    let proof = encode_proof(GroveDBProofV0 {
        root_layer: LayerProof {
            merk_proof: merk,
            lower_layers: Default::default(),
        },
        prove_options: Default::default(),
    });
    for r in [
        GroveDb::verify_query(&proof, &pq, v).map(|_| ()),
        GroveDb::verify_query_raw(&proof, &pq, v).map(|_| ()),
    ] {
        assert!(
            matches!(r, Err(Error::CorruptedData(ref m)) if m.contains("deserialize element")),
            "{r:?}"
        );
    }

    // An honest proof with a byte appended: 3.1.0 ignores it, strict refuses.
    let db = make_test_grovedb(v);
    db.insert(
        [TEST_LEAF].as_ref(),
        b"k",
        Element::new_item(b"v".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"k".to_vec()),
    );
    let mut proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    proof.push(0);
    assert!(GroveDb::verify_query_v310(&proof, &pq, v).is_ok());
    assert!(matches!(
        GroveDb::verify_query(&proof, &pq, v),
        Err(Error::CorruptedData(ref m)) if m.contains("trailing bytes")
    ));
}

// -------------------------------------------------------------------------
// An item presented as an empty tree, at result positions (review finding)
// -------------------------------------------------------------------------

fn as_empty_tree(proof: &[u8], path: &[&[u8]], key: &[u8], v: &GroveVersion) -> Vec<u8> {
    let empty = Element::empty_tree().serialize(v).unwrap();
    replace_node(proof, path, key, |n| match n {
        Node::KV(k, value) => {
            Node::KVValueHash(k.clone(), empty.clone(), value_hash(value).unwrap())
        }
        other => panic!("expected KV, got {other:?}"),
    })
}

#[test]
fn item_presented_as_an_empty_tree_is_refused_at_result_positions() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    for i in 0..10u8 {
        let k = format!("k{i:02}");
        db.insert(
            [TEST_LEAF].as_ref(),
            k.as_bytes(),
            Element::new_item(vec![i; 10]),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    db.insert(
        [TEST_LEAF].as_ref(),
        b"a",
        Element::empty_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF, b"a"].as_ref(),
        b"b",
        Element::empty_tree(),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    db.insert(
        [TEST_LEAF, b"a", b"b"].as_ref(),
        b"key",
        Element::new_item(b"v".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let root = root_hash(&db, v);

    // A single key at depth 1, with a limit (so also an absence proof).
    let pq = PathQuery::new(
        vec![TEST_LEAF.to_vec()],
        SizedQuery::new(Query::new_single_key(b"k03".to_vec()), Some(1), None),
    );
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let forged = as_empty_tree(&proof, &[TEST_LEAF], b"k03", v);
    let (r, rows) = GroveDb::verify_query_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_eq!((r, rows.len()), (root, 0));
    let (_, absent) = GroveDb::verify_query_with_options_and_rules(
        &forged,
        &pq,
        grovedb_merk::proofs::query::VerifyOptions {
            absence_proofs_for_non_existing_searched_keys: true,
            verify_proof_succinctness: true,
            include_empty_trees_in_result: false,
        },
        crate::ProofRules::V310,
        v,
    )
    .unwrap();
    assert_eq!(
        item_values(&absent),
        vec![None],
        "3.1.0 proves a present key absent"
    );
    assert_strict_refuses(&forged, &pq, v, "empty tree element not bound");
    assert!(GroveDb::verify_query_with_absence_proof(&forged, &pq, v).is_err());

    // A single key at depth 3 (the [subgroves, id, data]/key shape).
    let pq3 = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec(), b"a".to_vec(), b"b".to_vec()],
        Query::new_single_key(b"key".to_vec()),
    );
    let proof3 = db.prove_query(&pq3, None, v).unwrap().unwrap();
    let forged3 = as_empty_tree(&proof3, &[TEST_LEAF, b"a", b"b"], b"key", v);
    let (r, rows) = GroveDb::verify_query_v310(&forged3, &pq3, v).expect("3.1.0 accepts");
    assert_eq!((r, rows.len()), (root, 0));
    assert_strict_refuses(&forged3, &pq3, v, "empty tree element not bound");

    // A range that silently loses a row.
    let mut q = Query::new();
    q.insert_range(b"k02".to_vec()..b"k09".to_vec());
    let pqr = PathQuery::new_unsized(vec![TEST_LEAF.to_vec()], q);
    let proofr = db.prove_query(&pqr, None, v).unwrap().unwrap();
    let honest = assert_honest(&db, &pqr, v);
    assert_eq!(honest.len(), 7);
    let forgedr = as_empty_tree(&proofr, &[TEST_LEAF], b"k05", v);
    let (r, rows) = GroveDb::verify_query_v310(&forgedr, &pqr, v).expect("3.1.0 accepts");
    assert_eq!((r, rows.len()), (root, 6));
    assert_strict_refuses(&forgedr, &pqr, v, "empty tree element not bound");
}

#[test]
fn honest_empty_trees_as_result_rows_verify_strictly() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    for (k, e) in [
        (b"e1".as_slice(), Element::empty_tree()),
        (b"e2".as_slice(), Element::empty_sum_tree()),
        (b"e3".as_slice(), Element::empty_big_sum_tree()),
        (b"e4".as_slice(), Element::empty_count_tree()),
        (b"i1".as_slice(), Element::new_item(b"x".to_vec())),
    ] {
        db.insert([TEST_LEAF].as_ref(), k, e, None, None, v)
            .unwrap()
            .unwrap();
    }
    let pq = PathQuery::new_unsized(vec![TEST_LEAF.to_vec()], Query::new_range_full());
    assert_honest(&db, &pq, v);
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let (_, raw) = GroveDb::verify_query_raw(&proof, &pq, v).unwrap();
    assert_eq!(raw.len(), 5, "raw rows include the empty trees");
    let pq = PathQuery::new_unsized(
        vec![TEST_LEAF.to_vec()],
        Query::new_single_key(b"e2".to_vec()),
    );
    assert_honest(&db, &pq, v);
}

#[test]
fn tree_element_under_the_plain_hash_of_its_bytes_is_refused() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    // At the root layer, so no parent hash check catches the change first.
    db.insert(
        EMPTY_PATH,
        b"k",
        Element::new_item(b"v".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    let pq = PathQuery::new_unsized(vec![], Query::new_single_key(b"k".to_vec()));
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let tree_bytes = Element::empty_tree().serialize(v).unwrap();
    // A KV node carrying a tree's bytes: the root moves (only a 63-byte
    // collision would keep it), but strict refuses the shape outright.
    let forged = replace_node(&proof, &[], b"k", |n| match n {
        Node::KV(k, _) => Node::KV(k.clone(), tree_bytes.clone()),
        other => panic!("{other:?}"),
    });
    let (root, _) = GroveDb::verify_query_raw_v310(&forged, &pq, v).expect("3.1.0 accepts");
    assert_ne!(root, root_hash(&db, v));
    let raw = GroveDb::verify_query_raw(&forged, &pq, v);
    assert!(
        matches!(raw, Err(Error::InvalidProof(_, ref m)) if m.contains("plain hash")),
        "{raw:?}"
    );
}

// -------------------------------------------------------------------------
// Decode bounds proportional to the input (review finding)
// -------------------------------------------------------------------------

fn bomb_proof(nodes: usize) -> Vec<u8> {
    // Item tag 0x00, then a bincode varint claiming a 67,108,863-byte Vec<u8>.
    let bomb = vec![0x00u8, 0xFC, 0x03, 0xF0, 0x00, 0x00];
    let ops: Vec<Op> = (0..nodes as u32)
        .map(|i| {
            Op::Push(Node::KVValueHash(
                i.to_be_bytes().to_vec(),
                bomb.clone(),
                [0; 32],
            ))
        })
        .collect();
    encode_proof(GroveDBProofV0 {
        root_layer: LayerProof {
            merk_proof: encode_ops(&ops),
            lower_layers: Default::default(),
        },
        prove_options: Default::default(),
    })
}

#[test]
fn lying_element_lengths_are_refused_without_large_allocations() {
    let v = GroveVersion::latest();
    let pq = PathQuery::new_unsized(vec![], Query::new_single_key(vec![0xff; 5]));
    for n in [1usize, 50] {
        let proof = bomb_proof(n);
        let t = std::time::Instant::now();
        let r = GroveDb::verify_query(&proof, &pq, v);
        let elapsed = t.elapsed();
        assert!(
            matches!(r, Err(Error::InvalidProof(_, ref m)) if m.contains("not an element")),
            "{r:?}"
        );
        assert!(
            elapsed < std::time::Duration::from_secs(1),
            "{n} nodes: {elapsed:?}"
        );
    }
    // A ten-byte envelope claiming a 2 GiB merk proof.
    let mut env = vec![0x00, 0xFC];
    env.extend_from_slice(&0x7FFF_FFFFu32.to_be_bytes());
    env.extend_from_slice(&[0; 4]);
    let t = std::time::Instant::now();
    let r = GroveDb::verify_query(&env, &pq, v);
    assert!(
        matches!(r, Err(Error::CorruptedData(ref m)) if m.contains("unable to decode proof")),
        "{r:?}"
    );
    assert!(t.elapsed() < std::time::Duration::from_secs(1));
}

#[test]
fn honest_proofs_claiming_more_than_their_length_still_verify() {
    let v = GroveVersion::latest();
    let db = make_test_grovedb(v);
    // Many small lower layers in one map.
    for i in 0..300u16 {
        let k = i.to_be_bytes();
        db.insert(
            [TEST_LEAF].as_ref(),
            &k,
            Element::empty_tree(),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
        db.insert(
            [TEST_LEAF, k.as_slice()].as_ref(),
            b"x",
            Element::new_item(vec![1]),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    let mut q = Query::new_range_full();
    q.set_subquery(Query::new_range_full());
    let pq = PathQuery::new_unsized(vec![TEST_LEAF.to_vec()], q);
    assert_eq!(assert_honest(&db, &pq, v).len(), 300);

    // A reference with a 101-segment path, left unresolved in a KVValueHash
    // node once the limit is spent, which strict still decodes.
    let mut path: Vec<Vec<u8>> = vec![b"deep".to_vec()];
    db.insert(EMPTY_PATH, b"deep", Element::empty_tree(), None, None, v)
        .unwrap()
        .unwrap();
    for i in 0..99u8 {
        let p: Vec<&[u8]> = path.iter().map(|s| s.as_slice()).collect();
        db.insert(p.as_slice(), &[i], Element::empty_tree(), None, None, v)
            .unwrap()
            .unwrap();
        path.push(vec![i]);
    }
    let p: Vec<&[u8]> = path.iter().map(|s| s.as_slice()).collect();
    db.insert(
        p.as_slice(),
        b"it",
        Element::new_item(b"end".to_vec()),
        None,
        None,
        v,
    )
    .unwrap()
    .unwrap();
    path.push(b"it".to_vec());
    let reference = Element::new_reference(ReferencePathType::AbsolutePathReference(path));
    let ref_bytes = reference.serialize(v).unwrap();
    // 101 segments claim 101 * 24 bytes up front: more than a bound of twice
    // the element's length, even with a 1 KiB floor, would allow.
    assert!(101 * 24 > (2 * ref_bytes.len()).next_power_of_two().max(1024) * 2);
    db.insert(EMPTY_PATH, b"zz_ref", reference, None, None, v)
        .unwrap()
        .unwrap();
    db.insert(EMPTY_PATH, b"a_tree", Element::empty_tree(), None, None, v)
        .unwrap()
        .unwrap();
    for k in [b"1", b"2"] {
        db.insert(
            [b"a_tree".as_slice()].as_ref(),
            k,
            Element::new_item(vec![2]),
            None,
            None,
            v,
        )
        .unwrap()
        .unwrap();
    }
    let mut q = Query::new();
    q.insert_key(b"a_tree".to_vec());
    q.insert_key(b"zz_ref".to_vec());
    q.set_subquery(Query::new_range_full());
    let pq = PathQuery::new(vec![], SizedQuery::new(q, Some(2), None));
    let proof = db.prove_query(&pq, None, v).unwrap().unwrap();
    let unresolved = |op: &Op| match op {
        Op::Push(Node::KVValueHash(k, value, _)) => k == b"zz_ref" && value == &ref_bytes,
        _ => false,
    };
    assert!(ops(&decode_proof(&proof).root_layer.merk_proof)
        .iter()
        .any(unresolved));
    assert_eq!(assert_honest(&db, &pq, v).len(), 2);
}
