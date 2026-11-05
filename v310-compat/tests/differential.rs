//! Differential tests against crates.io grovedb 3.1.0 (`grovedb_v310`).
//!
//! 1. State: the same inserts give the same root hash in this fork and in 3.1.0
//!    (the fork changes no stored state).
//! 2. Encoding: every proof of values under 64 KiB is byte-identical to the one
//!    3.1.0 produces, and every value-carrying merk op under 64 KiB encodes
//!    exactly as 3.1.0's encoder does.
//! 3. Legacy verification: `GroveDb::verify_query_v310` and
//!    `GroveDb::verify_query_raw_v310` give the same `Debug` output (same
//!    Ok/Err, same root, same rows, same error text) as 3.1.0's `verify_query`
//!    and `verify_query_raw` on honest proofs, forgeries, a proof containing
//!    large-value ops, every truncation, single-byte corruptions, and garbage.
//!    Merk's `verify_proof_v310` likewise matches 3.1.0's `verify_proof`.
//! 4. Strict verification agrees with 3.1.0 on every honest proof except a
//!    query whose path runs through an item, and refuses every forgery.

use std::fmt::Debug;

use grovedb::{
    operations::proof::{GroveDBProof, GroveDBProofV0, LayerProof},
    reference_path::ReferencePathType,
    Element, GroveDb, PathQuery, Query, SizedQuery,
};
use grovedb_merk::{
    proofs::{encode_into, Decoder, Node, Op},
    tree::{combine_hash, kv_hash, node_hash, value_hash, NULL_HASH},
};
use grovedb_version::version::GroveVersion;
use grovedb_version_v310::version::GroveVersion as GroveVersionV310;

fn fv() -> &'static GroveVersion {
    GroveVersion::latest()
}
fn bv() -> &'static GroveVersionV310 {
    GroveVersionV310::latest()
}

fn cfg() -> impl bincode::config::Config {
    bincode::config::standard()
        .with_big_endian()
        .with_no_limit()
}

// ---------------------------------------------------------------------------
// Building the same state in both
// ---------------------------------------------------------------------------

struct Pair {
    _dirs: (tempfile::TempDir, tempfile::TempDir),
    fork: GroveDb,
    base: grovedb_v310::GroveDb,
}

impl Pair {
    fn new() -> Self {
        let a = tempfile::TempDir::new().unwrap();
        let b = tempfile::TempDir::new().unwrap();
        let fork = GroveDb::open(a.path()).unwrap();
        let base = grovedb_v310::GroveDb::open(b.path()).unwrap();
        Pair {
            _dirs: (a, b),
            fork,
            base,
        }
    }

    fn insert(&self, path: &[&[u8]], key: &[u8], element: Element) {
        let bytes = element.serialize(fv()).unwrap();
        let base_element = grovedb_v310::Element::deserialize(&bytes, bv()).unwrap();
        self.fork
            .insert(path, key, element, None, None, fv())
            .unwrap()
            .expect("fork insert");
        self.base
            .insert(path, key, base_element, None, None, bv())
            .unwrap()
            .expect("3.1.0 insert");
    }

    fn roots(&self) -> ([u8; 32], [u8; 32]) {
        (
            self.fork.root_hash(None, fv()).unwrap().unwrap(),
            self.base.root_hash(None, bv()).unwrap().unwrap(),
        )
    }
}

fn base_query(pq: &PathQuery) -> grovedb_v310::PathQuery {
    let bytes = bincode::encode_to_vec(pq, cfg()).unwrap();
    let (q, used): (grovedb_v310::PathQuery, usize) =
        bincode::decode_from_slice(&bytes, cfg()).unwrap();
    assert_eq!(used, bytes.len());
    q
}

const T: &[u8] = b"t";
const S: &[u8] = b"s";
const D: &[u8] = b"d";
const A: &[u8] = b"a";
const H: &[u8] = b"h";

fn populate(p: &Pair) {
    let e: &[&[u8]] = &[];
    p.insert(e, T, Element::empty_tree());
    p.insert(e, S, Element::empty_sum_tree());
    p.insert(e, D, Element::empty_tree());
    p.insert(e, A, Element::empty_tree());
    for i in 0..20u8 {
        let k = format!("k{i:02}");
        // 65,530 bytes of value is a 65,535-byte merk value (element framing
        // adds 5), the largest 3.1.0 encodes.
        let len = [0usize, 1, 63, 64, 200, 1000, 4096, 65_530][i as usize % 8];
        let v: Vec<u8> = (0..len).map(|j| (j as u8).wrapping_mul(i + 3)).collect();
        p.insert(&[T], k.as_bytes(), Element::new_item(v));
    }
    p.insert(&[T], b"inner", Element::empty_tree());
    p.insert(&[T], b"empty", Element::empty_tree());
    p.insert(&[T], b"item_on_path", Element::new_item(b"i".to_vec()));
    p.insert(
        &[T],
        b"ref1",
        Element::new_reference(ReferencePathType::AbsolutePathReference(vec![
            T.to_vec(),
            b"k05".to_vec(),
        ])),
    );
    p.insert(
        &[T],
        b"ref2",
        Element::new_reference(ReferencePathType::SiblingReference(b"k06".to_vec())),
    );
    for i in 1..=5u8 {
        p.insert(
            &[T, b"inner"],
            &[b'i', b'0' + i],
            Element::new_item(vec![i; 40]),
        );
    }
    for (k, n) in [(b"s1", 1i64), (b"s2", -2), (b"s3", 300)] {
        p.insert(&[S], k, Element::new_sum_item(n));
    }
    p.insert(&[S], b"st", Element::empty_sum_tree());
    p.insert(&[S, b"st"], b"z", Element::new_sum_item(9));
    for n in [b"n1", b"n2", b"n3"] {
        p.insert(&[D], n, Element::empty_tree());
        for x in [b"x1", b"x2"] {
            p.insert(&[D, n], x, Element::empty_tree());
            for k in 0..4u8 {
                p.insert(
                    &[D, n, x],
                    &[b'v', b'0' + k],
                    Element::new_item(vec![k; 10]),
                );
            }
        }
    }
    p.insert(&[A], b"bs", Element::empty_big_sum_tree());
    p.insert(&[A], b"ct", Element::empty_count_tree());
    p.insert(&[A, b"ct"], b"c1", Element::new_item(b"c".to_vec()));
    p.insert(&[A], b"es", Element::empty_sum_tree());
    // a three-node tree: k3 is a leaf
    p.insert(e, H, Element::empty_tree());
    for k in [b"k3", b"k5", b"k7"] {
        p.insert(&[H], k, Element::new_item(k.to_vec()));
    }
}

fn queries() -> Vec<(&'static str, PathQuery)> {
    let mut out: Vec<(&'static str, PathQuery)> = vec![];
    let key = |path: Vec<&[u8]>, k: &[u8]| {
        PathQuery::new_unsized(
            path.into_iter().map(|p| p.to_vec()).collect(),
            Query::new_single_key(k.to_vec()),
        )
    };
    out.push(("present item", key(vec![T], b"k03")));
    out.push(("present 65,535-byte merk value", key(vec![T], b"k07")));
    out.push(("absent key", key(vec![T], b"k035")));
    out.push(("absolute reference", key(vec![T], b"ref1")));
    out.push(("sibling reference", key(vec![T], b"ref2")));
    out.push(("tree as result", key(vec![T], b"inner")));
    out.push(("empty tree as result", key(vec![T], b"empty")));
    out.push(("two levels", key(vec![T, b"inner"], b"i3")));
    out.push(("four levels", key(vec![D, b"n2", b"x1"], b"v2")));
    out.push(("path through empty tree", key(vec![T, b"empty"], b"x")));
    out.push(("path through missing key", key(vec![T, b"missing"], b"x")));
    out.push(("path through item", key(vec![T, b"item_on_path"], b"x")));
    out.push(("sum item", key(vec![S], b"s2")));
    out.push(("sum tree child", key(vec![S, b"st"], b"z")));
    out.push(("count tree child", key(vec![A, b"ct"], b"c1")));
    out.push(("path through empty big sum tree", key(vec![A, b"bs"], b"x")));
    out.push(("path through empty sum tree", key(vec![A, b"es"], b"x")));
    for (name, ltr, limit) in [
        ("range ltr limit 3", true, Some(3u16)),
        ("range rtl limit 4", false, Some(4)),
        ("range ltr no limit", true, None),
    ] {
        let mut q = Query::new_with_direction(ltr);
        q.insert_range(b"k02".to_vec()..b"k09".to_vec());
        out.push((
            name,
            PathQuery::new(vec![T.to_vec()], SizedQuery::new(q, limit, None)),
        ));
    }
    out.push((
        "range full of t",
        PathQuery::new_unsized(vec![T.to_vec()], Query::new_range_full()),
    ));
    out.push((
        "root range",
        PathQuery::new_unsized(vec![], Query::new_range_full()),
    ));
    out.push((
        "sum tree range",
        PathQuery::new_unsized(vec![S.to_vec()], Query::new_range_full()),
    ));
    for limit in [None, Some(1u16), Some(5), Some(30)] {
        let mut q = Query::new_range_full();
        let mut sub = Query::new_range_full();
        sub.set_subquery(Query::new_range_full());
        q.set_subquery(sub);
        out.push((
            "subquery x2",
            PathQuery::new(vec![D.to_vec()], SizedQuery::new(q, limit, None)),
        ));
    }
    let mut q = Query::new_range_full();
    q.set_subquery_key(b"x2".to_vec());
    q.set_subquery(Query::new_single_key(b"v1".to_vec()));
    out.push(("subquery path", PathQuery::new_unsized(vec![D.to_vec()], q)));
    let mut q = Query::new_single_key(T.to_vec());
    q.insert_key(S.to_vec());
    q.set_subquery(Query::new_range_full());
    out.push((
        "subquery over mixed elements",
        PathQuery::new(vec![], SizedQuery::new(q, Some(40), None)),
    ));
    let mut q = Query::new();
    q.insert_key(b"k01".to_vec());
    q.insert_key(b"k011".to_vec());
    q.insert_key(b"zz".to_vec());
    out.push((
        "keys with limit (absence-proof shape)",
        PathQuery::new(vec![T.to_vec()], SizedQuery::new(q, Some(10), None)),
    ));
    out
}

// ---------------------------------------------------------------------------
// Comparing verdicts
// ---------------------------------------------------------------------------

fn dbg<T: Debug>(t: &T) -> String {
    format!("{t:?}")
}

static ABORTING_REFUSED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static LIMIT_REFUSALS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Whether 3.1.0's unbounded bincode decoding can run on `bytes` without
/// trying to allocate a lying length. 3.1.0 decodes the envelope and each
/// element with no size limit and resizes a byte string to its claimed length
/// before reading it, so such an input can abort the process: it is not run
/// through 3.1.0, and the fork's `_v310` path must return an error for it.
/// Decoding is deterministic, so an input that a bounded decode refuses for
/// another reason fails identically, with no large allocation, unbounded.
fn safe_for_unbounded_decoders(bytes: &[u8]) -> bool {
    use bincode::error::DecodeError::LimitExceeded;
    let cfg = bincode::config::standard()
        .with_big_endian()
        .with_limit::<{ 16 << 20 }>();
    let proof: GroveDBProof = match bincode::decode_from_slice(bytes, cfg) {
        Err(LimitExceeded) => return false,
        Err(_) => return true,
        Ok((p, _)) => p,
    };
    let GroveDBProof::V0(v0) = proof;
    let mut stack = vec![&v0.root_layer];
    while let Some(l) = stack.pop() {
        for op in Decoder::new_v310(&l.merk_proof) {
            let Ok(op) = op else { break };
            if let Op::Push(n) | Op::PushInverted(n) = op {
                let value = match &n {
                    Node::KV(_, v)
                    | Node::KVValueHash(_, v, _)
                    | Node::KVRefValueHash(_, v, _)
                    | Node::KVValueHashFeatureType(_, v, ..) => v,
                    _ => continue,
                };
                if let Err(LimitExceeded) = bincode::decode_from_slice::<Element, _>(value, cfg) {
                    return false;
                }
            }
        }
        stack.extend(l.lower_layers.values());
    }
    true
}

/// Legacy (fork `_v310`) vs 3.1.0 on the same bytes. Returns whether 3.1.0
/// accepted.
fn assert_legacy_matches(proof: &[u8], pq: &PathQuery, what: &str) -> bool {
    let fork_a = || {
        GroveDb::verify_query_with_options_and_rules(
            proof,
            pq,
            absence_options(),
            grovedb::ProofRules::V310,
            fv(),
        )
    };
    if !safe_for_unbounded_decoders(proof) {
        ABORTING_REFUSED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        // 3.1.0 would allocate the lying length; the fork's _v310 refuses it.
        assert!(
            GroveDb::verify_query_v310(proof, pq, fv()).is_err(),
            "{what}"
        );
        assert!(
            GroveDb::verify_query_raw_v310(proof, pq, fv()).is_err(),
            "{what}"
        );
        if pq.query.limit.is_some() {
            assert!(fork_a().is_err(), "{what}");
        }
        let _ = GroveDb::verify_query(proof, pq, fv());
        let _ = GroveDb::verify_query_raw(proof, pq, fv());
        return false;
    }
    let bpq = base_query(pq);
    let fork_q = GroveDb::verify_query_v310(proof, pq, fv());
    let base_q = grovedb_v310::GroveDb::verify_query(proof, &bpq, bv());
    same_verdict(&fork_q, &base_q, "verify_query", what);
    let fork_r = GroveDb::verify_query_raw_v310(proof, pq, fv());
    let base_r = grovedb_v310::GroveDb::verify_query_raw(proof, &bpq, bv());
    same_verdict(&fork_r, &base_r, "verify_query_raw", what);
    if pq.query.limit.is_some() {
        let base_a = grovedb_v310::GroveDb::verify_query_with_absence_proof(proof, &bpq, bv());
        same_verdict(&fork_a(), &base_a, "absence proof", what);
    }
    base_q.is_ok()
}

/// The fork's `_v310` result matches 3.1.0's exactly (`Debug`: Ok/Err, root,
/// rows, error text), except that where the fork's bounded decode refused a
/// length claim the input couldn't satisfy (`LimitExceeded`), 3.1.0 must have
/// failed too, on the same input, after allocating the claim.
fn same_verdict<A: Debug, B: Debug, E1: Debug, E2: Debug>(
    fork: &Result<A, E1>,
    base: &Result<B, E2>,
    which: &str,
    what: &str,
) {
    if let (Err(f), Err(_)) = (fork, base) {
        if dbg(f).contains("LimitExceeded") {
            LIMIT_REFUSALS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return;
        }
    }
    assert_eq!(dbg(fork), dbg(base), "{which} differs: {what}");
}

fn absence_options() -> grovedb::VerifyOptions {
    grovedb::VerifyOptions {
        absence_proofs_for_non_existing_searched_keys: true,
        verify_proof_succinctness: true,
        include_empty_trees_in_result: false,
    }
}

/// Strict on an honest proof equals 3.1.0.
fn assert_strict_matches(proof: &[u8], pq: &PathQuery, what: &str) {
    let bpq = base_query(pq);
    assert_eq!(
        dbg(&GroveDb::verify_query(proof, pq, fv())),
        dbg(&grovedb_v310::GroveDb::verify_query(proof, &bpq, bv())),
        "strict verify_query differs from 3.1.0 on an honest proof: {what}"
    );
    assert_eq!(
        dbg(&GroveDb::verify_query_raw(proof, pq, fv())),
        dbg(&grovedb_v310::GroveDb::verify_query_raw(proof, &bpq, bv())),
        "strict verify_query_raw differs from 3.1.0 on an honest proof: {what}"
    );
}

fn assert_strict_refuses(proof: &[u8], pq: &PathQuery, what: &str) {
    assert!(
        GroveDb::verify_query(proof, pq, fv()).is_err(),
        "strict accepted: {what}"
    );
    assert!(
        GroveDb::verify_query_raw(proof, pq, fv()).is_err(),
        "strict raw accepted: {what}"
    );
}

/// Every truncation, a corruption of every byte (bounded), and garbage.
fn mutations(proof: &[u8]) -> Vec<Vec<u8>> {
    let mut out = vec![];
    let stride = (proof.len() / 400).max(1);
    for len in (0..proof.len()).step_by(stride) {
        out.push(proof[..len].to_vec());
    }
    let stride = (proof.len() / 150).max(1);
    for i in (0..proof.len()).step_by(stride) {
        for x in [0x01u8, 0x80, 0xff] {
            let mut p = proof.to_vec();
            p[i] ^= x;
            out.push(p);
        }
    }
    let mut extra = proof.to_vec();
    extra.push(0);
    out.push(extra);
    out
}

fn garbage() -> Vec<Vec<u8>> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let mut out = vec![vec![], vec![0], vec![1], vec![0, 0, 0, 0], vec![0xff; 64]];
    for len in [1usize, 2, 3, 8, 33, 100, 1000, 5000] {
        for _ in 0..20 {
            out.push((0..len).map(|_| next() as u8).collect());
        }
    }
    // Well-formed envelope around a garbage merk proof
    for len in [0usize, 1, 2, 5, 40, 300] {
        for _ in 0..10 {
            let merk: Vec<u8> = (0..len).map(|_| next() as u8).collect();
            out.push(encode_proof(GroveDBProofV0 {
                root_layer: LayerProof {
                    merk_proof: merk,
                    lower_layers: Default::default(),
                },
                prove_options: Default::default(),
            }));
        }
    }
    out
}

fn decode_proof(bytes: &[u8]) -> GroveDBProofV0 {
    let (GroveDBProof::V0(v0), _) = bincode::decode_from_slice(bytes, cfg()).unwrap();
    v0
}

fn encode_proof(v0: GroveDBProofV0) -> Vec<u8> {
    bincode::encode_to_vec(GroveDBProof::V0(v0), cfg()).unwrap()
}

fn ops(merk_proof: &[u8]) -> Vec<Op> {
    Decoder::new(merk_proof).map(|o| o.unwrap()).collect()
}

fn encode_ops(ops: &[Op]) -> Vec<u8> {
    let mut out = vec![];
    encode_into(ops.iter(), &mut out);
    out
}

fn layer<'a>(root: &'a mut LayerProof, path: &[&[u8]]) -> &'a mut LayerProof {
    let mut l = root;
    for s in path {
        l = l.lower_layers.get_mut(*s).unwrap();
    }
    l
}

fn rewrite(proof: &[u8], path: &[&[u8]], f: impl Fn(Vec<Op>) -> Vec<Op>) -> Vec<u8> {
    let mut v0 = decode_proof(proof);
    let l = layer(&mut v0.root_layer, path);
    l.merk_proof = encode_ops(&f(ops(&l.merk_proof)));
    encode_proof(v0)
}

fn map_node(ops: Vec<Op>, key: &[u8], f: impl Fn(Node) -> Node) -> Vec<Op> {
    ops.into_iter()
        .map(|op| match op {
            Op::Push(n) if node_key(&n) == Some(key) => Op::Push(f(n)),
            Op::PushInverted(n) if node_key(&n) == Some(key) => Op::PushInverted(f(n)),
            o => o,
        })
        .collect()
}

fn node_key(n: &Node) -> Option<&[u8]> {
    match n {
        Node::KV(k, _)
        | Node::KVValueHash(k, ..)
        | Node::KVDigest(k, _)
        | Node::KVRefValueHash(k, ..)
        | Node::KVValueHashFeatureType(k, ..) => Some(k),
        _ => None,
    }
}

fn drop_lower(proof: &[u8], path: &[&[u8]], key: &[u8]) -> Vec<u8> {
    let mut v0 = decode_proof(proof);
    layer(&mut v0.root_layer, path)
        .lower_layers
        .remove(key)
        .unwrap();
    encode_proof(v0)
}

// ---------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------

#[test]
fn same_state_same_proofs_same_legacy_verdicts() {
    let p = Pair::new();
    populate(&p);
    let (fork_root, base_root) = p.roots();
    assert_eq!(fork_root, base_root, "root hash differs from 3.1.0");

    let mut honest_count = 0;
    let mut mutation_count = 0;
    let mut base_accepted_mutations = 0;
    for (name, pq) in queries() {
        let fork_proof = p.fork.prove_query(&pq, None, fv()).unwrap();
        let base_proof = p.base.prove_query(&base_query(&pq), None, bv()).unwrap();
        assert_eq!(
            dbg(&fork_proof),
            dbg(&base_proof),
            "proof bytes differ: {name}"
        );
        let proof = fork_proof.expect(name);
        honest_count += 1;

        assert!(
            assert_legacy_matches(&proof, &pq, name),
            "3.1.0 refused honest {name}"
        );
        if name == "path through item" {
            // Strict refuses by design; 3.1.0 returns the item as a row.
            assert_strict_refuses(&proof, &pq, name);
        } else {
            assert_strict_matches(&proof, &pq, name);
        }

        for m in mutations(&proof) {
            mutation_count += 1;
            if assert_legacy_matches(&m, &pq, name) {
                base_accepted_mutations += 1;
            }
        }
    }
    for g in garbage() {
        for (name, pq) in queries().into_iter().take(6) {
            assert_legacy_matches(&g, &pq, name);
        }
    }
    println!(
        "honest proofs: {honest_count} (byte-identical to 3.1.0); mutations: {mutation_count} \
         (3.1.0 accepted {base_accepted_mutations}); garbage inputs: {}; inputs that could abort \
         3.1.0, refused by _v310 (all tests so far): {}; both Err, the fork's by its claim limit: \
         {}",
        garbage().len(),
        ABORTING_REFUSED.load(std::sync::atomic::Ordering::Relaxed),
        LIMIT_REFUSALS.load(std::sync::atomic::Ordering::Relaxed)
    );
}

#[test]
fn forgeries_legacy_matches_and_strict_refuses() {
    let p = Pair::new();
    populate(&p);
    let root = p.roots().0;
    let mut forged: Vec<(&str, PathQuery, Vec<u8>)> = vec![];

    // 1. KV -> KVValueHash (item)
    let pq = PathQuery::new_unsized(vec![T.to_vec()], Query::new_single_key(b"k03".to_vec()));
    let proof = p.fork.prove_query(&pq, None, fv()).unwrap().unwrap();
    let fake = Element::new_item(b"attacker".to_vec())
        .serialize(fv())
        .unwrap();
    forged.push((
        "KV->KVValueHash item",
        pq.clone(),
        rewrite(&proof, &[T], |o| {
            map_node(o, b"k03", |n| match n {
                Node::KV(k, v) => Node::KVValueHash(k, fake.clone(), value_hash(&v).unwrap()),
                n => panic!("{n:?}"),
            })
        }),
    ));
    // 2. KV -> KVRefValueHash (3.1.0 refuses too: the root moves)
    forged.push((
        "KV->KVRefValueHash item",
        pq.clone(),
        rewrite(&proof, &[T], |o| {
            map_node(o, b"k03", |n| match n {
                Node::KV(k, v) => Node::KVRefValueHash(k, fake.clone(), value_hash(&v).unwrap()),
                n => panic!("{n:?}"),
            })
        }),
    ));
    // 3. SumItem in KVValueHash with a forged sum
    let pq_s = PathQuery::new_unsized(vec![S.to_vec()], Query::new_single_key(b"s2".to_vec()));
    let proof_s = p.fork.prove_query(&pq_s, None, fv()).unwrap().unwrap();
    let fake_sum = Element::new_sum_item(1_000_000).serialize(fv()).unwrap();
    forged.push((
        "forged sum item",
        pq_s.clone(),
        rewrite(&proof_s, &[S], |o| {
            map_node(o, b"s2", |n| match n {
                Node::KVValueHash(k, _, vh) => Node::KVValueHash(k, fake_sum.clone(), vh),
                n => panic!("{n:?}"),
            })
        }),
    ));
    // 4. Forged row under a Hash node: find a leaf KV in t's proof for a
    // single key and swap it for Hash(leaf) + forged child.
    let leaf_key = b"k3";
    let pq_l = PathQuery::new_unsized(vec![H.to_vec()], Query::new_single_key(leaf_key.to_vec()));
    let proof_l = p.fork.prove_query(&pq_l, None, fv()).unwrap().unwrap();
    let leaf_bytes = Element::new_item(b"k3".to_vec()).serialize(fv()).unwrap();
    let leaf_hash = node_hash(
        &kv_hash(leaf_key, &leaf_bytes).unwrap(),
        &NULL_HASH,
        &NULL_HASH,
    )
    .unwrap();
    forged.push((
        "forged row under Hash",
        pq_l.clone(),
        rewrite(&proof_l, &[H], |o| {
            let mut out = vec![];
            for op in o {
                match op {
                    Op::Push(Node::KV(ref k, _)) if k == leaf_key => {
                        out.push(Op::Push(Node::Hash(leaf_hash)));
                        out.push(Op::Push(Node::KV(leaf_key.to_vec(), fake.clone())));
                        out.push(Op::Child);
                    }
                    o => out.push(o),
                }
            }
            out
        }),
    ));
    // 5..7. Descent-path forgeries on [t, inner]
    let pq_i = PathQuery::new(
        vec![T.to_vec(), b"inner".to_vec()],
        SizedQuery::new(Query::new_single_key(b"i3".to_vec()), Some(1), None),
    );
    let proof_i = p.fork.prove_query(&pq_i, None, fv()).unwrap().unwrap();
    forged.push((
        "dropped lower layer",
        pq_i.clone(),
        drop_lower(&proof_i, &[T], b"inner"),
    ));
    let mut renamed = decode_proof(&proof_i);
    let l = layer(&mut renamed.root_layer, &[T]);
    let inner = l.lower_layers.remove(b"inner".as_slice()).unwrap();
    l.lower_layers.insert(b"innes".to_vec(), inner);
    forged.push(("renamed lower layer", pq_i.clone(), encode_proof(renamed)));
    let empty = Element::empty_tree().serialize(fv()).unwrap();
    let as_empty = rewrite(&proof_i, &[T], |o| {
        map_node(o, b"inner", |n| match n {
            Node::KVValueHash(k, _, vh) => Node::KVValueHash(k, empty.clone(), vh),
            n => panic!("{n:?}"),
        })
    });
    forged.push((
        "subtree presented as empty tree",
        pq_i.clone(),
        drop_lower(&as_empty, &[T], b"inner"),
    ));
    let as_item = rewrite(&proof_i, &[T], |o| {
        map_node(o, b"inner", |n| match n {
            Node::KVValueHash(k, _, vh) => Node::KVValueHash(k, fake.clone(), vh),
            n => panic!("{n:?}"),
        })
    });
    forged.push((
        "item standing in for a subtree",
        pq_i.clone(),
        drop_lower(&as_item, &[T], b"inner"),
    ));
    // 8. Unresolved reference through KVValueHash
    let pq_r = PathQuery::new_unsized(vec![T.to_vec()], Query::new_single_key(b"ref1".to_vec()));
    let proof_r = p.fork.prove_query(&pq_r, None, fv()).unwrap().unwrap();
    let fake_ref = Element::new_reference(ReferencePathType::AbsolutePathReference(vec![
        b"nowhere".to_vec(),
    ]))
    .serialize(fv())
    .unwrap();
    forged.push((
        "unresolved reference",
        pq_r.clone(),
        rewrite(&proof_r, &[T], |o| {
            map_node(o, b"ref1", |n| match n {
                Node::KVRefValueHash(k, referenced, nvh) => {
                    let committed = combine_hash(&nvh, &value_hash(&referenced).unwrap()).unwrap();
                    Node::KVValueHash(k, fake_ref.clone(), committed)
                }
                n => panic!("{n:?}"),
            })
        }),
    ));

    for (name, pq, bytes) in &forged {
        let base_accepts = assert_legacy_matches(bytes, pq, name);
        let expect_base_accepts = *name != "KV->KVRefValueHash item";
        if expect_base_accepts {
            assert!(base_accepts, "3.1.0 should accept the forgery: {name}");
            let (r, _) =
                grovedb_v310::GroveDb::verify_query_raw(bytes, &base_query(pq), bv()).unwrap();
            assert_eq!(r, root, "forgery at the honest root: {name}");
        }
        if expect_base_accepts {
            assert_strict_refuses(bytes, pq, name);
        } else {
            // The root moves, so neither accepts it at the honest root.
            for r in [
                GroveDb::verify_query(bytes, pq, fv()).map(|x| x.0),
                GroveDb::verify_query_v310(bytes, pq, fv()).map(|x| x.0),
            ] {
                assert!(r.map(|h| h != root).unwrap_or(true), "{name}");
            }
        }
        for m in mutations(bytes).into_iter().step_by(7) {
            assert_legacy_matches(&m, pq, name);
        }
    }
    println!("forgeries compared: {}", forged.len());
}

#[test]
fn large_values_state_proofs_and_legacy_verdicts() {
    let p = Pair::new();
    let e: &[&[u8]] = &[];
    p.insert(e, T, Element::empty_tree());
    // value lengths; the merk value (serialized Item) is 5 bytes longer
    let sizes = [65_530usize, 65_531, 65_537, 512 * 1024, 1 << 20];
    for (i, len) in sizes.iter().enumerate() {
        let v: Vec<u8> = (0..*len).map(|j| (j % 241) as u8).collect();
        p.insert(&[T], format!("big{i}").as_bytes(), Element::new_item(v));
    }
    p.insert(&[T], b"small", Element::new_item(b"s".to_vec()));
    let (fork_root, base_root) = p.roots();
    assert_eq!(
        fork_root, base_root,
        "large values: root hash differs from 3.1.0"
    );

    for (i, len) in sizes.iter().enumerate() {
        let pq = PathQuery::new_unsized(
            vec![T.to_vec()],
            Query::new_single_key(format!("big{i}").into_bytes()),
        );
        let proof = p.fork.prove_query(&pq, None, fv()).unwrap().unwrap();
        let has_large_op = decode_proof(&proof)
            .root_layer
            .lower_layers
            .get(T)
            .map(|l| {
                ops(&l.merk_proof).iter().any(|op| match op {
                    Op::Push(Node::KV(_, v)) | Op::PushInverted(Node::KV(_, v)) => {
                        v.len() >= 65_536
                    }
                    _ => false,
                })
            })
            .unwrap();
        let small = len + 5 < 65_536;
        assert_eq!(has_large_op, !small);
        let base_accepts = assert_legacy_matches(&proof, &pq, "large value");
        assert_eq!(base_accepts, small, "3.1.0 decodes only < 64 KiB");
        let (r, rows) = GroveDb::verify_query(&proof, &pq, fv()).expect("strict verifies");
        assert_eq!(r, fork_root);
        match &rows[0].2 {
            Some(Element::Item(b, _)) => assert_eq!(b.len(), *len),
            o => panic!("{o:?}"),
        }
        for m in mutations(&proof).into_iter().step_by(11) {
            assert_legacy_matches(&m, &pq, "large value mutation");
        }

        if small {
            let base_proof = p
                .base
                .prove_query(&base_query(&pq), None, bv())
                .unwrap()
                .unwrap();
            assert_eq!(
                base_proof, proof,
                "65,535-byte merk value: proof bytes differ"
            );
        } else if !cfg!(debug_assertions) {
            // 3.1.0's release-mode prover truncates the u16 length; its
            // proof is not the fork's and 3.1.0 cannot verify it.
            let base_proof = p
                .base
                .prove_query(&base_query(&pq), None, bv())
                .unwrap()
                .unwrap();
            assert_ne!(base_proof, proof);
            let base_verdict =
                grovedb_v310::GroveDb::verify_query(&base_proof, &base_query(&pq), bv());
            let mis_encoded = match &base_verdict {
                Err(_) => true,
                Ok((_, rows)) => !matches!(
                    rows.first().and_then(|r| r.2.as_ref()),
                    Some(grovedb_v310::Element::Item(b, _)) if b.len() == *len
                ),
            };
            assert!(mis_encoded, "3.1.0 release prover should mis-encode {len}");
            println!(
                "{len}-byte value: 3.1.0 proof is mis-encoded (verify -> {})",
                match base_verdict {
                    Ok(_) => "Ok with a wrong value".to_string(),
                    Err(e) => format!("Err {e}"),
                }
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Merk level
// ---------------------------------------------------------------------------

fn base_op(op: &Op) -> grovedb_merk_v310::proofs::Op {
    use grovedb_merk_v310::proofs::{Node as BN, Op as BO};
    let ft = |f: &grovedb_merk::TreeFeatureType| {
        let mut b = vec![];
        grovedb_merk::ed::Encode::encode_into(f, &mut b).unwrap();
        <grovedb_merk_v310::TreeFeatureType as grovedb_merk_v310::ed::Decode>::decode(b.as_slice())
            .unwrap()
    };
    let node = |n: &Node| match n {
        Node::Hash(h) => BN::Hash(*h),
        Node::KVHash(h) => BN::KVHash(*h),
        Node::KVDigest(k, h) => BN::KVDigest(k.clone(), *h),
        Node::KV(k, v) => BN::KV(k.clone(), v.clone()),
        Node::KVValueHash(k, v, h) => BN::KVValueHash(k.clone(), v.clone(), *h),
        Node::KVRefValueHash(k, v, h) => BN::KVRefValueHash(k.clone(), v.clone(), *h),
        Node::KVValueHashFeatureType(k, v, h, f) => {
            BN::KVValueHashFeatureType(k.clone(), v.clone(), *h, ft(f))
        }
    };
    match op {
        Op::Push(n) => BO::Push(node(n)),
        Op::PushInverted(n) => BO::PushInverted(node(n)),
        Op::Parent => BO::Parent,
        Op::Child => BO::Child,
        Op::ParentInverted => BO::ParentInverted,
        Op::ChildInverted => BO::ChildInverted,
    }
}

fn carries_value(op: &Op) -> bool {
    match op {
        Op::Push(n) | Op::PushInverted(n) => {
            !matches!(n, Node::Hash(_) | Node::KVHash(_) | Node::KVDigest(..))
        }
        _ => false,
    }
}

fn encode_base(op: &Op) -> Vec<u8> {
    let mut b = vec![];
    grovedb_merk_v310::ed::Encode::encode_into(&base_op(op), &mut b).unwrap();
    b
}

fn encode_fork(op: &Op) -> Vec<u8> {
    let mut b = vec![];
    grovedb_merk::ed::Encode::encode_into(op, &mut b).unwrap();
    b
}

#[test]
fn merk_op_encoding_matches_v310_below_64k() {
    use grovedb_merk::TreeFeatureType::{BasicMerkNode, BigSummedMerkNode, SummedMerkNode};
    let mut checked = 0;
    let lens: &[usize] = if cfg!(debug_assertions) {
        &[0, 1, 255, 256, 65_535]
    } else {
        &[0, 1, 255, 256, 65_535, 65_536, 70_000, 512 * 1024]
    };
    for &len in lens {
        let v: Vec<u8> = (0..len).map(|i| (i % 7) as u8).collect();
        let k = b"key".to_vec();
        let h = [9u8; 32];
        let mut all = vec![];
        for inv in [false, true] {
            let w = |n: Node| {
                if inv {
                    Op::PushInverted(n)
                } else {
                    Op::Push(n)
                }
            };
            all.push(w(Node::KV(k.clone(), v.clone())));
            all.push(w(Node::KVValueHash(k.clone(), v.clone(), h)));
            all.push(w(Node::KVRefValueHash(k.clone(), v.clone(), h)));
            for f in [
                BasicMerkNode,
                SummedMerkNode(-7),
                BigSummedMerkNode(1 << 70),
            ] {
                all.push(w(Node::KVValueHashFeatureType(k.clone(), v.clone(), h, f)));
            }
            all.push(w(Node::KVDigest(k.clone(), h)));
            all.push(w(Node::Hash(h)));
            all.push(w(Node::KVHash(h)));
        }
        all.extend([Op::Parent, Op::Child, Op::ParentInverted, Op::ChildInverted]);
        for op in &all {
            let (f, b) = (encode_fork(op), encode_base(op));
            if len < 65_536 {
                assert_eq!(f, b, "len {len}: {op:?}");
            } else if carries_value(op) {
                // 3.1.0 (release) wrote `len as u16`; the fork writes a
                // large-value op that decodes back to the same op.
                assert_ne!(f, b);
                assert_eq!(&Op::decode(&f).unwrap(), op);
                let base_decoded = grovedb_merk_v310::proofs::Op::decode(&b);
                assert!(
                    base_decoded.map(|d| d != base_op(op)).unwrap_or(true),
                    "3.1.0 should not round-trip len {len}"
                );
            }
            checked += 1;
        }
    }
    println!("merk ops compared: {checked}");
}

#[test]
fn merk_verify_proof_v310_matches_v310() {
    let left = [0x11u8; 32];
    let right = [0x22u8; 32];
    let root = node_hash(&kv_hash(&[5], &[5]).unwrap(), &left, &right).unwrap();
    let honest = vec![
        Op::Push(Node::Hash(left)),
        Op::Push(Node::KV(vec![5], vec![5])),
        Op::Parent,
        Op::Push(Node::Hash(right)),
        Op::Child,
    ];
    let under_hash = vec![
        Op::Push(Node::Hash(left)),
        Op::Push(Node::KV(vec![3], b"forged".to_vec())),
        Op::Child,
        Op::Push(Node::KV(vec![5], vec![5])),
        Op::Parent,
        Op::Push(Node::Hash(right)),
        Op::Child,
    ];
    let mut cases = vec![];
    for ops in [&honest, &under_hash] {
        let bytes = encode_ops(ops);
        cases.extend(mutations(&bytes));
        cases.push(bytes);
    }
    let mut large = encode_ops(&[Op::Push(Node::KV(vec![5], vec![1; 70_000]))]);
    cases.push(large.clone());
    large.truncate(100);
    cases.push(large);
    cases.extend(garbage().into_iter().take(120));
    for keys in [vec![vec![3u8]], vec![vec![5u8]], vec![vec![3u8], vec![5]]] {
        let mut fq = grovedb_merk::proofs::Query::new();
        let mut bq = grovedb_merk_v310::proofs::Query::new();
        for k in &keys {
            fq.insert_key(k.clone());
            bq.insert_key(k.clone());
        }
        for bytes in &cases {
            for ltr in [true, false] {
                let f = fq.verify_proof_v310(bytes, None, ltr, root).unwrap();
                let b = bq.verify_proof(bytes, None, ltr, root).unwrap();
                assert_eq!(dbg(&f), dbg(&b));
                let f = fq.execute_proof_v310(bytes, Some(1), ltr).unwrap();
                let b = bq.execute_proof(bytes, Some(1), ltr).unwrap();
                assert_eq!(dbg(&f), dbg(&b));
            }
        }
    }
    let mut q = grovedb_merk::proofs::Query::new();
    q.insert_key(vec![3]);
    let forged = encode_ops(&under_hash);
    assert!(q
        .verify_proof_v310(&forged, None, true, root)
        .unwrap()
        .is_ok());
    assert!(q.verify_proof(&forged, None, true, root).unwrap().is_err());
    println!("merk cases compared: {}", cases.len());
}

// ---------------------------------------------------------------------------
// SDK known-answer fixtures
// ---------------------------------------------------------------------------

fn kat_value(len: usize) -> Vec<u8> {
    (0..len).map(|i| ((i * 7 + 3) % 256) as u8).collect()
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// Proofs from this fork's prover of a 70,000-byte item value (merk value
/// 70,007 bytes, large-value opcode 0x20) and a 65,530-byte item value (merk
/// value 65,535 bytes, the largest under 3.1.0's opcode 0x03), for the SDK
/// decoders.
/// Writes them when `SDK_FIXTURE_DIR` is set; always checks them.
#[test]
fn sdk_large_value_fixtures() {
    let p = Pair::new();
    let e: &[&[u8]] = &[];
    p.insert(e, b"apps", Element::empty_tree());
    p.insert(&[b"apps"], b"data", Element::empty_tree());
    p.insert(
        &[b"apps", b"data"],
        b"key1",
        Element::new_item(b"value-for-key1".to_vec()),
    );
    p.insert(
        &[b"apps", b"data"],
        b"key3",
        Element::new_item(b"value-for-key3".to_vec()),
    );
    p.insert(
        &[b"apps", b"data"],
        b"large",
        Element::new_item(kat_value(70_000)),
    );
    p.insert(
        &[b"apps", b"data"],
        b"small",
        Element::new_item(kat_value(65_530)),
    );
    let (root, base_root) = p.roots();
    assert_eq!(root, base_root);

    for (key, len, opcode, name) in [
        ("large", 70_000usize, 0x20u8, "large_value_item"),
        ("small", 65_530, 0x03, "small_value_item"),
    ] {
        let pq = PathQuery::new_unsized(
            vec![b"apps".to_vec(), b"data".to_vec()],
            Query::new_single_key(key.as_bytes().to_vec()),
        );
        let proof = p.fork.prove_query(&pq, None, fv()).unwrap().unwrap();
        let (r, rows) = GroveDb::verify_query(&proof, &pq, fv()).unwrap();
        assert_eq!(r, root);
        let element_bytes = rows[0].2.as_ref().unwrap().serialize(fv()).unwrap();
        assert_eq!(rows[0].2, Some(Element::new_item(kat_value(len))));
        let leaf = &decode_proof(&proof).root_layer.lower_layers[b"apps".as_slice()].lower_layers
            [b"data".as_slice()];
        // the op carrying the item: opcode, key, then the value length
        let needle = {
            let mut n = vec![opcode, key.len() as u8];
            n.extend_from_slice(key.as_bytes());
            if opcode == 0x20 {
                n.extend_from_slice(&(element_bytes.len() as u32).to_be_bytes());
            } else {
                n.extend_from_slice(&(element_bytes.len() as u16).to_be_bytes());
            }
            n
        };
        assert!(
            leaf.merk_proof
                .windows(needle.len())
                .any(|w| w == needle.as_slice()),
            "{name}: expected opcode {opcode:#x}"
        );
        if element_bytes.len() < 65_536 {
            let base_proof = p
                .base
                .prove_query(&base_query(&pq), None, bv())
                .unwrap()
                .unwrap();
            assert_eq!(base_proof, proof);
        }
        if let Ok(dir) = std::env::var("SDK_FIXTURE_DIR") {
            let json = format!(
                "{{\n  \"kind\": \"single_key\",\n  \"description\": \"Single-key proof of a \
                 {len}-byte Item value (serialized element {elen} bytes) in ['apps','data'], with \
                 siblings key1 and key3. The item's merk op is opcode {opcode:#04x} \
                 ({kind}).\",\n  \"generator\": \"willow-network/grovedb \
                 willow/v3.1.0-proof-fixes, v310-compat/tests/differential.rs \
                 sdk_large_value_fixtures\",\n  \"path\": [\"apps\", \"data\"],\n  \"key\": \
                 \"{key}\",\n  \"value_len\": {len},\n  \"value_formula\": \"value[i] = (i * 7 + \
                 3) mod 256\",\n  \"element_len\": {elen},\n  \"item_opcode\": {opcode},\n  \
                 \"proof_hex\": \"{}\",\n  \"expected_root_hex\": \"{}\"\n}}\n",
                hex(&proof),
                hex(&root),
                elen = element_bytes.len(),
                kind = if opcode == 0x20 {
                    "large-value KV, u32 length"
                } else {
                    "3.1.0 KV, u16 length"
                },
            );
            std::fs::write(format!("{dir}/{name}.json"), json).unwrap();
        }
    }
}

// ---------------------------------------------------------------------------
// Nesting depth
// ---------------------------------------------------------------------------

fn nested_envelope(depth: usize) -> Vec<u8> {
    let mut proof = vec![0x00, 0x00, 0x01];
    for _ in 1..depth {
        proof.extend_from_slice(&[0x00, 0x00, 0x01]);
    }
    proof.extend_from_slice(&[0x00, 0x00, 0x00, 0x00]);
    proof
}

fn on_stack<T: Send + 'static>(bytes: usize, f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(bytes)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// Up to the `_v310` depth limit (4,400; 3.1.0 aborts from 4,355 on a fresh
/// 2 MiB thread) the fork verifies exactly as 3.1.0, both on a stack big
/// enough for 3.1.0's recursion; one deeper, the fork refuses without
/// recursing (on a 256 KiB stack).
#[test]
fn deep_nesting_v310_matches_v310_up_to_its_limit() {
    use grovedb::operations::proof::{
        envelope_depth_within, MAX_STRICT_PROOF_DEPTH, MAX_V310_PROOF_DEPTH,
    };
    for depth in [1, 2, 63, 64, 65, 1_000, 3_001, 4_354, MAX_V310_PROOF_DEPTH] {
        let (fork, base) = on_stack(256 << 20, move || {
            let proof = nested_envelope(depth);
            let mut keys = Query::new();
            keys.insert_key(b"k".to_vec());
            let pq = PathQuery::new(vec![], SizedQuery::new(keys, Some(3), None));
            let bpq = base_query(&pq);
            (
                [
                    dbg(&GroveDb::verify_query_v310(&proof, &pq, fv())),
                    dbg(&GroveDb::verify_query_raw_v310(&proof, &pq, fv())),
                ],
                [
                    dbg(&grovedb_v310::GroveDb::verify_query(&proof, &bpq, bv())),
                    dbg(&grovedb_v310::GroveDb::verify_query_raw(&proof, &bpq, bv())),
                ],
            )
        });
        assert_eq!(fork, base, "depth {depth}");
        assert!(envelope_depth_within(&nested_envelope(depth), depth));
    }
    let refused = on_stack(256 << 10, || {
        let pq = PathQuery::new_unsized(vec![], Query::new_single_key(b"k".to_vec()));
        let legacy = nested_envelope(MAX_V310_PROOF_DEPTH + 1);
        let strict = nested_envelope(MAX_STRICT_PROOF_DEPTH + 1);
        [
            dbg(&GroveDb::verify_query_v310(&legacy, &pq, fv())),
            dbg(&GroveDb::verify_query_raw_v310(&legacy, &pq, fv())),
            dbg(&GroveDb::verify_query(&strict, &pq, fv())),
            dbg(&GroveDb::verify_query_raw(&strict, &pq, fv())),
        ]
    });
    for r in refused {
        assert!(r.contains("nest more than"), "{r}");
    }
}
