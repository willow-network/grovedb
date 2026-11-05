//! Proofs encoding
//!
//! A value shorter than [`LARGE_VALUE_THRESHOLD`] (64 KiB) is written with the
//! 3.1.0 opcodes (0x03..=0x0e), whose value length is a big-endian `u16`. A
//! longer value is written with the large-value opcodes, which carry a
//! big-endian `u32` length and otherwise mirror the opcode they replace:
//!
//! | small | large | node                                  |
//! |-------|-------|---------------------------------------|
//! | 0x03  | 0x20  | `Push(KV)`                            |
//! | 0x04  | 0x21  | `Push(KVValueHash)`                   |
//! | 0x06  | 0x22  | `Push(KVRefValueHash)`                |
//! | 0x07  | 0x23  | `Push(KVValueHashFeatureType)`        |
//! | 0x0a  | 0x28  | `PushInverted(KV)`                    |
//! | 0x0b  | 0x29  | `PushInverted(KVValueHash)`           |
//! | 0x0d  | 0x2a  | `PushInverted(KVRefValueHash)`        |
//! | 0x0e  | 0x2b  | `PushInverted(KVValueHashFeatureType)`|
//!
//! These are the opcodes upstream GroveDB assigned (dashpay/grovedb
//! `86562f65`). grovedb-merk 3.1.0 instead wrote `value.len() as u16`, which
//! silently truncates the length of any value of 64 KiB or more, so a proof
//! of such a value could not be decoded. Every op whose value is shorter than
//! 64 KiB encodes byte-identically to 3.1.0.
//!
//! The decoder accepts a large-value opcode only under
//! [`ProofRules::Strict`], only with a length of at least
//! [`LARGE_VALUE_THRESHOLD`] (one encoding per op) and at most
//! [`MAX_VALUE_LEN`]. Under [`ProofRules::V310`] the large-value opcodes are
//! unknown, exactly as in 3.1.0.

#[cfg(any(feature = "minimal", feature = "verify"))]
use std::io::{Read, Write};

#[cfg(feature = "minimal")]
use ed::Terminated;
#[cfg(any(feature = "minimal", feature = "verify"))]
use ed::{Decode, Encode, Error as EdError};

#[cfg(any(feature = "minimal", feature = "verify"))]
use super::{Node, Op, ProofRules};
#[cfg(any(feature = "minimal", feature = "verify"))]
use crate::{error::Error, tree::HASH_LENGTH, TreeFeatureType};

/// A value of this many bytes or more is encoded with a large-value opcode
/// (`u32` length) instead of the 3.1.0 opcode (`u16` length).
#[cfg(any(feature = "minimal", feature = "verify"))]
pub const LARGE_VALUE_THRESHOLD: usize = 65_536;

/// Longest value a large-value opcode may declare (64 MiB, as upstream). Caps
/// what a malicious proof can make the decoder read.
#[cfg(any(feature = "minimal", feature = "verify"))]
pub const MAX_VALUE_LEN: u32 = 64 * 1024 * 1024;

/// Writes `[opcode, key_len, key, value_len, value]`, choosing the 3.1.0
/// opcode and a `u16` length below [`LARGE_VALUE_THRESHOLD`], else the
/// large-value opcode and a `u32` length.
#[cfg(any(feature = "minimal", feature = "verify"))]
fn encode_key_value<W: Write>(
    dest: &mut W,
    small_opcode: u8,
    large_opcode: u8,
    key: &[u8],
    value: &[u8],
) -> ed::Result<()> {
    debug_assert!(key.len() < 256);
    if value.len() < LARGE_VALUE_THRESHOLD {
        dest.write_all(&[small_opcode, key.len() as u8])?;
        dest.write_all(key)?;
        (value.len() as u16).encode_into(dest)?;
    } else {
        debug_assert!(value.len() <= u32::MAX as usize);
        dest.write_all(&[large_opcode, key.len() as u8])?;
        dest.write_all(key)?;
        (value.len() as u32).encode_into(dest)?;
    }
    dest.write_all(value)?;
    Ok(())
}

/// Length of the `[opcode, key_len, key, value_len, value]` prefix that
/// [`encode_key_value`] writes.
#[cfg(any(feature = "minimal", feature = "verify"))]
const fn key_value_encoding_length(key: &[u8], value: &[u8]) -> usize {
    let header = if value.len() < LARGE_VALUE_THRESHOLD {
        4
    } else {
        6
    };
    header + key.len() + value.len()
}

/// Reads the key and the `u32`-length value of a large-value op. Refuses a
/// length below [`LARGE_VALUE_THRESHOLD`] (that value has a 3.1.0 encoding,
/// and the decoder's offset arithmetic assumes the canonical one) or above
/// [`MAX_VALUE_LEN`]. Reads through `take` so a lying length cannot make the
/// decoder allocate more than the input holds.
#[cfg(any(feature = "minimal", feature = "verify"))]
fn decode_large_key_value<R: Read>(input: &mut R, opcode: u8) -> ed::Result<(Vec<u8>, Vec<u8>)> {
    let key_len: u8 = Decode::decode(&mut *input)?;
    let mut key = vec![0; key_len as usize];
    input.read_exact(key.as_mut_slice())?;

    let value_len: u32 = Decode::decode(&mut *input)?;
    if (value_len as usize) < LARGE_VALUE_THRESHOLD || value_len > MAX_VALUE_LEN {
        return Err(EdError::UnexpectedByte(opcode));
    }
    let mut value = Vec::new();
    (&mut *input)
        .take(value_len as u64)
        .read_to_end(&mut value)?;
    if value.len() != value_len as usize {
        return Err(EdError::IOError(std::io::Error::new(
            std::io::ErrorKind::UnexpectedEof,
            "failed to fill whole buffer",
        )));
    }
    Ok((key, value))
}

#[cfg(any(feature = "minimal", feature = "verify"))]
impl Encode for Op {
    fn encode_into<W: Write>(&self, dest: &mut W) -> ed::Result<()> {
        match self {
            // Push
            Op::Push(Node::Hash(hash)) => {
                dest.write_all(&[0x01])?;
                dest.write_all(hash)?;
            }
            Op::Push(Node::KVHash(kv_hash)) => {
                dest.write_all(&[0x02])?;
                dest.write_all(kv_hash)?;
            }
            Op::Push(Node::KV(key, value)) => {
                encode_key_value(dest, 0x03, 0x20, key, value)?;
            }
            Op::Push(Node::KVValueHash(key, value, value_hash)) => {
                encode_key_value(dest, 0x04, 0x21, key, value)?;
                dest.write_all(value_hash)?;
            }
            Op::Push(Node::KVDigest(key, value_hash)) => {
                debug_assert!(key.len() < 256);

                dest.write_all(&[0x05, key.len() as u8])?;
                dest.write_all(key)?;
                dest.write_all(value_hash)?;
            }
            Op::Push(Node::KVRefValueHash(key, value, value_hash)) => {
                encode_key_value(dest, 0x06, 0x22, key, value)?;
                dest.write_all(value_hash)?;
            }
            Op::Push(Node::KVValueHashFeatureType(key, value, value_hash, feature_type)) => {
                encode_key_value(dest, 0x07, 0x23, key, value)?;
                dest.write_all(value_hash)?;
                feature_type.encode_into(dest)?;
            }

            // PushInverted
            Op::PushInverted(Node::Hash(hash)) => {
                dest.write_all(&[0x08])?;
                dest.write_all(hash)?;
            }
            Op::PushInverted(Node::KVHash(kv_hash)) => {
                dest.write_all(&[0x09])?;
                dest.write_all(kv_hash)?;
            }
            Op::PushInverted(Node::KV(key, value)) => {
                encode_key_value(dest, 0x0a, 0x28, key, value)?;
            }
            Op::PushInverted(Node::KVValueHash(key, value, value_hash)) => {
                encode_key_value(dest, 0x0b, 0x29, key, value)?;
                dest.write_all(value_hash)?;
            }
            Op::PushInverted(Node::KVDigest(key, value_hash)) => {
                debug_assert!(key.len() < 256);

                dest.write_all(&[0x0c, key.len() as u8])?;
                dest.write_all(key)?;
                dest.write_all(value_hash)?;
            }
            Op::PushInverted(Node::KVRefValueHash(key, value, value_hash)) => {
                encode_key_value(dest, 0x0d, 0x2a, key, value)?;
                dest.write_all(value_hash)?;
            }
            Op::PushInverted(Node::KVValueHashFeatureType(
                key,
                value,
                value_hash,
                feature_type,
            )) => {
                encode_key_value(dest, 0x0e, 0x2b, key, value)?;
                dest.write_all(value_hash)?;
                feature_type.encode_into(dest)?;
            }

            Op::Parent => dest.write_all(&[0x10])?,
            Op::Child => dest.write_all(&[0x11])?,
            Op::ParentInverted => dest.write_all(&[0x12])?,
            Op::ChildInverted => dest.write_all(&[0x13])?,
        };
        Ok(())
    }

    fn encoding_length(&self) -> ed::Result<usize> {
        Ok(match self {
            Op::Push(Node::Hash(_)) => 1 + HASH_LENGTH,
            Op::Push(Node::KVHash(_)) => 1 + HASH_LENGTH,
            Op::Push(Node::KVDigest(key, _)) => 2 + key.len() + HASH_LENGTH,
            Op::Push(Node::KV(key, value)) => key_value_encoding_length(key, value),
            Op::Push(Node::KVValueHash(key, value, _)) => {
                key_value_encoding_length(key, value) + HASH_LENGTH
            }
            Op::Push(Node::KVRefValueHash(key, value, _)) => {
                key_value_encoding_length(key, value) + HASH_LENGTH
            }
            Op::Push(Node::KVValueHashFeatureType(key, value, _, feature_type)) => {
                key_value_encoding_length(key, value)
                    + HASH_LENGTH
                    + feature_type.encoding_length()?
            }
            Op::PushInverted(Node::Hash(_)) => 1 + HASH_LENGTH,
            Op::PushInverted(Node::KVHash(_)) => 1 + HASH_LENGTH,
            Op::PushInverted(Node::KVDigest(key, _)) => 2 + key.len() + HASH_LENGTH,
            Op::PushInverted(Node::KV(key, value)) => key_value_encoding_length(key, value),
            Op::PushInverted(Node::KVValueHash(key, value, _)) => {
                key_value_encoding_length(key, value) + HASH_LENGTH
            }
            Op::PushInverted(Node::KVRefValueHash(key, value, _)) => {
                key_value_encoding_length(key, value) + HASH_LENGTH
            }
            Op::PushInverted(Node::KVValueHashFeatureType(key, value, _, feature_type)) => {
                key_value_encoding_length(key, value)
                    + HASH_LENGTH
                    + feature_type.encoding_length()?
            }
            Op::Parent => 1,
            Op::Child => 1,
            Op::ParentInverted => 1,
            Op::ChildInverted => 1,
        })
    }
}

/// Decodes one op. The arms for 0x01..=0x13 are grovedb-merk 3.1.0's,
/// unchanged; the large-value arms exist only under [`ProofRules::Strict`].
#[cfg(any(feature = "minimal", feature = "verify"))]
fn decode_op<R: Read>(mut input: R, rules: ProofRules) -> ed::Result<Op> {
    let variant: u8 = Decode::decode(&mut input)?;

    Ok(match variant {
        0x01 => {
            let mut hash = [0; HASH_LENGTH];
            input.read_exact(&mut hash)?;
            Op::Push(Node::Hash(hash))
        }
        0x02 => {
            let mut hash = [0; HASH_LENGTH];
            input.read_exact(&mut hash)?;
            Op::Push(Node::KVHash(hash))
        }
        0x03 => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            Op::Push(Node::KV(key, value))
        }
        0x04 => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::Push(Node::KVValueHash(key, value, value_hash))
        }
        0x05 => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::Push(Node::KVDigest(key, value_hash))
        }
        0x06 => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::Push(Node::KVRefValueHash(key, value, value_hash))
        }
        0x07 => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            let tree_feature_type = TreeFeatureType::decode(input)?;
            Op::Push(Node::KVValueHashFeatureType(
                key,
                value,
                value_hash,
                tree_feature_type,
            ))
        }
        0x08 => {
            let mut hash = [0; HASH_LENGTH];
            input.read_exact(&mut hash)?;
            Op::PushInverted(Node::Hash(hash))
        }
        0x09 => {
            let mut hash = [0; HASH_LENGTH];
            input.read_exact(&mut hash)?;
            Op::PushInverted(Node::KVHash(hash))
        }
        0x0a => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            Op::PushInverted(Node::KV(key, value))
        }
        0x0b => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::PushInverted(Node::KVValueHash(key, value, value_hash))
        }
        0x0c => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::PushInverted(Node::KVDigest(key, value_hash))
        }
        0x0d => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            Op::PushInverted(Node::KVRefValueHash(key, value, value_hash))
        }
        0x0e => {
            let key_len: u8 = Decode::decode(&mut input)?;
            let mut key = vec![0; key_len as usize];
            input.read_exact(key.as_mut_slice())?;

            let value_len: u16 = Decode::decode(&mut input)?;
            let mut value = vec![0; value_len as usize];
            input.read_exact(value.as_mut_slice())?;

            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;

            let tree_feature_type = TreeFeatureType::decode(input)?;
            Op::PushInverted(Node::KVValueHashFeatureType(
                key,
                value,
                value_hash,
                tree_feature_type,
            ))
        }
        // Large-value opcodes: same layout as the opcode they mirror, but the
        // value length is a big-endian u32. Not part of the 3.1.0 format, so
        // under `ProofRules::V310` they fall through to the unknown-opcode arm.
        0x20 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            Op::Push(Node::KV(key, value))
        }
        0x21 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            Op::Push(Node::KVValueHash(key, value, value_hash))
        }
        0x22 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            Op::Push(Node::KVRefValueHash(key, value, value_hash))
        }
        0x23 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            let tree_feature_type = TreeFeatureType::decode(input)?;
            Op::Push(Node::KVValueHashFeatureType(
                key,
                value,
                value_hash,
                tree_feature_type,
            ))
        }
        0x28 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            Op::PushInverted(Node::KV(key, value))
        }
        0x29 if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            Op::PushInverted(Node::KVValueHash(key, value, value_hash))
        }
        0x2a if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            Op::PushInverted(Node::KVRefValueHash(key, value, value_hash))
        }
        0x2b if rules.large_value_ops() => {
            let (key, value) = decode_large_key_value(&mut input, variant)?;
            let mut value_hash = [0; HASH_LENGTH];
            input.read_exact(&mut value_hash)?;
            let tree_feature_type = TreeFeatureType::decode(input)?;
            Op::PushInverted(Node::KVValueHashFeatureType(
                key,
                value,
                value_hash,
                tree_feature_type,
            ))
        }
        0x10 => Op::Parent,
        0x11 => Op::Child,
        0x12 => Op::ParentInverted,
        0x13 => Op::ChildInverted,
        // TODO: Remove dependency on ed and throw an internal error
        _ => return Err(ed::Error::UnexpectedByte(variant)),
    })
}

#[cfg(any(feature = "minimal", feature = "verify"))]
impl Decode for Op {
    /// Decodes under [`ProofRules::Strict`].
    fn decode<R: Read>(input: R) -> ed::Result<Self> {
        decode_op(input, ProofRules::Strict)
    }
}

#[cfg(feature = "minimal")]
impl Terminated for Op {}

impl Op {
    #[cfg(feature = "minimal")]
    fn encode_into<W: Write>(&self, dest: &mut W) -> Result<(), Error> {
        Encode::encode_into(self, dest).map_err(|e| match e {
            EdError::UnexpectedByte(byte) => Error::ProofCreationError(format!(
                "failed to encode an proofs::Op structure (UnexpectedByte: {byte})"
            )),
            EdError::IOError(error) => Error::ProofCreationError(format!(
                "failed to encode an proofs::Op structure ({error})"
            )),
        })
    }

    #[cfg(any(feature = "minimal", feature = "verify"))]
    fn encoding_length(&self) -> usize {
        Encode::encoding_length(self).unwrap()
    }

    #[cfg(any(feature = "minimal", feature = "verify"))]
    /// Decode under [`ProofRules::Strict`] (accepts the large-value opcodes).
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        Self::decode_with_rules(bytes, ProofRules::Strict)
    }

    #[cfg(any(feature = "minimal", feature = "verify"))]
    /// Decode exactly as grovedb-merk 3.1.0 did: a large-value opcode is an
    /// unknown opcode.
    pub fn decode_v310(bytes: &[u8]) -> Result<Self, Error> {
        Self::decode_with_rules(bytes, ProofRules::V310)
    }

    #[cfg(any(feature = "minimal", feature = "verify"))]
    /// Decode under the given rules.
    pub fn decode_with_rules(bytes: &[u8], rules: ProofRules) -> Result<Self, Error> {
        decode_op(bytes, rules).map_err(|e| match e {
            EdError::UnexpectedByte(byte) => Error::ProofCreationError(format!(
                "failed to decode an proofs::Op structure (UnexpectedByte: {byte})"
            )),
            EdError::IOError(error) => Error::ProofCreationError(format!(
                "failed to decode an proofs::Op structure ({error})"
            )),
        })
    }
}

#[cfg(feature = "minimal")]
/// Encode into
pub fn encode_into<'a, T: Iterator<Item = &'a Op>>(ops: T, output: &mut Vec<u8>) {
    for op in ops {
        op.encode_into(output).unwrap();
    }
}

#[cfg(any(feature = "minimal", feature = "verify"))]
/// Decoder
pub struct Decoder<'a> {
    offset: usize,
    bytes: &'a [u8],
    rules: ProofRules,
    failed: bool,
}

#[cfg(any(feature = "minimal", feature = "verify"))]
impl<'a> Decoder<'a> {
    /// New decoder under [`ProofRules::Strict`].
    pub const fn new(proof_bytes: &'a [u8]) -> Self {
        Self::with_rules(proof_bytes, ProofRules::Strict)
    }

    /// New decoder that decodes exactly as grovedb-merk 3.1.0's did.
    pub const fn new_v310(proof_bytes: &'a [u8]) -> Self {
        Self::with_rules(proof_bytes, ProofRules::V310)
    }

    /// New decoder under the given rules.
    pub const fn with_rules(proof_bytes: &'a [u8], rules: ProofRules) -> Self {
        Decoder {
            offset: 0,
            bytes: proof_bytes,
            rules,
            failed: false,
        }
    }
}

#[cfg(any(feature = "minimal", feature = "verify"))]
impl Iterator for Decoder<'_> {
    type Item = Result<Op, Error>;

    /// Under [`ProofRules::Strict`] the first decoding error ends the
    /// iteration. Under [`ProofRules::V310`] the decoder keeps yielding the
    /// same error, as 3.1.0's did.
    fn next(&mut self) -> Option<Self::Item> {
        if self.failed || self.offset >= self.bytes.len() {
            return None;
        }

        let result = (|| {
            let bytes = &self.bytes[self.offset..];
            let op = Op::decode_with_rules(bytes, self.rules)?;
            self.offset += op.encoding_length();
            Ok(op)
        })();
        if result.is_err() && self.rules == ProofRules::Strict {
            self.failed = true;
        }
        Some(result)
    }
}

#[cfg(feature = "minimal")]
#[cfg(test)]
mod test {
    use super::super::{Node, Op};
    use crate::{
        proofs::Decoder,
        tree::HASH_LENGTH,
        TreeFeatureType::{BasicMerkNode, SummedMerkNode},
    };

    #[test]
    fn encode_push_hash() {
        let op = Op::Push(Node::Hash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x01, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123
            ]
        );
    }

    #[test]
    fn encode_push_kvhash() {
        let op = Op::Push(Node::KVHash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x02, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123
            ]
        );
    }

    #[test]
    fn encode_push_kvdigest() {
        let op = Op::Push(Node::KVDigest(vec![1, 2, 3], [123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 5 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x05, 3, 1, 2, 3, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123
            ]
        );
    }

    #[test]
    fn encode_push_kv() {
        let op = Op::Push(Node::KV(vec![1, 2, 3], vec![4, 5, 6]));
        assert_eq!(op.encoding_length(), 10);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x03, 3, 1, 2, 3, 0, 3, 4, 5, 6]);
    }

    #[test]
    fn encode_push_kvvaluehash() {
        let op = Op::Push(Node::KVValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]));
        assert_eq!(op.encoding_length(), 42);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x04, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        )
    }

    #[test]
    fn encode_push_kvvaluerefhash() {
        let op = Op::Push(Node::KVRefValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]));
        assert_eq!(op.encoding_length(), 42);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x06, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        )
    }

    #[test]
    fn encode_push_kvvalue_hash_feature_type() {
        let op = Op::Push(Node::KVValueHashFeatureType(
            vec![1, 2, 3],
            vec![4, 5, 6],
            [0; 32],
            BasicMerkNode,
        ));
        assert_eq!(op.encoding_length(), 43);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x07, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        );

        let op = Op::Push(Node::KVValueHashFeatureType(
            vec![1, 2, 3],
            vec![4, 5, 6],
            [0; 32],
            SummedMerkNode(6),
        ));
        assert_eq!(op.encoding_length(), 44);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x07, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12
            ]
        )
    }

    #[test]
    fn encode_push_inverted_hash() {
        let op = Op::PushInverted(Node::Hash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x08, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123
            ]
        );
    }

    #[test]
    fn encode_push_inverted_kvhash() {
        let op = Op::PushInverted(Node::KVHash([123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 1 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x09, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123
            ]
        );
    }

    #[test]
    fn encode_push_inverted_kvdigest() {
        let op = Op::PushInverted(Node::KVDigest(vec![1, 2, 3], [123; HASH_LENGTH]));
        assert_eq!(op.encoding_length(), 5 + HASH_LENGTH);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x0c, 3, 1, 2, 3, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
                123, 123, 123
            ]
        );
    }

    #[test]
    fn encode_push_inverted_kv() {
        let op = Op::PushInverted(Node::KV(vec![1, 2, 3], vec![4, 5, 6]));
        assert_eq!(op.encoding_length(), 10);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x0a, 3, 1, 2, 3, 0, 3, 4, 5, 6]);
    }

    #[test]
    fn encode_push_inverted_kvvaluehash() {
        let op = Op::PushInverted(Node::KVValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]));
        assert_eq!(op.encoding_length(), 42);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x0b, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        )
    }

    #[test]
    fn encode_push_inverted_kvvalue_hash_feature_type() {
        let op = Op::PushInverted(Node::KVValueHashFeatureType(
            vec![1, 2, 3],
            vec![4, 5, 6],
            [0; 32],
            BasicMerkNode,
        ));
        assert_eq!(op.encoding_length(), 43);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x0e, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        );

        let op = Op::PushInverted(Node::KVValueHashFeatureType(
            vec![1, 2, 3],
            vec![4, 5, 6],
            [0; 32],
            SummedMerkNode(5),
        ));
        assert_eq!(op.encoding_length(), 44);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x0e, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10
            ]
        );
    }

    #[test]
    fn encode_push_inverted_kvvaluerefhash() {
        let op = Op::PushInverted(Node::KVRefValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]));
        assert_eq!(op.encoding_length(), 42);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(
            bytes,
            vec![
                0x0d, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            ]
        )
    }

    #[test]
    fn encode_parent() {
        let op = Op::Parent;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x10]);
    }

    #[test]
    fn encode_child() {
        let op = Op::Child;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x11]);
    }

    #[test]
    fn encode_parent_inverted() {
        let op = Op::ParentInverted;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x12]);
    }

    #[test]
    fn encode_child_inverted() {
        let op = Op::ChildInverted;
        assert_eq!(op.encoding_length(), 1);

        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        assert_eq!(bytes, vec![0x13]);
    }

    #[test]
    #[should_panic]
    fn encode_push_kv_long_key() {
        let op = Op::Push(Node::KV(vec![123; 300], vec![4, 5, 6]));
        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
    }

    #[test]
    fn decode_push_hash() {
        let bytes = [
            0x01, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::Hash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_kvhash() {
        let bytes = [
            0x02, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::KVHash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_kvdigest() {
        let bytes = [
            0x05, 3, 1, 2, 3, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::Push(Node::KVDigest(vec![1, 2, 3], [123; HASH_LENGTH]))
        );
    }

    #[test]
    fn decode_push_kv() {
        let bytes = [0x03, 3, 1, 2, 3, 0, 3, 4, 5, 6];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Push(Node::KV(vec![1, 2, 3], vec![4, 5, 6])));
    }

    #[test]
    fn decode_push_kvvaluehash() {
        let bytes = [
            0x04, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::Push(Node::KVValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]))
        );
    }

    #[test]
    fn decode_push_kvvaluerefhash() {
        let bytes = [
            0x06, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::Push(Node::KVRefValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]))
        );
    }

    #[test]
    fn decode_push_kvvalue_hash_feature_type() {
        let bytes = [
            0x07, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::Push(Node::KVValueHashFeatureType(
                vec![1, 2, 3],
                vec![4, 5, 6],
                [0; 32],
                BasicMerkNode
            ))
        );

        let bytes = [
            0x07, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::Push(Node::KVValueHashFeatureType(
                vec![1, 2, 3],
                vec![4, 5, 6],
                [0; 32],
                SummedMerkNode(6)
            ))
        );
    }

    #[test]
    fn decode_push_inverted_hash() {
        let bytes = [
            0x08, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::PushInverted(Node::Hash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_inverted_kvhash() {
        let bytes = [
            0x09, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::PushInverted(Node::KVHash([123; HASH_LENGTH])));
    }

    #[test]
    fn decode_push_inverted_kvdigest() {
        let bytes = [
            0x0c, 3, 1, 2, 3, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123, 123,
            123,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::PushInverted(Node::KVDigest(vec![1, 2, 3], [123; HASH_LENGTH]))
        );
    }

    #[test]
    fn decode_push_inverted_kv() {
        let bytes = [0x0a, 3, 1, 2, 3, 0, 3, 4, 5, 6];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::PushInverted(Node::KV(vec![1, 2, 3], vec![4, 5, 6])));
    }

    #[test]
    fn decode_push_inverted_kvvaluehash() {
        let bytes = [
            0x0b, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::PushInverted(Node::KVValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]))
        );
    }

    #[test]
    fn decode_push_inverted_kvvaluerefhash() {
        let bytes = [
            0x0d, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::PushInverted(Node::KVRefValueHash(vec![1, 2, 3], vec![4, 5, 6], [0; 32]))
        );
    }

    #[test]
    fn decode_push_inverted_kvvalue_hash_feature_type() {
        let bytes = [
            0x0e, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::PushInverted(Node::KVValueHashFeatureType(
                vec![1, 2, 3],
                vec![4, 5, 6],
                [0; 32],
                BasicMerkNode
            ))
        );

        let bytes = [
            0x0e, 3, 1, 2, 3, 0, 3, 4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 12,
        ];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(
            op,
            Op::PushInverted(Node::KVValueHashFeatureType(
                vec![1, 2, 3],
                vec![4, 5, 6],
                [0; 32],
                SummedMerkNode(6)
            ))
        );
    }

    #[test]
    fn decode_parent() {
        let bytes = [0x10];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Parent);
    }

    #[test]
    fn decode_child() {
        let bytes = [0x11];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::Child);
    }

    #[test]
    fn decode_multiple_child() {
        let bytes = [0x11, 0x11, 0x11, 0x10];
        let decoder = Decoder::new(&bytes);

        let mut vecop = vec![];
        for op in decoder {
            match op {
                Ok(op) => vecop.push(op),
                Err(e) => eprintln!("Error decoding: {:?}", e),
            }
        }
        assert_eq!(vecop, vec![Op::Child, Op::Child, Op::Child, Op::Parent]);
    }

    #[test]
    fn decode_parent_inverted() {
        let bytes = [0x12];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::ParentInverted);
    }

    #[test]
    fn decode_child_inverted() {
        let bytes = [0x13];
        let op = Op::decode(&bytes[..]).expect("decode failed");
        assert_eq!(op, Op::ChildInverted);
    }

    #[test]
    fn decode_unknown() {
        let bytes = [0x88];
        assert!(Op::decode(&bytes[..]).is_err());
    }

    // ---------------------------------------------------------------------
    // Large-value opcodes (backport of dashpay/grovedb 86562f65)
    // ---------------------------------------------------------------------

    use super::{LARGE_VALUE_THRESHOLD, MAX_VALUE_LEN};
    use crate::proofs::ProofRules;

    /// Every node that carries a value, each pushed both ways, with the
    /// (3.1.0 opcode, large-value opcode) pair it encodes under.
    fn value_carrying_ops(key: Vec<u8>, value: Vec<u8>) -> Vec<(Op, u8, u8)> {
        let vh = [7u8; HASH_LENGTH];
        let mut out = vec![];
        for inverted in [false, true] {
            let wrap = |node: Node| {
                if inverted {
                    Op::PushInverted(node)
                } else {
                    Op::Push(node)
                }
            };
            let (kv, kvvh, kvref, kvft) = if inverted {
                (0x0a, 0x0b, 0x0d, 0x0e)
            } else {
                (0x03, 0x04, 0x06, 0x07)
            };
            let large = |small: u8| -> u8 {
                match small {
                    0x03 => 0x20,
                    0x04 => 0x21,
                    0x06 => 0x22,
                    0x07 => 0x23,
                    0x0a => 0x28,
                    0x0b => 0x29,
                    0x0d => 0x2a,
                    0x0e => 0x2b,
                    _ => unreachable!(),
                }
            };
            out.push((wrap(Node::KV(key.clone(), value.clone())), kv, large(kv)));
            out.push((
                wrap(Node::KVValueHash(key.clone(), value.clone(), vh)),
                kvvh,
                large(kvvh),
            ));
            out.push((
                wrap(Node::KVRefValueHash(key.clone(), value.clone(), vh)),
                kvref,
                large(kvref),
            ));
            out.push((
                wrap(Node::KVValueHashFeatureType(
                    key.clone(),
                    value.clone(),
                    vh,
                    SummedMerkNode(-5),
                )),
                kvft,
                large(kvft),
            ));
        }
        out
    }

    /// The bytes 3.1.0 wrote for a value-carrying op (u16 length), built by
    /// hand: `[opcode, key_len, key, u16 BE len, value, tail]`.
    fn v310_layout(opcode: u8, key: &[u8], value: &[u8], op: &Op) -> Vec<u8> {
        let mut b = vec![opcode, key.len() as u8];
        b.extend_from_slice(key);
        b.extend_from_slice(&(value.len() as u16).to_be_bytes());
        b.extend_from_slice(value);
        b.extend_from_slice(&tail_after_value(op));
        b
    }

    fn large_layout(opcode: u8, key: &[u8], value: &[u8], op: &Op) -> Vec<u8> {
        let mut b = vec![opcode, key.len() as u8];
        b.extend_from_slice(key);
        b.extend_from_slice(&(value.len() as u32).to_be_bytes());
        b.extend_from_slice(value);
        b.extend_from_slice(&tail_after_value(op));
        b
    }

    fn tail_after_value(op: &Op) -> Vec<u8> {
        let node = match op {
            Op::Push(n) | Op::PushInverted(n) => n,
            _ => unreachable!(),
        };
        let mut t = vec![];
        match node {
            Node::KV(..) => {}
            Node::KVValueHash(_, _, vh) | Node::KVRefValueHash(_, _, vh) => t.extend_from_slice(vh),
            Node::KVValueHashFeatureType(_, _, vh, ft) => {
                t.extend_from_slice(vh);
                ed::Encode::encode_into(ft, &mut t).unwrap();
            }
            _ => unreachable!(),
        }
        t
    }

    #[test]
    fn values_below_64k_keep_the_v310_encoding() {
        for len in [0usize, 1, 255, 256, 65_534, LARGE_VALUE_THRESHOLD - 1] {
            let key = vec![9u8; 32];
            let value: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
            for (op, small, _) in value_carrying_ops(key.clone(), value.clone()) {
                let mut bytes = vec![];
                op.encode_into(&mut bytes).unwrap();
                assert_eq!(bytes, v310_layout(small, &key, &value, &op), "len {len}");
                assert_eq!(op.encoding_length(), bytes.len());
                // decodes identically under both rule sets
                assert_eq!(Op::decode(&bytes).unwrap(), op);
                assert_eq!(Op::decode_v310(&bytes).unwrap(), op);
            }
        }
    }

    #[test]
    fn values_of_64k_or_more_use_the_large_value_opcodes() {
        for len in [
            LARGE_VALUE_THRESHOLD,
            LARGE_VALUE_THRESHOLD + 1,
            512 * 1024,
            1 << 20,
        ] {
            let key = vec![1u8, 2, 3];
            let value: Vec<u8> = (0..len).map(|i| (i % 253) as u8).collect();
            for (op, _, large) in value_carrying_ops(key.clone(), value.clone()) {
                let mut bytes = vec![];
                op.encode_into(&mut bytes).unwrap();
                assert_eq!(bytes, large_layout(large, &key, &value, &op), "len {len}");
                assert_eq!(op.encoding_length(), bytes.len());
                assert_eq!(Op::decode(&bytes).unwrap(), op);
                // 3.1.0 has no such opcode
                let err = Op::decode_v310(&bytes).unwrap_err();
                assert_eq!(
                    err.to_string(),
                    format!(
                        "proof creation error failed to decode an proofs::Op structure \
                         (UnexpectedByte: {large})"
                    )
                );
            }
        }
    }

    #[test]
    fn decoder_walks_mixed_small_and_large_ops() {
        let big = vec![0xab; LARGE_VALUE_THRESHOLD + 10];
        let ops = vec![
            Op::Push(Node::KV(vec![1], vec![1; 10])),
            Op::Push(Node::KVValueHash(vec![2], big.clone(), [3; 32])),
            Op::Parent,
            Op::Push(Node::KV(vec![3], big.clone())),
            Op::Child,
            Op::PushInverted(Node::KVRefValueHash(vec![4], big, [4; 32])),
            Op::ChildInverted,
        ];
        let mut bytes = vec![];
        super::encode_into(ops.iter(), &mut bytes);
        let decoded: Vec<Op> = Decoder::new(&bytes).map(|r| r.unwrap()).collect();
        assert_eq!(decoded, ops);

        let mut v310 = Decoder::new_v310(&bytes);
        assert_eq!(v310.next().unwrap().unwrap(), ops[0]);
        assert!(v310.next().unwrap().is_err());
        // 3.1.0's decoder keeps yielding the same error; the strict one stops.
        assert!(v310.next().unwrap().is_err());
    }

    #[test]
    fn strict_decoder_stops_after_an_error() {
        let bytes = [0x88u8, 0x10];
        let mut d = Decoder::new(&bytes);
        assert!(d.next().unwrap().is_err());
        assert!(d.next().is_none());
    }

    #[test]
    fn large_opcode_with_a_short_value_is_refused() {
        // A 0x20 op declaring a 100-byte value: that value has a 3.1.0
        // encoding, so the large form is non-canonical and refused.
        let mut bytes = vec![0x20, 1, 9];
        bytes.extend_from_slice(&100u32.to_be_bytes());
        bytes.extend_from_slice(&[0; 100]);
        assert!(Op::decode(&bytes).is_err());
        let mut at_threshold = vec![0x20, 1, 9];
        at_threshold.extend_from_slice(&((LARGE_VALUE_THRESHOLD - 1) as u32).to_be_bytes());
        at_threshold.extend_from_slice(&vec![0; LARGE_VALUE_THRESHOLD - 1]);
        assert!(Op::decode(&at_threshold).is_err());
    }

    #[test]
    fn large_opcode_over_the_cap_or_truncated_is_refused() {
        let mut over = vec![0x21, 1, 9];
        over.extend_from_slice(&(MAX_VALUE_LEN + 1).to_be_bytes());
        assert!(Op::decode(&over).is_err());

        // Declares 64 MiB but carries 10 bytes: refused without trusting the
        // declared length for the allocation.
        let mut truncated = vec![0x20, 1, 9];
        truncated.extend_from_slice(&MAX_VALUE_LEN.to_be_bytes());
        truncated.extend_from_slice(&[0; 10]);
        assert!(Op::decode(&truncated).is_err());

        // Large value present but its value hash cut short.
        let op = Op::Push(Node::KVValueHash(
            vec![1],
            vec![0; LARGE_VALUE_THRESHOLD],
            [5; 32],
        ));
        let mut bytes = vec![];
        op.encode_into(&mut bytes).unwrap();
        bytes.truncate(bytes.len() - 1);
        assert!(Op::decode(&bytes).is_err());
    }

    #[test]
    fn unassigned_large_opcodes_stay_unknown() {
        // 0x24/0x25/0x2c/0x2d are upstream's count-tree variants, which this
        // version does not have; 0x26/0x27/0x2e/0x2f are unassigned.
        for opcode in [0x24u8, 0x25, 0x26, 0x27, 0x2c, 0x2d, 0x2e, 0x2f, 0x30] {
            let mut bytes = vec![opcode, 1, 9];
            bytes.extend_from_slice(&(LARGE_VALUE_THRESHOLD as u32).to_be_bytes());
            bytes.extend_from_slice(&vec![0; LARGE_VALUE_THRESHOLD + 64]);
            assert!(Op::decode(&bytes).is_err(), "{opcode:#x}");
            assert!(Op::decode_v310(&bytes).is_err(), "{opcode:#x}");
        }
        let _ = ProofRules::V310;
    }
}
