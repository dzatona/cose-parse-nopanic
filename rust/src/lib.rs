//! Loop-free canonical-CBOR unsigned-integer decoder, extracted for a
//! machine-checked no-panic claim.
//!
//! [`take`], [`Reader::read_head`], and [`Reader::read_uint`] are copied from
//! `kntrl-license-core` `cbor/reader.rs`. Every line that is not a verbatim copy
//! of that path is marked `// EXTRACT:` or `// REMODEL:`.

// EXTRACT: standalone crate is `no_std` and allocator-free; the source crate
// is also `no_std` by default, but this file does not pull the rest of it.
#![no_std]
// EXTRACT: the source path is already safe; keep it that way in the proof crate.
#![forbid(unsafe_code)]

/// A malformed or non-canonical CBOR byte sequence.
///
/// EXTRACT: copied from `kntrl-license-core` `error.rs`, keeping only the
/// variants this path can produce. `thiserror` is dropped so Charon sees a
/// plain `Copy` enum and no proc-macro dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodecError {
    /// The input ended before a complete CBOR item could be read.
    UnexpectedEnd,
    /// The next CBOR item's major type does not match what the schema expects here.
    TypeMismatch,
    /// An integer used more encoding bytes than its value strictly requires
    /// (RFC 8949 §4.2.1 smallest-form only).
    NonCanonicalLength,
    /// The input uses CBOR's indefinite-length encoding, which this parser never
    /// accepts.
    IndefiniteLength,
    /// Additional-info values 28..=30 (reserved) appeared in a head byte.
    DisallowedMajorType,
}

/// Major type 0 (unsigned integer), pre-shifted into the top-3-bits position.
const MAJOR_UNSIGNED: u8 = 0x00;
/// Mask selecting the major-type bits of a CBOR head byte.
const MAJOR_MASK: u8 = 0xE0;
/// Mask selecting the additional-info bits of a CBOR head byte.
const ADDITIONAL_MASK: u8 = 0x1F;

/// A cursor over a borrowed canonical-CBOR byte slice.
///
/// Every `read_*` method on the chosen path rejects non-canonical encodings
/// (extra-length forms, indefinite-length items) as it goes.
#[derive(Debug, Clone, Copy)]
pub struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    /// Starts a cursor at the beginning of `buf`.
    #[must_use]
    pub const fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    /// Consumes and returns the next `n` bytes.
    ///
    /// # Errors
    /// Returns [`CodecError::UnexpectedEnd`] if fewer than `n` bytes remain.
    fn take(&mut self, n: usize) -> Result<&'a [u8], CodecError> {
        let end = self.pos.checked_add(n).ok_or(CodecError::UnexpectedEnd)?;
        let out = self.buf.get(self.pos..end).ok_or(CodecError::UnexpectedEnd)?;
        self.pos = end;
        Ok(out)
    }

    /// Reads one CBOR head (major type + canonical-minimal argument), requiring the major
    /// type to equal `major_base`.
    ///
    /// # Errors
    /// Returns [`CodecError::TypeMismatch`] if the major type does not match
    /// `major_base`, [`CodecError::NonCanonicalLength`] if the argument is not in
    /// smallest-form encoding, [`CodecError::DisallowedMajorType`]/
    /// [`CodecError::IndefiniteLength`] for the two reserved/indefinite-length additional
    /// values, or [`CodecError::UnexpectedEnd`] if the input is truncated.
    fn read_head(&mut self, major_base: u8) -> Result<u64, CodecError> {
        let head = self.take(1)?.first().copied().ok_or(CodecError::UnexpectedEnd)?;
        if head & MAJOR_MASK != major_base {
            return Err(CodecError::TypeMismatch);
        }
        let additional = head & ADDITIONAL_MASK;
        if additional < 24 {
            return Ok(u64::from(additional));
        }
        match additional {
            24 => {
                let byte = self.take(1)?.first().copied().ok_or(CodecError::UnexpectedEnd)?;
                if byte < 24 {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(u64::from(byte))
            },
            25 => {
                let bytes = self.take(2)?;
                let array: [u8; 2] =
                    bytes.try_into().map_err(|_wrong_len| CodecError::UnexpectedEnd)?;
                let value = u64::from(u16::from_be_bytes(array));
                if u8::try_from(value).is_ok() {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            },
            26 => {
                let bytes = self.take(4)?;
                let array: [u8; 4] =
                    bytes.try_into().map_err(|_wrong_len| CodecError::UnexpectedEnd)?;
                let value = u64::from(u32::from_be_bytes(array));
                if u16::try_from(value).is_ok() {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            },
            27 => {
                let bytes = self.take(8)?;
                let array: [u8; 8] =
                    bytes.try_into().map_err(|_wrong_len| CodecError::UnexpectedEnd)?;
                let value = u64::from_be_bytes(array);
                if u32::try_from(value).is_ok() {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            },
            28..=30 => Err(CodecError::DisallowedMajorType),
            _ => Err(CodecError::IndefiniteLength),
        }
    }

    /// Reads a canonical CBOR unsigned integer (major type 0).
    ///
    /// # Errors
    /// Returns [`CodecError::TypeMismatch`] if the next item is not major type 0,
    /// [`CodecError::NonCanonicalLength`] if it is not in smallest-form encoding, or
    /// [`CodecError::UnexpectedEnd`] if the input is truncated.
    pub fn read_uint(&mut self) -> Result<u64, CodecError> {
        self.read_head(MAJOR_UNSIGNED)
    }
}

/// Reads a canonical CBOR unsigned integer from the start of `buf`.
///
/// # Errors
/// As [`Reader::read_uint`].
// EXTRACT: public `&[u8]` entry point so the no-panic theorem is a function of
// hostile bytes (Binder `parse_one` shape). Body is `Reader::new` + method.
pub fn read_uint(buf: &[u8]) -> Result<u64, CodecError> {
    // EXTRACT: wrapper; source exposes only the method on `Reader`.
    let mut reader = Reader::new(buf);
    reader.read_uint()
}

#[cfg(test)]
mod tests {
    use super::{read_uint, CodecError, Reader};

    /// Canonical encodings of the smallest-form uint boundaries from the source
    /// `should_round_trip_uint_smallest_form_boundaries` test, written by hand
    /// because the encoder is not extracted.
    // EXTRACT: source builds these via `write_uint`; vectors match RFC 8949 §3.1.
    #[test]
    fn should_decode_uint_smallest_form_boundaries() {
        let cases: &[(&[u8], u64)] = &[
            (&[0x00], 0),
            (&[0x17], 23),
            (&[0x18, 0x18], 24),
            (&[0x18, 0xFF], 255),
            (&[0x19, 0x01, 0x00], 256),
            (&[0x19, 0xFF, 0xFF], 65_535),
            (&[0x1A, 0x00, 0x01, 0x00, 0x00], 65_536),
            (&[0x1A, 0xFF, 0xFF, 0xFF, 0xFF], u64::from(u32::MAX)),
            (
                &[0x1B, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00],
                u64::from(u32::MAX) + 1,
            ),
        ];
        for (bytes, value) in cases {
            assert_eq!(read_uint(bytes), Ok(*value), "free wrapper must decode {value}");
            let mut reader = Reader::new(bytes);
            let decoded = reader.read_uint().expect("encoded bytes must decode");
            assert_eq!(decoded, *value, "Reader method must preserve the exact value");
        }
    }

    /// Copied from source `should_reject_non_canonical_uint_length`.
    #[test]
    fn should_reject_non_canonical_uint_length() {
        let bytes = [0x18_u8, 0x05];
        let err = read_uint(&bytes).expect_err("2-byte form of 5 must be rejected");
        assert_eq!(err, CodecError::NonCanonicalLength);
    }

    #[test]
    fn should_reject_empty_input() {
        let err = read_uint(&[]).expect_err("empty input must be truncated");
        assert_eq!(err, CodecError::UnexpectedEnd);
    }

    #[test]
    fn should_reject_major_type_not_unsigned() {
        // Major type 2 (bstr), additional 0 — not an unsigned integer.
        let err = read_uint(&[0x40]).expect_err("bstr head must not decode as uint");
        assert_eq!(err, CodecError::TypeMismatch);
    }

    #[test]
    fn should_reject_truncated_extra_length() {
        assert_eq!(read_uint(&[0x18]), Err(CodecError::UnexpectedEnd));
        assert_eq!(read_uint(&[0x19, 0x00]), Err(CodecError::UnexpectedEnd));
        assert_eq!(read_uint(&[0x1A, 0x00, 0x00, 0x00]), Err(CodecError::UnexpectedEnd));
        assert_eq!(
            read_uint(&[0x1B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]),
            Err(CodecError::UnexpectedEnd)
        );
    }

    #[test]
    fn should_reject_reserved_and_indefinite_additional() {
        assert_eq!(read_uint(&[0x1C]), Err(CodecError::DisallowedMajorType));
        assert_eq!(read_uint(&[0x1D]), Err(CodecError::DisallowedMajorType));
        assert_eq!(read_uint(&[0x1E]), Err(CodecError::DisallowedMajorType));
        assert_eq!(read_uint(&[0x1F]), Err(CodecError::IndefiniteLength));
    }
}
