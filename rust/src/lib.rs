//! Loop-free canonical-CBOR decoder paths extracted for machine-checked
//! no-panic claims.
//!
//! [`take`], [`Reader::read_head`], [`Reader::read_uint`], [`Reader::read_bstr`],
//! and [`Reader::read_bstr_fixed_64`] are copied from `kntrl-license-core`
//! `cbor/reader.rs`. Every line that is not a verbatim copy of that path is
//! marked `// EXTRACT:` or `// REMODEL:`.

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
    /// A length or count could not be represented in this platform's `usize`.
    LengthOverflow,
    /// A fixed-length byte string had the wrong length.
    WrongLength,
}

/// Major type 0 (unsigned integer), pre-shifted into the top-3-bits position.
const MAJOR_UNSIGNED: u8 = 0x00;
/// Major type 2 (byte string), pre-shifted into the top-3-bits position.
const MAJOR_BSTR: u8 = 0x40;
/// Mask selecting the major-type bits of a CBOR head byte.
const MAJOR_MASK: u8 = 0xE0;
/// Mask selecting the additional-info bits of a CBOR head byte.
const ADDITIONAL_MASK: u8 = 0x1F;

/// A cursor over a borrowed canonical-CBOR byte slice.
///
/// Every `read_*` method on the chosen path rejects non-canonical encodings
/// (extra-length forms, indefinite-length items) as it goes.
// REMODEL: dropped `Debug`/`Clone`/`Copy` so Aeneas does not emit an opaque
// `fmt` axiom for `&[u8]` (unused on the no-panic path).
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
        // REMODEL: `Option::ok_or` is an Aeneas-unknown external (opaque axiom).
        // Same `checked_add` + `slice::get` as source; `None` is still UnexpectedEnd.
        let end = match self.pos.checked_add(n) {
            Some(end) => end,
            None => return Err(CodecError::UnexpectedEnd),
        };
        match self.buf.get(self.pos..end) {
            Some(out) => {
                self.pos = end;
                Ok(out)
            },
            None => Err(CodecError::UnexpectedEnd),
        }
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
        let head = get_u8(self.take(1)?, 0)?;
        if head & MAJOR_MASK != major_base {
            return Err(CodecError::TypeMismatch);
        }
        let additional = head & ADDITIONAL_MASK;
        if additional < 24 {
            return Ok(u64::from(additional));
        }
        match additional {
            24 => {
                let byte = get_u8(self.take(1)?, 0)?;
                if byte < 24 {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(u64::from(byte))
            },
            25 => {
                let bytes = self.take(2)?;
                let value = u64::from(u16::from_be_bytes([get_u8(bytes, 0)?, get_u8(bytes, 1)?]));
                // REMODEL: `u8::try_from(value).is_ok()` is an Aeneas-unknown
                // `TryFrom<u64>` axiom; the bound is the same as source.
                if value <= u64::from(u8::MAX) {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            },
            26 => {
                let bytes = self.take(4)?;
                let value = u64::from(u32::from_be_bytes([
                    get_u8(bytes, 0)?,
                    get_u8(bytes, 1)?,
                    get_u8(bytes, 2)?,
                    get_u8(bytes, 3)?,
                ]));
                // REMODEL: same as `u16::try_from(value).is_ok()` in source.
                if value <= u64::from(u16::MAX) {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            },
            27 => {
                let bytes = self.take(8)?;
                let value = u64::from_be_bytes([
                    get_u8(bytes, 0)?,
                    get_u8(bytes, 1)?,
                    get_u8(bytes, 2)?,
                    get_u8(bytes, 3)?,
                    get_u8(bytes, 4)?,
                    get_u8(bytes, 5)?,
                    get_u8(bytes, 6)?,
                    get_u8(bytes, 7)?,
                ]);
                // REMODEL: same as `u32::try_from(value).is_ok()` in source.
                if value <= u64::from(u32::MAX) {
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

    /// Reads a canonical CBOR definite-length byte string (major type 2), zero-copy.
    ///
    /// # Errors
    /// Returns [`CodecError::TypeMismatch`] if the next item is not major type 2,
    /// [`CodecError::NonCanonicalLength`] if its length is not smallest-form,
    /// [`CodecError::LengthOverflow`] if the length does not fit `usize`, or
    /// [`CodecError::UnexpectedEnd`] if the input is truncated.
    pub fn read_bstr(&mut self) -> Result<&'a [u8], CodecError> {
        let len = self.read_head(MAJOR_BSTR)?;
        // REMODEL: `usize::try_from(len).map_err(...)` is an Aeneas-unknown
        // `TryFrom<u64>` / `map_err` pair; the overflow check is the same.
        if len > usize::MAX as u64 {
            return Err(CodecError::LengthOverflow);
        }
        #[allow(clippy::cast_possible_truncation)] // bounded by the check above
        let len = len as usize;
        self.take(len)
    }

    /// Reads a canonical CBOR byte string that must be exactly 64 bytes long.
    ///
    /// EXTRACT: source is `read_bstr_fixed::<N>`; this crate monomorphizes N=64
    /// (COSE_Sign1 signature). Kid N=16 is a later path.
    ///
    /// # Errors
    /// As [`Reader::read_bstr`], plus [`CodecError::WrongLength`] if the decoded
    /// length is not exactly 64. The body is taken first, then the length is
    /// checked — a truncated 64-byte claim stays [`CodecError::UnexpectedEnd`].
    pub fn read_bstr_fixed_64(&mut self) -> Result<[u8; 64], CodecError> {
        let bytes = self.read_bstr()?;
        // REMODEL: `try_from(...).map_err(...)` → match; same WrongLength.
        // Do not reject `len != 64` before `take` (that would turn a truncated
        // body into WrongLength).
        match <[u8; 64]>::try_from(bytes) {
            Ok(arr) => Ok(arr),
            Err(_) => Err(CodecError::WrongLength),
        }
    }
}

/// Index `bytes[i]` as `Result`, never a panic.
///
/// REMODEL: source uses `slice::first().copied().ok_or(UnexpectedEnd)` and
/// `try_into` on a length-checked slice. Both became Aeneas-unknown externals
/// (`Option::ok_or`, `Option::copied`, `TryFrom<&[u8]> for [u8; N]`,
/// `Result::map_err`). `slice::get` + `match` is the same bounds check.
fn get_u8(bytes: &[u8], i: usize) -> Result<u8, CodecError> {
    match bytes.get(i) {
        Some(b) => Ok(*b),
        None => Err(CodecError::UnexpectedEnd),
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

/// Reads a canonical CBOR definite-length byte string from the start of `buf`.
///
/// # Errors
/// As [`Reader::read_bstr`].
// EXTRACT: public `&[u8]` entry point so the no-panic theorem is a function of
// hostile bytes (Binder `parse_one` shape). Body is `Reader::new` + method.
pub fn read_bstr(buf: &[u8]) -> Result<&[u8], CodecError> {
    // EXTRACT: wrapper; source exposes only the method on `Reader`.
    let mut reader = Reader::new(buf);
    reader.read_bstr()
}

/// Reads a canonical CBOR byte string that must be exactly 64 bytes long.
///
/// # Errors
/// As [`Reader::read_bstr_fixed_64`].
// EXTRACT: public `&[u8]` entry point so the no-panic theorem is a function of
// hostile bytes (Binder `parse_one` shape). Body is `Reader::new` + method.
pub fn read_bstr_fixed_64(buf: &[u8]) -> Result<[u8; 64], CodecError> {
    // EXTRACT: wrapper; source exposes only the method on `Reader`.
    let mut reader = Reader::new(buf);
    reader.read_bstr_fixed_64()
}

#[cfg(test)]
mod tests {
    use super::{read_bstr, read_bstr_fixed_64, read_uint, CodecError, Reader};

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
            assert_eq!(
                read_uint(bytes),
                Ok(*value),
                "free wrapper must decode {value}"
            );
            let mut reader = Reader::new(bytes);
            let decoded = reader.read_uint().expect("encoded bytes must decode");
            assert_eq!(
                decoded, *value,
                "Reader method must preserve the exact value"
            );
        }
    }

    /// Copied from source `should_reject_non_canonical_uint_length`.
    #[test]
    fn should_reject_non_canonical_uint_length() {
        let bytes = [0x18_u8, 0x05];
        let err = read_uint(&bytes).expect_err("2-byte form of 5 must be rejected");
        assert_eq!(err, CodecError::NonCanonicalLength);
        // REMODEL: extra-width forms that `try_from` rejected in source.
        assert_eq!(
            read_uint(&[0x19, 0x00, 0xFF]),
            Err(CodecError::NonCanonicalLength)
        );
        assert_eq!(
            read_uint(&[0x1A, 0x00, 0x00, 0x00, 0xFF]),
            Err(CodecError::NonCanonicalLength)
        );
        assert_eq!(
            read_uint(&[0x1B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF]),
            Err(CodecError::NonCanonicalLength)
        );
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
        assert_eq!(
            read_uint(&[0x1A, 0x00, 0x00, 0x00]),
            Err(CodecError::UnexpectedEnd)
        );
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

    /// Canonical definite-length bstrs, including empty and the 1-byte length
    /// threshold (24). Vectors match RFC 8949 §3.1 major type 2.
    #[test]
    fn should_decode_canonical_bstr() {
        assert_eq!(read_bstr(&[0x40]), Ok([].as_slice()));
        assert_eq!(read_bstr(&[0x41, 0xAB]), Ok([0xAB].as_slice()));
        assert_eq!(
            read_bstr(&[0x43, 0x01, 0x02, 0x03]),
            Ok([0x01, 0x02, 0x03].as_slice())
        );
        let mut twenty_four = [0_u8; 26];
        twenty_four[0] = 0x58;
        twenty_four[1] = 0x18;
        twenty_four[2..].fill(0xAA);
        assert_eq!(read_bstr(&twenty_four), Ok([0xAA; 24].as_slice()));
        let mut reader = Reader::new(&[0x41, 0xAB]);
        let decoded = reader.read_bstr().expect("encoded bytes must decode");
        assert_eq!(decoded, [0xAB]);
    }

    #[test]
    fn should_reject_non_canonical_bstr_length() {
        // 1-byte length form of 5 (must be additional-info 5).
        assert_eq!(
            read_bstr(&[0x58, 0x05, 0x01, 0x02, 0x03, 0x04, 0x05]),
            Err(CodecError::NonCanonicalLength)
        );
    }

    #[test]
    fn should_reject_empty_bstr_input() {
        assert_eq!(read_bstr(&[]), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_reject_major_type_not_bstr() {
        assert_eq!(read_bstr(&[0x00]), Err(CodecError::TypeMismatch));
        assert_eq!(read_bstr(&[0x60]), Err(CodecError::TypeMismatch));
    }

    #[test]
    fn should_reject_truncated_bstr_header() {
        assert_eq!(read_bstr(&[0x58]), Err(CodecError::UnexpectedEnd));
        assert_eq!(read_bstr(&[0x59, 0x00]), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_reject_truncated_bstr_body() {
        // Claims 3 bytes, only 2 follow. Must stay UnexpectedEnd, not WrongLength.
        assert_eq!(
            read_bstr(&[0x43, 0x01, 0x02]),
            Err(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            read_bstr(&[0x58, 0x18, 0x00]),
            Err(CodecError::UnexpectedEnd)
        );
    }

    #[test]
    fn should_decode_fixed_64_bstr() {
        let mut bytes = [0_u8; 66];
        bytes[0] = 0x58;
        bytes[1] = 64;
        for (i, slot) in bytes[2..].iter_mut().enumerate() {
            *slot = u8::try_from(i).unwrap_or(0);
        }
        let got = read_bstr_fixed_64(&bytes).expect("64-byte bstr must decode");
        assert_eq!(got[0], 0);
        assert_eq!(got[63], 63);
        let mut reader = Reader::new(&bytes);
        let via_method = reader.read_bstr_fixed_64().expect("method must decode");
        assert_eq!(via_method, got);
    }

    #[test]
    fn should_reject_fixed_64_wrong_length_after_full_body() {
        // Complete 8-byte bstr offered to the 64-byte reader.
        assert_eq!(
            read_bstr_fixed_64(&[0x48, 1, 2, 3, 4, 5, 6, 7, 8]),
            Err(CodecError::WrongLength)
        );
        // Complete 65-byte bstr (1-byte length form).
        let mut too_long = [0_u8; 67];
        too_long[0] = 0x58;
        too_long[1] = 65;
        assert_eq!(read_bstr_fixed_64(&too_long), Err(CodecError::WrongLength));
    }

    #[test]
    fn should_reject_truncated_fixed_64_body() {
        // Header claims 64, body is short. Must stay UnexpectedEnd, not WrongLength.
        let mut bytes = [0_u8; 12];
        bytes[0] = 0x58;
        bytes[1] = 64;
        assert_eq!(read_bstr_fixed_64(&bytes), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_reject_reserved_and_indefinite_bstr() {
        assert_eq!(read_bstr(&[0x5C]), Err(CodecError::DisallowedMajorType));
        assert_eq!(read_bstr(&[0x5F]), Err(CodecError::IndefiniteLength));
    }
}
