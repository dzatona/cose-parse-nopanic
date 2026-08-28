//! Canonical-CBOR decoder paths extracted for machine-checked no-panic claims.
//!
//! [`take`], [`Reader::read_head`], [`Reader::read_uint`], [`Reader::read_bstr`],
//! [`Reader::read_bstr_fixed_64`], [`Reader::read_bstr_fixed_16`],
//! [`Reader::read_array_header`], [`Reader::read_map_header`],
//! [`Reader::read_fixed_byte`], [`Reader::next_map_key`], and [`Reader::finish`]
//! are copied from `kntrl-license-core` `cbor/reader.rs`. [`read_sign1_envelope`]
//! composes the `COSE_Sign1` array-of-4 prefix of `verify`.
//! [`decode_protected_header`] is the unrolled `{1,4,100}` map (three
//! [`Reader::next_map_key`] calls, not a walker). [`build_sig_structure`]
//! rebuilds RFC 9052 `Sig_structure` into a `[u8; MAX_MESSAGE_LEN]` buffer.
//! [`parse_sign1`] is `verify` minus crypto: those three helpers, then
//! [`Parsed`]. [`slice_validated_uints`] is a looping specialization of
//! `slice_validated_array` (`while seen < count`). Every line that is not a
//! verbatim copy of that path is marked `// EXTRACT:` or `// REMODEL:`.

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
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
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
    /// Extra bytes remain after a complete self-delimiting item.
    TrailingBytes,
    /// Map keys were not strictly ascending (covers a duplicate key too).
    NonCanonicalKeyOrder,
    /// An integer that should select a fixed enum discriminant is out of range.
    InvalidEnumValue,
    /// The output buffer has no room left for the next encoded item.
    BufferTooSmall,
}

/// A `COSE_Sign1` envelope that is structurally malformed.
///
/// EXTRACT: copied from `kntrl-license-core` `error.rs` `CoseError`, keeping
/// only the variants the envelope and protected-header paths can produce
/// (`Codec`, `MalformedEnvelope`, `NonEmptyUnprotectedHeader`,
/// `MalformedProtectedHeader`, `UnsupportedAlgorithm`, `UnknownTyp`).
/// `thiserror` is dropped so Charon sees a plain `Copy` enum. Codec errors
/// wrap as [`CoseError::Codec`] via [`From`] (source: `#[from] CodecError`).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub enum CoseError {
    /// A lower-level canonical-CBOR codec error.
    Codec(CodecError),
    /// The envelope is not a definite-length 4-element array.
    MalformedEnvelope,
    /// The unprotected header is not the empty map.
    NonEmptyUnprotectedHeader,
    /// The protected header is not exactly `{1: alg, 4: kid, 100: typ}`.
    MalformedProtectedHeader,
    /// The protected header's `alg` is not `-8` (`EdDSA`).
    UnsupportedAlgorithm,
    /// The protected header's `typ` is not one of the four defined discriminants.
    UnknownTyp,
}

// EXTRACT: source is `#[from] CodecError` on `CoseError::Codec` (thiserror).
// Same wrap: `?` on a `CodecError` in a `Result<_, CoseError>` function
// becomes `CoseError::Codec(...)`. thiserror is not pulled.
impl From<CodecError> for CoseError {
    fn from(error: CodecError) -> Self {
        Self::Codec(error)
    }
}

/// Major type 0 (unsigned integer), pre-shifted into the top-3-bits position.
const MAJOR_UNSIGNED: u8 = 0x00;
/// Major type 1 (negative integer), pre-shifted into the top-3-bits position.
const MAJOR_NEGATIVE: u8 = 0x20;
/// Major type 2 (byte string), pre-shifted into the top-3-bits position.
const MAJOR_BSTR: u8 = 0x40;
/// Major type 3 (text string), pre-shifted into the top-3-bits position.
const MAJOR_TEXT: u8 = 0x60;
/// Major type 4 (array), pre-shifted into the top-3-bits position.
const MAJOR_ARRAY: u8 = 0x80;
/// Fixed stack buffer for a reconstructed `Sig_structure`.
///
/// EXTRACT: copied from `kntrl-license-core` `cose/mod.rs`. A cap on each
/// input bstr at this size does not imply the encoded structure fits.
pub const MAX_MESSAGE_LEN: usize = 4096;
/// Major type 5 (map), pre-shifted into the top-3-bits position.
const MAJOR_MAP: u8 = 0xA0;
/// Mask selecting the major-type bits of a CBOR head byte.
const MAJOR_MASK: u8 = 0xE0;
/// Mask selecting the additional-info bits of a CBOR head byte.
const ADDITIONAL_MASK: u8 = 0x1F;
/// COSE `alg = -8` (`EdDSA`): major type 1 with argument 7 (`-(1 + 7)`).
const ALG_EDDSA_BYTE: u8 = MAJOR_NEGATIVE | 0x07;

/// The COSE protected-header `typ` discriminant.
///
/// EXTRACT: copied from `kntrl-license-core` `types.rs`, keeping only this
/// enum and [`Typ::from_u64`]. Product meaning of each variant is outside
/// the no-panic claim. `Hash` is dropped (unused on this path).
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(test, derive(Debug))]
pub enum Typ {
    /// `typ = 1`.
    License,
    /// `typ = 2`.
    Enroll,
    /// `typ = 3`.
    Revoke,
    /// `typ = 4`.
    TrustUpdate,
}

impl Typ {
    /// Parses the canonical `uint` discriminant back into a [`Typ`].
    ///
    /// # Errors
    /// Returns [`CodecError::InvalidEnumValue`] if `value` is not `1..=4`.
    pub const fn from_u64(value: u64) -> Result<Self, CodecError> {
        match value {
            1 => Ok(Self::License),
            2 => Ok(Self::Enroll),
            3 => Ok(Self::Revoke),
            4 => Ok(Self::TrustUpdate),
            _ => Err(CodecError::InvalidEnumValue),
        }
    }
}

/// The exact `external_aad` ASCII literal for [`Typ::License`].
pub const AAD_LICENSE: &[u8] = b"kntrl/license/v1";
/// The exact `external_aad` ASCII literal for [`Typ::Enroll`].
pub const AAD_ENROLL: &[u8] = b"kntrl/enroll/v1";
/// The exact `external_aad` ASCII literal for [`Typ::Revoke`].
pub const AAD_REVOKE: &[u8] = b"kntrl/revoke/v1";
/// The exact `external_aad` ASCII literal for [`Typ::TrustUpdate`].
pub const AAD_TRUST_UPDATE: &[u8] = b"kntrl/trust-update/v1";

/// Returns the exact `external_aad` ASCII bytes for `typ`.
///
/// EXTRACT: copied from `kntrl-license-core` `domain.rs`. Match only; product
/// meaning of each token is outside the no-panic claim.
#[must_use]
pub const fn external_aad(typ: Typ) -> &'static [u8] {
    match typ {
        Typ::License => AAD_LICENSE,
        Typ::Enroll => AAD_ENROLL,
        Typ::Revoke => AAD_REVOKE,
        Typ::TrustUpdate => AAD_TRUST_UPDATE,
    }
}

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

    /// Returns `true` iff every byte of the input has been consumed.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.pos == self.buf.len()
    }

    /// Confirms every byte of the input was consumed.
    ///
    /// # Errors
    /// Returns [`CodecError::TrailingBytes`] if bytes remain.
    pub const fn finish(&self) -> Result<(), CodecError> {
        if self.is_empty() {
            Ok(())
        } else {
            Err(CodecError::TrailingBytes)
        }
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
            }
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
            }
            25 => {
                let bytes = self.take(2)?;
                let value = u64::from(u16::from_be_bytes([get_u8(bytes, 0)?, get_u8(bytes, 1)?]));
                // REMODEL: `u8::try_from(value).is_ok()` is an Aeneas-unknown
                // `TryFrom<u64>` axiom; the bound is the same as source.
                if value <= u64::from(u8::MAX) {
                    return Err(CodecError::NonCanonicalLength);
                }
                Ok(value)
            }
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
            }
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
            }
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
    /// (COSE_Sign1 signature). Kid N=16 is [`Reader::read_bstr_fixed_16`].
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

    /// Reads a canonical CBOR byte string that must be exactly 16 bytes long.
    ///
    /// EXTRACT: source is `read_bstr_fixed::<N>`; this crate monomorphizes N=16
    /// (protected-header kid).
    ///
    /// # Errors
    /// As [`Reader::read_bstr`], plus [`CodecError::WrongLength`] if the decoded
    /// length is not exactly 16. The body is taken first, then the length is
    /// checked — a truncated 16-byte claim stays [`CodecError::UnexpectedEnd`].
    pub fn read_bstr_fixed_16(&mut self) -> Result<[u8; 16], CodecError> {
        let bytes = self.read_bstr()?;
        // REMODEL: `try_from(...).map_err(...)` → match; same WrongLength.
        // Do not reject `len != 16` before `take` (that would turn a truncated
        // body into WrongLength).
        match <[u8; 16]>::try_from(bytes) {
            Ok(arr) => Ok(arr),
            Err(_) => Err(CodecError::WrongLength),
        }
    }

    /// Reads a canonical CBOR definite-length array header (major type 4).
    ///
    /// # Errors
    /// As [`Reader::read_uint`] (for major type 4 instead of 0).
    pub fn read_array_header(&mut self) -> Result<u64, CodecError> {
        self.read_head(MAJOR_ARRAY)
    }

    /// Reads a canonical CBOR definite-length map header (major type 5).
    ///
    /// # Errors
    /// As [`Reader::read_uint`] (for major type 5 instead of 0).
    pub fn read_map_header(&mut self) -> Result<u64, CodecError> {
        self.read_head(MAJOR_MAP)
    }

    /// Reads exactly one raw byte and requires it to equal `expected` verbatim.
    ///
    /// # Errors
    /// Returns [`CodecError::TypeMismatch`] if the next byte does not equal
    /// `expected`, or [`CodecError::UnexpectedEnd`] if the input is truncated.
    pub fn read_fixed_byte(&mut self, expected: u8) -> Result<(), CodecError> {
        // REMODEL: source is `take(1)?.first().copied().ok_or(UnexpectedEnd)`.
        // Same bounds check as layer-1 `get_u8`.
        let byte = get_u8(self.take(1)?, 0)?;
        if byte == expected {
            Ok(())
        } else {
            Err(CodecError::TypeMismatch)
        }
    }

    /// Reads the next map key as a canonical unsigned integer and requires it
    /// to be strictly greater than `*last_key`.
    ///
    /// # Errors
    /// As [`Reader::read_uint`], plus [`CodecError::NonCanonicalKeyOrder`] if
    /// the new key does not strictly exceed `*last_key`.
    pub fn next_map_key(&mut self, last_key: &mut Option<u64>) -> Result<u64, CodecError> {
        let key = self.read_uint()?;
        // REMODEL: source is `if let Some(last) = *last_key && key <= last`.
        // Nested `if let` is the same strictly-ascending check; avoids a
        // let-chain that Aeneas does not model.
        if let Some(last) = *last_key {
            if key <= last {
                return Err(CodecError::NonCanonicalKeyOrder);
            }
        }
        *last_key = Some(key);
        Ok(key)
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

/// Reads a canonical CBOR definite-length array header from the start of `buf`.
///
/// # Errors
/// As [`Reader::read_array_header`].
// EXTRACT: public `&[u8]` entry point so the no-panic theorem is a function of
// hostile bytes (Binder `parse_one` shape). Body is `Reader::new` + method.
pub fn read_array_header(buf: &[u8]) -> Result<u64, CodecError> {
    // EXTRACT: wrapper; source exposes only the method on `Reader`.
    let mut reader = Reader::new(buf);
    reader.read_array_header()
}

/// Reads a canonical CBOR definite-length map header from the start of `buf`.
///
/// # Errors
/// As [`Reader::read_map_header`].
// EXTRACT: public `&[u8]` entry point so the no-panic theorem is a function of
// hostile bytes (Binder `parse_one` shape). Body is `Reader::new` + method.
pub fn read_map_header(buf: &[u8]) -> Result<u64, CodecError> {
    // EXTRACT: wrapper; source exposes only the method on `Reader`.
    let mut reader = Reader::new(buf);
    reader.read_map_header()
}

/// The four `COSE_Sign1` array slots, before protected-header decode.
///
/// EXTRACT: source `verify` keeps these as locals (`protected`, `payload`,
/// `signature_bytes`) and then decodes the protected map. This type stops
/// before that decode. `Debug`/`Clone`/`Copy` are omitted so Aeneas does not
/// emit an unused slice `fmt` axiom.
pub struct Envelope<'a> {
    /// Raw protected-header byte string. Not a decoded map.
    pub protected: &'a [u8],
    /// Raw payload byte string. Not decoded.
    pub payload: &'a [u8],
    /// 64-byte signature slot. Not checked against a public key here.
    pub signature: [u8; 64],
}

/// Reads the `COSE_Sign1` array-of-4 envelope skeleton.
///
/// Order matches source `verify` before protected-header decode: array header
/// must be 4, then protected bstr, empty unprotected map, payload bstr,
/// 64-byte signature bstr, then [`Reader::finish`].
///
/// # Errors
/// Returns [`CoseError::MalformedEnvelope`] if the array count is not 4,
/// [`CoseError::NonEmptyUnprotectedHeader`] if the unprotected map is not
/// empty, [`CoseError::Codec`] wrapping [`CodecError::TrailingBytes`] if
/// bytes remain after the signature, or [`CoseError::Codec`] wrapping the
/// same [`CodecError`] variants as the bstr readers for truncated or
/// non-canonical slots.
// EXTRACT: `verify` lines 221–234 that read the four array slots and
// `finish`, minus `decode_protected_header`, `build_sig_structure`, and
// dalek. Return type matches source `verify` prefix: `Result<_, CoseError>`.
// `?` on `CodecError` uses [`From`] → [`CoseError::Codec`]. Truncated-bstr
// errors are unchanged (`UnexpectedEnd`, not `WrongLength`, on a short
// signature body).
pub fn read_sign1_envelope(buf: &[u8]) -> Result<Envelope<'_>, CoseError> {
    let mut reader = Reader::new(buf);
    let count = reader.read_array_header()?;
    if count != 4 {
        return Err(CoseError::MalformedEnvelope);
    }
    let protected = reader.read_bstr()?;
    let unprotected_count = reader.read_map_header()?;
    if unprotected_count != 0 {
        return Err(CoseError::NonEmptyUnprotectedHeader);
    }
    let payload = reader.read_bstr()?;
    let signature = reader.read_bstr_fixed_64()?;
    reader.finish()?;
    Ok(Envelope {
        protected,
        payload,
        signature,
    })
}

/// Decodes a canonical `{1: alg=-8, 4: kid-16, 100: typ}` protected header.
///
/// Three [`Reader::next_map_key`] calls, not a loop over the pair count.
///
/// # Errors
/// Returns [`CoseError::MalformedProtectedHeader`] if the key set/order is not
/// exactly `{1, 4, 100}`, [`CoseError::UnsupportedAlgorithm`] if `alg` is not
/// `-8`, [`CoseError::UnknownTyp`] if `typ` is not `1..=4`, or
/// [`CoseError::Codec`] for other structural violations.
// EXTRACT: source `decode_protected_header` (cose/mod.rs) is crate-private;
// public here so the no-panic theorem is a function of hostile bytes.
// Unroll is source syntax (three `next_map_key`), not a generic map walker.
pub fn decode_protected_header(bytes: &[u8]) -> Result<([u8; 16], Typ), CoseError> {
    let mut reader = Reader::new(bytes);
    let count = reader.read_map_header()?;
    if count != 3 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    let mut last_key = None;

    let key = reader.next_map_key(&mut last_key)?;
    if key != 1 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    // REMODEL: source is `read_fixed_byte(...).map_err(|_bad_alg| UnsupportedAlgorithm)`.
    // Any failure (wrong byte or truncated) stays UnsupportedAlgorithm.
    match reader.read_fixed_byte(ALG_EDDSA_BYTE) {
        Ok(()) => {}
        Err(_) => return Err(CoseError::UnsupportedAlgorithm),
    }

    let key = reader.next_map_key(&mut last_key)?;
    if key != 4 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    let kid = reader.read_bstr_fixed_16()?;

    let key = reader.next_map_key(&mut last_key)?;
    if key != 100 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    let typ_raw = reader.read_uint()?;
    // REMODEL: source is `Typ::from_u64(...).map_err(|_unknown| UnknownTyp)`.
    // InvalidEnumValue (and only that, from this match) becomes UnknownTyp.
    let typ = match Typ::from_u64(typ_raw) {
        Ok(typ) => typ,
        Err(_) => return Err(CoseError::UnknownTyp),
    };

    reader.finish()?;
    Ok((kid, typ))
}

/// A fixed `[u8; MAX_MESSAGE_LEN]` output buffer.
///
/// EXTRACT: source `SliceSink` borrows `&mut [u8]` and implements a `Sink`
/// trait (also for `Vec<u8>` under alloc). Owned array so Aeneas does not see
/// `FnOnce` + `&mut [u8; N]` (Binder `&mut [u8; N]` trap). No trait, no Vec.
struct SliceSink {
    buf: [u8; MAX_MESSAGE_LEN],
    len: usize,
}

impl SliceSink {
    /// An initially-empty sink.
    // EXTRACT: source `new` wraps a caller `&mut [u8]`.
    const fn new() -> Self {
        Self {
            buf: [0_u8; MAX_MESSAGE_LEN],
            len: 0,
        }
    }

    /// Returns the number of bytes written so far.
    const fn len(&self) -> usize {
        self.len
    }

    /// Appends `bytes` to the end of this sink.
    ///
    /// # Errors
    /// Returns [`CodecError::BufferTooSmall`] if the sink has no room left.
    fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), CodecError> {
        // REMODEL: `Option::ok_or` is an Aeneas-unknown external (opaque axiom).
        // Same `checked_add` + `get_mut` as source; `None` is still BufferTooSmall.
        let end = match self.len.checked_add(bytes.len()) {
            Some(end) => end,
            None => return Err(CodecError::BufferTooSmall),
        };
        match self.buf.get_mut(self.len..end) {
            Some(dest) => {
                // REMODEL: copy bounded by remaining buffer. Source
                // `copy_from_slice` panics if dest/src lengths differ; Aeneas
                // models that as `fail`. The lengths already match after
                // `get_mut(len..len+bytes.len())`; the check puts `copy_from_slice`
                // behind an equal-length branch so the panic path is `Err`.
                if dest.len() != bytes.len() {
                    return Err(CodecError::BufferTooSmall);
                }
                dest.copy_from_slice(bytes);
                self.len = end;
                Ok(())
            }
            None => Err(CodecError::BufferTooSmall),
        }
    }
}

/// Index `be[i]` as `Result`, never a panic.
///
/// REMODEL: source uses `be.get(i).copied().ok_or(BufferTooSmall)` on
/// `u64::to_be_bytes()`. Same bounds check; `None` is still BufferTooSmall
/// (unlike [`get_u8`], which is UnexpectedEnd on the decoder path).
fn be_byte(be: &[u8; 8], i: usize) -> Result<u8, CodecError> {
    match be.get(i) {
        Some(b) => Ok(*b),
        None => Err(CodecError::BufferTooSmall),
    }
}

/// Writes a canonical CBOR head (major type + argument) in smallest-form encoding.
///
/// EXTRACT: source is generic over `impl Sink`. This path only has [`SliceSink`].
///
/// # Errors
/// Returns [`CodecError::BufferTooSmall`] if `sink` has no room left.
fn write_head(sink: &mut SliceSink, major_base: u8, arg: u64) -> Result<(), CodecError> {
    if arg < 24 {
        // REMODEL: `u8::try_from(arg)` is an Aeneas-unknown `TryFrom<u64>` axiom.
        // `arg < 24` already fits in `u8`; same bytes as source.
        #[allow(clippy::cast_possible_truncation)]
        let small = arg as u8;
        return sink.write_bytes(&[major_base | small]);
    }
    let be = arg.to_be_bytes();
    // REMODEL: `u8::try_from(arg).is_ok()` — same bound as layer 1.
    if arg <= u64::from(u8::MAX) {
        let byte = be_byte(&be, 7)?;
        return sink.write_bytes(&[major_base | 0x18, byte]);
    }
    // REMODEL: `u16::try_from(arg).is_ok()`; unroll the 2-byte `copy_from_slice`.
    if arg <= u64::from(u16::MAX) {
        return sink.write_bytes(&[major_base | 0x19, be_byte(&be, 6)?, be_byte(&be, 7)?]);
    }
    // REMODEL: `u32::try_from(arg).is_ok()`; unroll the 4-byte `copy_from_slice`.
    if arg <= u64::from(u32::MAX) {
        return sink.write_bytes(&[
            major_base | 0x1A,
            be_byte(&be, 4)?,
            be_byte(&be, 5)?,
            be_byte(&be, 6)?,
            be_byte(&be, 7)?,
        ]);
    }
    sink.write_bytes(&[
        major_base | 0x1B,
        be_byte(&be, 0)?,
        be_byte(&be, 1)?,
        be_byte(&be, 2)?,
        be_byte(&be, 3)?,
        be_byte(&be, 4)?,
        be_byte(&be, 5)?,
        be_byte(&be, 6)?,
        be_byte(&be, 7)?,
    ])
}

/// Writes `bytes` as a canonical CBOR definite-length byte string (major type 2).
///
/// EXTRACT: source is generic over `impl Sink`. This path only has [`SliceSink`].
///
/// # Errors
/// Returns [`CodecError::BufferTooSmall`] if `sink` has no room left.
fn write_bstr(sink: &mut SliceSink, bytes: &[u8]) -> Result<(), CodecError> {
    // REMODEL: `u64::try_from(bytes.len()).map_err(...)` is an Aeneas-unknown
    // `TryFrom<usize>` / `map_err` pair. `usize` fits in `u64` on this crate's
    // targets; LengthOverflow cannot fire here.
    let len = bytes.len() as u64;
    write_head(sink, MAJOR_BSTR, len)?;
    sink.write_bytes(bytes)
}

/// Writes `text` as a canonical CBOR definite-length UTF-8 text string (major type 3).
///
/// EXTRACT: source is generic over `impl Sink` and takes `&str` (`text.as_bytes()`).
/// This path only has [`SliceSink`] and only writes the RFC 9052 context string
/// `Signature1` (ASCII), so the argument is already bytes.
///
/// # Errors
/// Returns [`CodecError::BufferTooSmall`] if `sink` has no room left.
fn write_text(sink: &mut SliceSink, text: &[u8]) -> Result<(), CodecError> {
    // REMODEL: same `u64::try_from` replacement as [`write_bstr`].
    let len = text.len() as u64;
    write_head(sink, MAJOR_TEXT, len)?;
    sink.write_bytes(text)
}

/// Writes a canonical CBOR definite-length array header (major type 4) for `len` items.
///
/// EXTRACT: source is generic over `impl Sink`. This path only has [`SliceSink`].
///
/// # Errors
/// Returns [`CodecError::BufferTooSmall`] if `sink` has no room left.
fn write_array_header(sink: &mut SliceSink, len: u64) -> Result<(), CodecError> {
    write_head(sink, MAJOR_ARRAY, len)
}

/// RFC 9052 `Sig_structure` bytes in a fixed [`MAX_MESSAGE_LEN`]-byte buffer.
///
/// EXTRACT: source `build_sig_structure` returns a prefix `&[u8]` into a
/// caller-supplied `&mut [u8]`. This type owns the filled buffer so the
/// public function does not take `FnOnce` + `&mut [u8; N]` (Binder `&mut [u8; N]` trap).
pub struct SigStructure {
    /// Encoded bytes, zero-padded after [`Self::len`].
    pub buf: [u8; MAX_MESSAGE_LEN],
    /// Number of valid bytes in [`Self::buf`].
    pub len: usize,
}

/// Reconstructs the RFC 9052 `Sig_structure` `["Signature1", protected,
/// external_aad, payload]` into a `[u8; MAX_MESSAGE_LEN]` buffer.
///
/// # Errors
/// Returns [`CoseError::Codec`] wrapping [`CodecError::BufferTooSmall`] if the
/// reconstructed bytes do not fit.
// EXTRACT: source takes `out: &mut [u8]` and returns `out.get(..written_len)`.
// Buffer is built locally and returned filled (Binder close).
pub fn build_sig_structure(
    typ: Typ,
    protected: &[u8],
    payload: &[u8],
) -> Result<SigStructure, CoseError> {
    let mut sink = SliceSink::new();
    write_array_header(&mut sink, 4)?;
    write_text(&mut sink, b"Signature1")?;
    write_bstr(&mut sink, protected)?;
    // EXTRACT: same match as [`external_aad`], with byte literals so Aeneas
    // does not mix a `'static` global slice with `&mut SliceSink`.
    match typ {
        Typ::License => write_bstr(&mut sink, b"kntrl/license/v1")?,
        Typ::Enroll => write_bstr(&mut sink, b"kntrl/enroll/v1")?,
        Typ::Revoke => write_bstr(&mut sink, b"kntrl/revoke/v1")?,
        Typ::TrustUpdate => write_bstr(&mut sink, b"kntrl/trust-update/v1")?,
    }
    write_bstr(&mut sink, payload)?;
    let written_len = sink.len();
    // REMODEL: source is `out.get(..written_len).ok_or(BufferTooSmall)`.
    // A length check avoids re-slicing the owned array (Aeneas bottoms).
    if written_len > MAX_MESSAGE_LEN {
        return Err(CoseError::Codec(CodecError::BufferTooSmall));
    }
    Ok(SigStructure {
        buf: sink.buf,
        len: written_len,
    })
}

/// Authoritative `kid`/`typ` and still-undecoded payload from a `COSE_Sign1`
/// envelope, before signature verification.
///
/// EXTRACT: source `Parsed` in `cose/mod.rs`. `Debug`/`Clone`/`Copy` are
/// omitted so Aeneas does not emit an unused slice `fmt` axiom. Crypto is
/// not represented: this is the pre-dalek view of `verify`.
pub struct Parsed<'a> {
    /// 16-byte key identifier from protected-header key 4.
    pub kid: [u8; 16],
    /// Protected-header `typ` discriminant.
    pub typ: Typ,
    /// Raw payload byte string. Not decoded.
    pub payload: &'a [u8],
}

/// Parses a `COSE_Sign1` envelope up to `Sig_structure`, without verifying
/// the signature.
///
/// Order matches source `verify` before dalek: array-of-4 envelope, protected
/// header `{1,4,100}`, then [`build_sig_structure`]. The 64-byte signature
/// slot is consumed and discarded. The reconstructed `Sig_structure` buffer
/// is discarded; [`CodecError::BufferTooSmall`] stays [`Err`].
///
/// # Errors
/// As [`read_sign1_envelope`], [`decode_protected_header`], and
/// [`build_sig_structure`].
// EXTRACT: verify minus crypto. Source `cose/mod.rs` 221–239 then
// `Ok(Parsed { kid, typ, payload })` at 248. CUT 241–246 (dalek). No pubkey.
// Body composes [`read_sign1_envelope`] + [`decode_protected_header`] +
// [`build_sig_structure`], which is the same byte sequence as inlining
// `Reader::new` / array4 / protected bstr / empty map / payload bstr /
// sig64 / `finish`.
pub fn parse_sign1<'a>(bytes: &'a [u8]) -> Result<Parsed<'a>, CoseError> {
    let envelope = read_sign1_envelope(bytes)?;
    let (kid, typ) = decode_protected_header(envelope.protected)?;
    let _sig_structure = build_sig_structure(typ, envelope.protected, envelope.payload)?;
    Ok(Parsed {
        kid,
        typ,
        payload: envelope.payload,
    })
}

/// Validates a definite-length CBOR array of canonical unsigned integers.
///
/// Returns the array count. Extra bytes after the array are not consumed.
///
/// # Errors
/// As [`Reader::read_array_header`] and [`Reader::read_uint`]: truncated input,
/// wrong major type, non-canonical length, reserved/indefinite additional-info.
// EXTRACT: specialization of `slice_validated_array` (`reader.rs`) with
// `validate_elem = |r| r.read_uint().map(|_| ())`. Source takes `impl FnMut`;
// Charon/Aeneas do not model that callback. The `while seen < count` is kept
// — the bound is the array count decoded from the hostile bytes, not a
// compile-time constant. Not three unrolled `next_map_key` (layer 4 header).
// Source also snapshots `remaining()` and returns the occupied slice; this
// path only needs no-panic of the count loop, so the slice return is dropped.
pub fn slice_validated_uints(buf: &[u8]) -> Result<u64, CodecError> {
    // EXTRACT: public `&[u8]` wrapper (Binder `parse_one` shape).
    let mut reader = Reader::new(buf);
    let count = reader.read_array_header()?;
    let mut seen = 0_u64;
    // REMODEL: Aeneas rejects `?` / `return` inside `while` ("Early returns
    // inside of loops are not supported yet"). Same control-flow as source:
    // stop on the first `read_uint` / `checked_add` error; success is `Ok(count)`.
    // `ok_or` is also an Aeneas-unknown external; `None` is still UnexpectedEnd.
    let mut err: Option<CodecError> = None;
    while seen < count && err.is_none() {
        match reader.read_uint() {
            Ok(_) => match seen.checked_add(1) {
                Some(n) => seen = n,
                None => err = Some(CodecError::UnexpectedEnd),
            },
            Err(e) => err = Some(e),
        }
    }
    match err {
        Some(e) => Err(e),
        None => Ok(count),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_sig_structure, decode_protected_header, parse_sign1, read_array_header, read_bstr,
        read_bstr_fixed_64, read_map_header, read_sign1_envelope, read_uint, slice_validated_uints,
        write_head, CodecError, CoseError, Reader, SliceSink, Typ, AAD_ENROLL, AAD_LICENSE,
        AAD_REVOKE, AAD_TRUST_UPDATE, MAX_MESSAGE_LEN,
    };

    /// Canonical 4-array: empty protected, empty unprotected map, empty payload,
    /// 64-byte signature (all zeros).
    fn minimal_sign1_bytes() -> [u8; 70] {
        let mut bytes = [0_u8; 70];
        bytes[0] = 0x84;
        bytes[1] = 0x40;
        bytes[2] = 0xA0;
        bytes[3] = 0x40;
        bytes[4] = 0x58;
        bytes[5] = 64;
        bytes
    }

    fn expect_envelope_err(buf: &[u8]) -> CoseError {
        match read_sign1_envelope(buf) {
            Ok(_) => panic!("expected envelope error"),
            Err(e) => e,
        }
    }

    /// Canonical `{1: -8, 4: kid-16, 100: typ}` for a given typ discriminant.
    fn canon_header(typ: u8, kid: [u8; 16]) -> [u8; 24] {
        let mut bytes = [0_u8; 24];
        bytes[0] = 0xA3;
        bytes[1] = 0x01;
        bytes[2] = 0x27;
        bytes[3] = 0x04;
        bytes[4] = 0x50;
        bytes[5..21].copy_from_slice(&kid);
        bytes[21] = 0x18;
        bytes[22] = 100;
        bytes[23] = typ;
        bytes
    }

    fn expect_header_err(buf: &[u8]) -> CoseError {
        match decode_protected_header(buf) {
            Ok(_) => panic!("expected protected-header error"),
            Err(e) => e,
        }
    }

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

    /// Encode then decode: `write_head` into an empty sink, `read_head` on the
    /// written prefix recovers `arg`. Covers additional-info 0..=23, 24 (1-byte),
    /// and the 2/4/8-byte smallest-form boundaries. Extra-width `[0x18, 0x05]`
    /// stays `NonCanonicalLength`.
    #[test]
    fn should_round_trip_write_then_read_head() {
        let majors: [u8; 6] = [0x00, 0x20, 0x40, 0x60, 0x80, 0xA0];
        let wide: [u64; 7] = [
            24,
            255,
            256,
            65_535,
            65_536,
            u64::from(u32::MAX),
            u64::from(u32::MAX) + 1,
        ];
        for major in majors {
            for arg in 0_u64..=23 {
                let mut sink = SliceSink::new();
                write_head(&mut sink, major, arg).expect("empty sink has room for a CBOR head");
                assert_eq!(sink.len, 1, "AI 0..=23 is one byte");
                let extra = u8::try_from(arg).expect("arg < 24 fits u8");
                assert_eq!(sink.buf[0], major | extra, "RFC 8949 smallest-form byte");
                let mut reader = Reader::new(&sink.buf[..sink.len]);
                let decoded = reader
                    .read_head(major)
                    .expect("canonical write_head bytes must decode");
                assert_eq!(decoded, arg, "major={major:#x} arg={arg}");
            }
            for arg in wide {
                let mut sink = SliceSink::new();
                write_head(&mut sink, major, arg).expect("empty sink has room for a CBOR head");
                let mut reader = Reader::new(&sink.buf[..sink.len]);
                let decoded = reader
                    .read_head(major)
                    .expect("canonical write_head bytes must decode");
                assert_eq!(decoded, arg, "major={major:#x} arg={arg}");
            }
        }
        assert_eq!(
            read_uint(&[0x18, 0x05]),
            Err(CodecError::NonCanonicalLength)
        );
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

    #[test]
    fn should_decode_canonical_array_header_count_4() {
        assert_eq!(read_array_header(&[0x84]), Ok(4));
        let mut reader = Reader::new(&[0x84]);
        let count = reader
            .read_array_header()
            .expect("array-4 head must decode");
        assert_eq!(count, 4);
    }

    #[test]
    fn should_reject_non_canonical_array_header() {
        // 1-byte length form of 4 (must be additional-info 4).
        assert_eq!(
            read_array_header(&[0x98, 0x04]),
            Err(CodecError::NonCanonicalLength)
        );
    }

    #[test]
    fn should_reject_empty_array_header_input() {
        assert_eq!(read_array_header(&[]), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_reject_major_type_not_array() {
        assert_eq!(read_array_header(&[0x00]), Err(CodecError::TypeMismatch));
        assert_eq!(read_array_header(&[0xA0]), Err(CodecError::TypeMismatch));
    }

    #[test]
    fn should_reject_truncated_array_header() {
        assert_eq!(read_array_header(&[0x98]), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_decode_empty_map_header() {
        assert_eq!(read_map_header(&[0xA0]), Ok(0));
        let mut reader = Reader::new(&[0xA0]);
        let count = reader
            .read_map_header()
            .expect("empty map head must decode");
        assert_eq!(count, 0);
    }

    #[test]
    fn should_decode_minimal_sign1_envelope() {
        let bytes = minimal_sign1_bytes();
        let envelope = read_sign1_envelope(&bytes).expect("minimal envelope must decode");
        assert!(envelope.protected.is_empty());
        assert!(envelope.payload.is_empty());
        assert_eq!(envelope.signature, [0_u8; 64]);
    }

    #[test]
    fn should_reject_sign1_trailing_bytes() {
        let mut bytes = [0_u8; 71];
        bytes[..70].copy_from_slice(&minimal_sign1_bytes());
        bytes[70] = 0x00;
        assert_eq!(
            expect_envelope_err(&bytes),
            CoseError::Codec(CodecError::TrailingBytes)
        );
    }

    #[test]
    fn should_reject_sign1_count_not_4() {
        assert_eq!(expect_envelope_err(&[0x80]), CoseError::MalformedEnvelope);
        assert_eq!(
            expect_envelope_err(&[0x83, 0x40, 0xA0, 0x40]),
            CoseError::MalformedEnvelope
        );
        assert_eq!(expect_envelope_err(&[0x85]), CoseError::MalformedEnvelope);
    }

    #[test]
    fn should_reject_sign1_nonempty_unprotected() {
        let mut bytes = minimal_sign1_bytes();
        bytes[2] = 0xA1;
        assert_eq!(
            expect_envelope_err(&bytes),
            CoseError::NonEmptyUnprotectedHeader
        );
    }

    #[test]
    fn should_reject_truncated_sign1_slots() {
        assert_eq!(
            expect_envelope_err(&[0x84]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            expect_envelope_err(&[0x84, 0x41]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            expect_envelope_err(&[0x84, 0x40]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            expect_envelope_err(&[0x84, 0x40, 0xA0, 0x41]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        // Header claims 64, body is short. Must stay UnexpectedEnd, not WrongLength.
        let mut short_sig = [0_u8; 16];
        short_sig[0] = 0x84;
        short_sig[1] = 0x40;
        short_sig[2] = 0xA0;
        short_sig[3] = 0x40;
        short_sig[4] = 0x58;
        short_sig[5] = 64;
        assert_eq!(
            expect_envelope_err(&short_sig),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
    }

    #[test]
    fn should_decode_canonical_protected_header() {
        let kid = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD,
            0xEE, 0xFF,
        ];
        let cases = [
            (1_u8, Typ::License),
            (2, Typ::Enroll),
            (3, Typ::Revoke),
            (4, Typ::TrustUpdate),
        ];
        for (disc, typ) in cases {
            let bytes = canon_header(disc, kid);
            let (got_kid, got_typ) =
                decode_protected_header(&bytes).expect("canonical header must decode");
            assert_eq!(got_kid, kid);
            assert_eq!(got_typ, typ);
        }
    }

    #[test]
    fn should_reject_protected_header_wrong_map_count() {
        assert_eq!(
            expect_header_err(&[0xA0]),
            CoseError::MalformedProtectedHeader
        );
        assert_eq!(
            expect_header_err(&[0xA2]),
            CoseError::MalformedProtectedHeader
        );
        assert_eq!(
            expect_header_err(&[0xA4]),
            CoseError::MalformedProtectedHeader
        );
    }

    #[test]
    fn should_reject_protected_header_keys_out_of_order() {
        // {4: kid-16, 1: -8, 100: 1} — first key is 4, not 1.
        let mut bytes = [0_u8; 24];
        bytes[0] = 0xA3;
        bytes[1] = 0x04;
        bytes[2] = 0x50;
        bytes[3..19].fill(0x07);
        bytes[19] = 0x01;
        bytes[20] = 0x27;
        bytes[21] = 0x18;
        bytes[22] = 100;
        bytes[23] = 1;
        assert_eq!(
            expect_header_err(&bytes),
            CoseError::MalformedProtectedHeader
        );
    }

    #[test]
    fn should_reject_protected_header_duplicate_key() {
        // {1: -8, 1: -8, 100: 1} — second key does not strictly increase.
        let bytes = [0xA3, 0x01, 0x27, 0x01, 0x27, 0x18, 100, 0x01];
        assert_eq!(
            expect_header_err(&bytes),
            CoseError::Codec(CodecError::NonCanonicalKeyOrder)
        );
    }

    #[test]
    fn should_reject_protected_header_unsupported_alg() {
        let mut bytes = canon_header(1, [0_u8; 16]);
        bytes[2] = 0x26;
        assert_eq!(expect_header_err(&bytes), CoseError::UnsupportedAlgorithm);
        bytes[2] = 0x00;
        assert_eq!(expect_header_err(&bytes), CoseError::UnsupportedAlgorithm);
    }

    #[test]
    fn should_reject_truncated_kid_body() {
        // Map-3, key 1, alg -8, key 4, bstr claims 16, only 2 body bytes.
        let bytes = [0xA3, 0x01, 0x27, 0x04, 0x50, 0xAA, 0xBB];
        assert_eq!(
            expect_header_err(&bytes),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
    }

    #[test]
    fn should_reject_kid_wrong_length() {
        // Complete 8-byte kid offered where 16 is required.
        let mut bytes = [0_u8; 17];
        bytes[0] = 0xA3;
        bytes[1] = 0x01;
        bytes[2] = 0x27;
        bytes[3] = 0x04;
        bytes[4] = 0x48;
        bytes[5..13].fill(0x07);
        bytes[13] = 0x18;
        bytes[14] = 100;
        bytes[15] = 1;
        assert_eq!(
            expect_header_err(&bytes[..16]),
            CoseError::Codec(CodecError::WrongLength)
        );
    }

    #[test]
    fn should_reject_unknown_typ() {
        assert_eq!(
            expect_header_err(&canon_header(0, [0_u8; 16])),
            CoseError::UnknownTyp
        );
        assert_eq!(
            expect_header_err(&canon_header(5, [0_u8; 16])),
            CoseError::UnknownTyp
        );
    }

    #[test]
    fn should_reject_protected_header_trailing_bytes() {
        let mut bytes = [0_u8; 25];
        bytes[..24].copy_from_slice(&canon_header(1, [0_u8; 16]));
        bytes[24] = 0x00;
        assert_eq!(
            expect_header_err(&bytes),
            CoseError::Codec(CodecError::TrailingBytes)
        );
    }

    fn expect_sig_err(typ: Typ, protected: &[u8], payload: &[u8]) -> CoseError {
        match build_sig_structure(typ, protected, payload) {
            Ok(_) => panic!("expected sig-structure error"),
            Err(e) => e,
        }
    }

    fn sig_bytes(got: &super::SigStructure) -> &[u8] {
        match got.buf.get(..got.len) {
            Some(bytes) => bytes,
            None => &[],
        }
    }

    /// Empty protected/payload still produce array-4 + text "Signature1".
    #[test]
    fn should_encode_empty_sig_structure() {
        let got = build_sig_structure(Typ::License, &[], &[]).expect("empty inputs must fit");
        let bytes = sig_bytes(&got);
        assert_eq!(bytes.first().copied(), Some(0x84));
        assert_eq!(bytes.get(1).copied(), Some(0x6A));
        assert_eq!(bytes.get(2..12), Some(b"Signature1".as_slice()));
        assert_eq!(bytes.get(12).copied(), Some(0x40));
        assert_eq!(bytes.get(13).copied(), Some(0x50));
        assert_eq!(bytes.get(14..30), Some(AAD_LICENSE));
        assert_eq!(bytes.get(30).copied(), Some(0x40));
        assert_eq!(bytes.len(), 31);
    }

    #[test]
    fn should_encode_tiny_protected_and_payload() {
        let protected = [0xA0_u8];
        let payload = [0x01_u8, 0x02];
        let got =
            build_sig_structure(Typ::Enroll, &protected, &payload).expect("tiny inputs must fit");
        let bytes = sig_bytes(&got);
        assert_eq!(bytes.first().copied(), Some(0x84));
        assert_eq!(bytes.get(2..12), Some(b"Signature1".as_slice()));
        assert_eq!(bytes.get(12).copied(), Some(0x41));
        assert_eq!(bytes.get(13).copied(), Some(0xA0));
        assert!(
            bytes.windows(2).any(|w| w == payload),
            "payload bytes must appear in the encoding"
        );
    }

    #[test]
    fn should_change_sig_structure_for_each_typ_aad() {
        let license = build_sig_structure(Typ::License, &[], &[]).expect("license aad must fit");
        let enroll = build_sig_structure(Typ::Enroll, &[], &[]).expect("enroll aad must fit");
        let revoke = build_sig_structure(Typ::Revoke, &[], &[]).expect("revoke aad must fit");
        let trust =
            build_sig_structure(Typ::TrustUpdate, &[], &[]).expect("trust-update aad must fit");
        let encodings = [
            sig_bytes(&license),
            sig_bytes(&enroll),
            sig_bytes(&revoke),
            sig_bytes(&trust),
        ];
        for (i, a) in encodings.iter().enumerate() {
            for (j, b) in encodings.iter().enumerate() {
                if i != j {
                    assert_ne!(a, b, "typ {i} and {j} must encode differently");
                }
            }
        }
        assert!(sig_bytes(&license)
            .windows(AAD_LICENSE.len())
            .any(|w| w == AAD_LICENSE));
        assert!(sig_bytes(&enroll)
            .windows(AAD_ENROLL.len())
            .any(|w| w == AAD_ENROLL));
        assert!(sig_bytes(&revoke)
            .windows(AAD_REVOKE.len())
            .any(|w| w == AAD_REVOKE));
        assert!(sig_bytes(&trust)
            .windows(AAD_TRUST_UPDATE.len())
            .any(|w| w == AAD_TRUST_UPDATE));
    }

    #[test]
    fn should_reject_oversized_sig_structure_payload() {
        let payload = [0_u8; MAX_MESSAGE_LEN];
        assert_eq!(
            expect_sig_err(Typ::License, &[], &payload),
            CoseError::Codec(CodecError::BufferTooSmall)
        );
        let protected = [0_u8; MAX_MESSAGE_LEN];
        assert_eq!(
            expect_sig_err(Typ::License, &protected, &[]),
            CoseError::Codec(CodecError::BufferTooSmall)
        );
    }

    /// Canonical Sign1: array-4, protected `{1:-8,4:kid,100:typ}`, empty
    /// unprotected, `payload`, 64-byte zero signature.
    fn fill_sign1(out: &mut [u8], typ: u8, kid: [u8; 16], payload: &[u8]) -> usize {
        let header = canon_header(typ, kid);
        let mut i = 0;
        out[i] = 0x84;
        i += 1;
        out[i] = 0x58;
        i += 1;
        out[i] = 24;
        i += 1;
        out[i..i + 24].copy_from_slice(&header);
        i += 24;
        out[i] = 0xA0;
        i += 1;
        let plen = payload.len();
        if plen < 24 {
            out[i] = 0x40 | u8::try_from(plen).unwrap_or(0);
            i += 1;
        } else if plen <= 255 {
            out[i] = 0x58;
            i += 1;
            out[i] = u8::try_from(plen).unwrap_or(0);
            i += 1;
        } else {
            out[i] = 0x59;
            i += 1;
            out[i] = u8::try_from(plen >> 8).unwrap_or(0);
            i += 1;
            out[i] = u8::try_from(plen & 0xFF).unwrap_or(0);
            i += 1;
        }
        out[i..i + plen].copy_from_slice(payload);
        i += plen;
        out[i] = 0x58;
        i += 1;
        out[i] = 64;
        i += 1;
        i += 64;
        i
    }

    fn expect_parse_err(buf: &[u8]) -> CoseError {
        match parse_sign1(buf) {
            Ok(_) => panic!("expected parse_sign1 error"),
            Err(e) => e,
        }
    }

    #[test]
    fn should_parse_canonical_sign1() {
        let kid = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD,
            0xEE, 0xFF,
        ];
        let payload = [0xAB_u8];
        let mut bytes = [0_u8; 128];
        let n = fill_sign1(&mut bytes, 1, kid, &payload);
        let parsed = parse_sign1(&bytes[..n]).expect("canonical sign1 must parse");
        assert_eq!(parsed.kid, kid);
        assert_eq!(parsed.typ, Typ::License);
        assert_eq!(parsed.payload, payload.as_slice());
    }

    #[test]
    fn should_reject_parse_malformed_envelope() {
        assert_eq!(expect_parse_err(&[0x80]), CoseError::MalformedEnvelope);
        assert_eq!(
            expect_parse_err(&[0x83, 0x40, 0xA0, 0x40]),
            CoseError::MalformedEnvelope
        );
    }

    #[test]
    fn should_reject_parse_nonempty_unprotected() {
        let mut bytes = [0_u8; 128];
        let n = fill_sign1(&mut bytes, 1, [0_u8; 16], &[]);
        bytes[27] = 0xA1;
        assert_eq!(
            expect_parse_err(&bytes[..n]),
            CoseError::NonEmptyUnprotectedHeader
        );
    }

    #[test]
    fn should_reject_parse_bad_protected_header() {
        let mut bytes = [0_u8; 128];
        let n = fill_sign1(&mut bytes, 5, [0_u8; 16], &[]);
        assert_eq!(expect_parse_err(&bytes[..n]), CoseError::UnknownTyp);
        let n = fill_sign1(&mut bytes, 1, [0_u8; 16], &[]);
        bytes[5] = 0x26;
        assert_eq!(
            expect_parse_err(&bytes[..n]),
            CoseError::UnsupportedAlgorithm
        );
        let empty_map_protected = [0x84, 0x41, 0xA0, 0xA0, 0x40, 0x58, 64];
        let mut with_sig = [0_u8; 71];
        with_sig[..7].copy_from_slice(&empty_map_protected);
        assert_eq!(
            expect_parse_err(&with_sig),
            CoseError::MalformedProtectedHeader
        );
    }

    #[test]
    fn should_reject_parse_truncated_and_trailing() {
        assert_eq!(
            expect_parse_err(&[0x84]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        let mut bytes = [0_u8; 128];
        let n = fill_sign1(&mut bytes, 1, [0_u8; 16], &[0xAB]);
        assert_eq!(
            expect_parse_err(&bytes[..n - 10]),
            CoseError::Codec(CodecError::UnexpectedEnd)
        );
        bytes[n] = 0x00;
        assert_eq!(
            expect_parse_err(&bytes[..=n]),
            CoseError::Codec(CodecError::TrailingBytes)
        );
    }

    #[test]
    fn should_reject_parse_oversized_sig_structure() {
        // 4096-byte payload fits the envelope bstr but not Sig_structure.
        let mut bytes = [0_u8; 4193];
        bytes[0] = 0x84;
        bytes[1] = 0x58;
        bytes[2] = 24;
        bytes[3..27].copy_from_slice(&canon_header(1, [0_u8; 16]));
        bytes[27] = 0xA0;
        bytes[28] = 0x59;
        bytes[29] = 0x10;
        bytes[30] = 0x00;
        bytes[4127] = 0x58;
        bytes[4128] = 64;
        assert_eq!(
            expect_parse_err(&bytes),
            CoseError::Codec(CodecError::BufferTooSmall)
        );
    }

    #[test]
    fn should_reject_empty_array_input() {
        assert_eq!(slice_validated_uints(&[]), Err(CodecError::UnexpectedEnd));
    }

    #[test]
    fn should_decode_empty_uint_array() {
        assert_eq!(slice_validated_uints(&[0x80]), Ok(0));
    }

    #[test]
    fn should_decode_uint_array_counts_1_to_3() {
        assert_eq!(slice_validated_uints(&[0x81, 0x00]), Ok(1));
        assert_eq!(slice_validated_uints(&[0x82, 0x00, 0x01]), Ok(2));
        assert_eq!(slice_validated_uints(&[0x83, 0x00, 0x01, 0x02]), Ok(3));
    }

    #[test]
    fn should_reject_truncated_uint_array() {
        assert_eq!(
            slice_validated_uints(&[0x81]),
            Err(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            slice_validated_uints(&[0x82, 0x00]),
            Err(CodecError::UnexpectedEnd)
        );
        assert_eq!(
            slice_validated_uints(&[0x81, 0x18]),
            Err(CodecError::UnexpectedEnd)
        );
    }

    #[test]
    fn should_reject_non_canonical_uint_inside_array() {
        assert_eq!(
            slice_validated_uints(&[0x81, 0x18, 0x05]),
            Err(CodecError::NonCanonicalLength)
        );
        assert_eq!(
            slice_validated_uints(&[0x82, 0x00, 0x18, 0x05]),
            Err(CodecError::NonCanonicalLength)
        );
    }

    #[test]
    fn should_reject_wrong_major_for_uint_array() {
        assert_eq!(
            slice_validated_uints(&[0x00]),
            Err(CodecError::TypeMismatch)
        );
        assert_eq!(
            slice_validated_uints(&[0xA0]),
            Err(CodecError::TypeMismatch)
        );
        assert_eq!(
            slice_validated_uints(&[0x81, 0x40]),
            Err(CodecError::TypeMismatch)
        );
    }
}
