# EXTRACT — `read_uint` path

Source of truth (read-only, not copied as a tree):

- `kntrl-org/api-kntrl-org/kntrl-license-core/src/cbor/reader.rs`
- `kntrl-org/api-kntrl-org/kntrl-license-core/src/cbor/mod.rs`
- `kntrl-org/api-kntrl-org/kntrl-license-core/src/error.rs`

Destination: `rust/src/lib.rs` (single-file crate).

## Provenance

Local checkout: `/Users/dzatona/Sites/MacExchange/kntrl-org/api-kntrl-org`  
HEAD: `206ec5ecab0f579d538eac7897434d9a2f43f058`  
Last commit touching the three files:
`764a0ee8438dfd13001d295c6e4539c74089404f` `feat(license-core): add COSE/Ed25519 wire core`

| File | sha256 |
|---|---|
| `kntrl-license-core/src/cbor/reader.rs` | `c5d35b4a66935b9acf3fcaa97d5cd14035eafe4f1b643110274e0814122f1b73` |
| `kntrl-license-core/src/cbor/mod.rs` | `f4dd9ef0245f10d9bafe8afae7f08ac226657fe699861c34f30359b805f2462b` |
| `kntrl-license-core/src/error.rs` | `74b96d0e2ae382184e7665576379cda6f234ecd6d03e5547118f39467ee64a13` |

## Called from `COSE_Sign1` verify ()

Path: `verify` → `decode_protected_header` → `read_map_header` / `next_map_key` → `read_uint`.

Call sites only (no extra code):

- `kntrl-license-core/src/cose/mod.rs:221` `verify`
- `kntrl-license-core/src/cose/mod.rs:236` `decode_protected_header(protected)`
- `kntrl-license-core/src/cose/mod.rs:95` `decode_protected_header`
- `kntrl-license-core/src/cose/mod.rs:97` `reader.read_map_header()`
- `kntrl-license-core/src/cose/mod.rs:103`, `:109`, `:115` `reader.next_map_key(...)`
- `kntrl-license-core/src/cose/mod.rs:119` `reader.read_uint()` (typ)
- `kntrl-license-core/src/cbor/reader.rs:181` `read_map_header`
- `kntrl-license-core/src/cbor/reader.rs:209` `next_map_key`
- `kntrl-license-core/src/cbor/reader.rs:210` `self.read_uint()`
- `kntrl-license-core/src/cbor/reader.rs:126` `read_uint`

`read_map_header` uses `read_head` with the map major type. The unsigned-integer decoder is `next_map_key` → `read_uint`, and also the direct `read_uint` at `decode_protected_header:119`.

Chosen path: `Reader::take` + `Reader::read_head` + `Reader::read_uint`, plus a
public `&[u8]` wrapper `read_uint` so the theorem is a function of hostile bytes
(Binder `parse_one` shape). No `while` / `for` / recursion on input length.

`Reader<'a>` + `&mut self` extracted. Aeneas erased the lifetime (`structure Reader`
with `buf : Slice U8` and `pos : Usize`).  free-function fallback was not
needed.

## Line map (copied path)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `error.rs` 24–25 `UnexpectedEnd` | `CodecError::UnexpectedEnd` | variant kept |
| `error.rs` 27–28 `TypeMismatch` | `CodecError::TypeMismatch` | variant kept |
| `error.rs` 31–32 `NonCanonicalLength` | `CodecError::NonCanonicalLength` | variant kept |
| `error.rs` 35–36 `IndefiniteLength` | `CodecError::IndefiniteLength` | variant kept |
| `error.rs` 64–65 `DisallowedMajorType` | `CodecError::DisallowedMajorType` | variant kept |
| `mod.rs` 43 `MAJOR_UNSIGNED` | `MAJOR_UNSIGNED` | body identical |
| `mod.rs` 55 `MAJOR_MASK` | `MAJOR_MASK` | body identical |
| `mod.rs` 57 `ADDITIONAL_MASK` | `ADDITIONAL_MASK` | body identical |
| `reader.rs` 16–19 `Reader` fields | `Reader` | `buf`, `pos` identical |
| `reader.rs` 23–26 `new` | `Reader::new` | body identical |
| `reader.rs` 52–57 `take` | `Reader::take` | same `checked_add` + `get`; see REMODEL |
| `reader.rs` 68–118 `read_head` | `Reader::read_head` | same branches 0..=23 / 24 / 25 / 26 / 27 / 28..=30 / indefinite; see REMODEL |
| `reader.rs` 126–128 `read_uint` | `Reader::read_uint` | body identical (`read_head(MAJOR_UNSIGNED)`) |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| Single `lib.rs` instead of `cbor/{mod,reader}.rs` + `error.rs` | tiny proof crate, not the product tree |
| `#![no_std]` / `#![forbid(unsafe_code)]` at crate root | source crate is `no_std`; pin that here |
| `CodecError` without `thiserror` | Charon must not pull a proc-macro dep; variants are still `Copy` |
| Dropped unused `CodecError` variants | path cannot produce them |
| Dropped unused major-type constants | path only needs unsigned / masks |
| Public free `read_uint(&[u8])` | theorem entry point; body is `Reader::new` + method |
| Tests hand-write CBOR vectors | encoder (`write_uint`) is not extracted |

## Remodel (`// REMODEL:`)

First Aeneas translation succeeded but emitted `axiom`s for unknown core
functions (`Option::ok_or`, `Option::copied`, `slice::first`,
`TryFrom<&[u8]> for [u8; N]`, `Result::map_err`, integer `TryFrom`). Those
would have been extra axioms on the theorem. Loop-free remodel, same bytes:

| Source | Remodel | Why |
|---|---|---|
| `x.ok_or(UnexpectedEnd)?` | `match x { Some(v) => v, None => return Err(UnexpectedEnd) }` | drop `ok_or` axiom |
| `take(1)?.first().copied().ok_or(...)` | `get_u8(take(1)?, 0)?` | drop `first`/`copied`/`ok_or` |
| `bytes.try_into().map_err(...)` for `[u8; 2/4/8]` | `get_u8(bytes, i)?` into `from_be_bytes([...])` | drop `try_into`/`map_err` (Binder trap trap) |
| `u8::try_from(value).is_ok()` | `value <= u64::from(u8::MAX)` (and u16/u32) | drop integer `TryFrom` axiom; same bound |
| `#[derive(Debug, Clone, Copy)]` on `Reader` | dropped | drop unused slice `fmt` axiom |

`get_u8` is new. Tests still reject `[0x18, 0x05]` as `NonCanonicalLength` and
round-trip the source uint boundaries.

## Not extracted (after layer 1)

`read_bstr`, `next_map_key`, `slice_validated_array`, `verify`, `Sig_structure`,
unions, `MaybeUninit`, raw pointer casts, ed25519, KNTRL `Typ`, payload, encoder.

---

# EXTRACT — `read_bstr` / `read_bstr_fixed_64` path (layer 2)

Same source files and provenance hashes as the layer-1 table above.
Destination is still `rust/src/lib.rs`.

Called from `COSE_Sign1` verify (protected bstr, payload bstr, signature
`read_bstr_fixed::<64>`). Kid `read_bstr_fixed::<16>` is not extracted here.

Public hostile-bytes wrappers (Binder `parse_one` shape):

- `read_bstr(buf: &[u8]) -> Result<&[u8], CodecError>`
- `read_bstr_fixed_64(buf: &[u8]) -> Result<[u8; 64], CodecError>`

Order matches the source: `read_head(MAJOR_BSTR)` → convert length → `take(len)`
→ (fixed-64 only) `try_from`. Length is **not** checked against `N` before
`take`, so a truncated 64-byte claim stays `UnexpectedEnd`, not `WrongLength`.

No `while` / `for` / recursion on input length. `take(len)` is the same
`checked_add` + `slice::get` as layer 1 (already no-panic for any `usize`).
The 4096 `MAX_MESSAGE_LEN` cap was **not** applied: Aeneas did not turn
`take` of an input length into a loop.

## Line map (layer 2)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `error.rs` 67–68 `LengthOverflow` | `CodecError::LengthOverflow` | variant kept; appended after layer-1 variants |
| `error.rs` 50–51 `WrongLength` | `CodecError::WrongLength` | variant kept; appended after layer-1 variants |
| `mod.rs` 47 `MAJOR_BSTR` | `MAJOR_BSTR` | body identical (`0x40`) |
| `reader.rs` 137–142 `read_bstr` | `Reader::read_bstr` | same `read_head` + convert + `take`; see REMODEL |
| `reader.rs` 149–152 `read_bstr_fixed::<N>` | `Reader::read_bstr_fixed_64` | monomorphized N=64; `take` then `try_from` |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| `read_bstr_fixed_64` instead of `read_bstr_fixed::<N>` | only the COSE_Sign1 signature width is in this path; kid N=16 is later |
| Public free `read_bstr(&[u8])` / `read_bstr_fixed_64(&[u8])` | theorem entry points; body is `Reader::new` + method |

## Remodel (`// REMODEL:`)

| Source | Remodel | Error change |
|---|---|---|
| `usize::try_from(len).map_err(\|_\| LengthOverflow)` | `if len > usize::MAX as u64 { LengthOverflow } else { len as usize }` | **none** — same overflow predicate |
| `<[u8; N]>::try_from(bytes).map_err(\|_\| WrongLength)` | `match <[u8; 64]>::try_from(bytes) { Ok(a) => Ok(a), Err(_) => Err(WrongLength) }` | **none** — same wrong-length predicate |

Aeneas extracted the `as usize` bound check as `lift (UScalar.cast .Usize val)`.
`UScalar.cast` is a pure truncate/zero-extend (never `fail`). The array
`try_from` is the Aeneas stdlib model `TryFromArrayCopySlice.try_from`, which
always returns `ok (Ok arr)` or `ok (Err ())`.

No `MAX_MESSAGE_LEN` cap. Inputs that the source accepts as a complete bstr
still succeed; truncated short bodies stay `UnexpectedEnd`; non-canonical
stays `Err`.

## Not extracted (after layer 2)

`read_bstr_fixed::<16>` (kid), `next_map_key`, `slice_validated_array`,
`verify`, `parse_sign1`, `Sig_structure`, unions, `MaybeUninit`, raw pointer
casts, ed25519, KNTRL `Typ`, payload, encoder.

---

# EXTRACT — `read_sign1_envelope` path (layer 3)

Same CBOR source files and provenance hashes as the layer-1 table above, plus
`kntrl-license-core/src/cose/mod.rs` (hashed below). Destination is still
`rust/src/lib.rs`.

## Provenance (layer 3)

Local checkout: `/Users/dzatona/Sites/MacExchange/kntrl-org/api-kntrl-org`  
HEAD: `206ec5ecab0f579d538eac7897434d9a2f43f058`  
Last commit touching `kntrl-license-core/src/cose/mod.rs`:
`0a2f9a176ec041aaf38c4775473cd8e41406867a` `docs: fix rustdoc private and feature-gated links`

| File | sha256 |
|---|---|
| `kntrl-license-core/src/cose/mod.rs` | `8abf884d28ee63c28ff5f85aba99e74cc662c52462741d180d9ca20a2e0a7a28` |

Control-flow source of `read_sign1_envelope` is `verify` lines 221–234
(quoted; read-only, not copied as a tree):

```
pub fn verify<'a>(bytes: &'a [u8], expected_pubkey: &[u8; 32]) -> Result<Parsed<'a>, CoseError> {
    let mut reader = Reader::new(bytes);
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
    let signature_bytes = reader.read_bstr_fixed::<64>()?;
    reader.finish()?;
```

`?` on `CodecError` in this `Result<_, CoseError>` function uses
`From<CodecError> for CoseError` (`error.rs` `CoseError::Codec(#[from]
CodecError)`), so truncated slots become `CoseError::Codec(UnexpectedEnd)`
and `finish` becomes `CoseError::Codec(TrailingBytes)`. Count ≠ 4 and a
nonempty unprotected map stay the bare `CoseError` variants.

Called from `COSE_Sign1` verify as the array-of-4 envelope skeleton, **before**
`decode_protected_header` and `build_sig_structure`. Kid / Typ / protected-map
contents are not extracted here.

Public hostile-bytes wrappers (Binder `parse_one` shape):

- `read_array_header(buf: &[u8]) -> Result<u64, CodecError>`
- `read_map_header(buf: &[u8]) -> Result<u64, CodecError>`
- `read_sign1_envelope(buf: &[u8]) -> Result<Envelope, CoseError>`

`read_array_header` / `read_map_header` / `read_bstr` stay on `CodecError`.
Only the envelope wrapper returns `CoseError`, matching source `verify`.

`Envelope` holds `protected: &[u8]`, `payload: &[u8]`, `signature: [u8; 64]`.
It is not a source type: source `verify` keeps those as locals and then
decodes the protected map. This crate stops before that decode.

Control flow is the source order, not a synthetic “array header + empty map +
finish” without the bstrs:

`read_array_header` == 4 → protected `read_bstr` → `read_map_header` == 0 →
payload `read_bstr` → `read_bstr_fixed_64` → `finish`.

No `while` / `for` / recursion on input length. `take(len)` is still the
layer-1 `checked_add` + `slice::get`.

## Line map (layer 3)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `error.rs` 61–62 `TrailingBytes` | `CodecError::TrailingBytes` | variant kept; required by `finish` |
| `error.rs` 78–91 `CoseError` | `CoseError::{Codec, MalformedEnvelope, NonEmptyUnprotectedHeader}` | only variants this path produces |
| `error.rs` 81 `#[from] CodecError` | `impl From<CodecError> for CoseError` | same wrap; thiserror dropped |
| `mod.rs` 51 `MAJOR_ARRAY` | `MAJOR_ARRAY` | body identical (`0x80`) |
| `mod.rs` 53 `MAJOR_MAP` | `MAJOR_MAP` | body identical (`0xA0`) |
| `reader.rs` 30–32 `is_empty` | `Reader::is_empty` | body identical (`pos == buf.len()`) |
| `reader.rs` 44–46 `finish` | `Reader::finish` | same `TrailingBytes`; braces only |
| `reader.rs` 172–174 `read_array_header` | `Reader::read_array_header` | body identical (`read_head(MAJOR_ARRAY)`) |
| `reader.rs` 181–183 `read_map_header` | `Reader::read_map_header` | body identical (`read_head(MAJOR_MAP)`) |
| `cose/mod.rs` 221–234 | `read_sign1_envelope` | array4 + two bstrs + empty map + sig64 + finish; returns `CoseError` |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| `CoseError` without `MalformedProtectedHeader` / alg / typ / dalek variants | path cannot produce them |
| `From<CodecError>` written by hand | source is thiserror `#[from]`; Charon must not pull a proc-macro dep |
| Public free `read_array_header` / `read_map_header` / `read_sign1_envelope` | theorem entry points; methods stay on `Reader` |
| `Envelope` struct | source uses locals; theorem needs a named `Ok` payload |
| No `decode_protected_header` / `build_sig_structure` / dalek | later layers |

Source `verify` turns `finish`’s `CodecError::TrailingBytes` into
`CoseError::Codec(TrailingBytes)` via `From`. This crate does the same:
`read_sign1_envelope` returns `Result<Envelope, CoseError>`, so `?` wraps.
Truncated bstr slots stay inner `CodecError::UnexpectedEnd` (not
`WrongLength` on a short signature body), surfaced as
`CoseError::Codec(UnexpectedEnd)`.

## Remodel (`// REMODEL:`)

None on this path beyond the layer-1/2 remodels already in `read_head` /
`read_bstr` / `read_bstr_fixed_64`. `Envelope` omits `Debug`/`Clone`/`Copy`
for the same unused slice-`fmt` reason as `Reader`.

## Not extracted (after layer 3)

`read_bstr_fixed::<16>` (kid), `next_map_key`, `decode_protected_header`,
`Typ::from_u64`, `slice_validated_array`, `verify`, `parse_sign1`,
`Sig_structure`, unions, `MaybeUninit`, raw pointer casts, ed25519, KNTRL
`Typ` meaning, payload decode, encoder. Unused `CoseError` variants
(`MalformedProtectedHeader`, `UnsupportedAlgorithm`, `UnknownTyp`,
`SignatureInvalid`, `InvalidPublicKey`, `InvalidSigningKey`).
