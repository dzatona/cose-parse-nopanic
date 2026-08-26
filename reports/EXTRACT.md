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

## Called from `COSE_Sign1` verify

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
with `buf : Slice U8` and `pos : Usize`). The free-function fallback was not
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
| `bytes.try_into().map_err(...)` for `[u8; 2/4/8]` | `get_u8(bytes, i)?` into `from_be_bytes([...])` | drop `try_into`/`map_err` (Binder trap) |
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

---

# EXTRACT — `decode_protected_header` path (layer 4)

Same CBOR source files and provenance hashes as the layer-1 table above, plus
`kntrl-license-core/src/cose/mod.rs` (hashed in layer 3) and
`kntrl-license-core/src/types.rs` (hashed below). Destination is still
`rust/src/lib.rs`.

## Provenance (layer 4)

Local checkout: `/Users/dzatona/Sites/MacExchange/kntrl-org/api-kntrl-org`  
HEAD: `206ec5ecab0f579d538eac7897434d9a2f43f058`  
Last commit touching `cose/mod.rs` / `types.rs` / `reader.rs`:
`0a2f9a176ec041aaf38c4775473cd8e41406867a` `docs: fix rustdoc private and feature-gated links`

| File | sha256 |
|---|---|
| `kntrl-license-core/src/cose/mod.rs` | `8abf884d28ee63c28ff5f85aba99e74cc662c52462741d180d9ca20a2e0a7a28` |
| `kntrl-license-core/src/types.rs` | `0abf46e07c4ed3f20345528d9d97d9f54877aaa76af77629a186d53cbaf8bad5` |
| `kntrl-license-core/src/cbor/reader.rs` | `c5d35b4a66935b9acf3fcaa97d5cd14035eafe4f1b643110274e0814122f1b73` |
| `kntrl-license-core/src/cbor/mod.rs` | `f4dd9ef0245f10d9bafe8afae7f08ac226657fe699861c34f30359b805f2462b` |
| `kntrl-license-core/src/error.rs` | `74b96d0e2ae382184e7665576379cda6f234ecd6d03e5547118f39467ee64a13` |

`Typ::from_u64` span (`types.rs` 47–55):

```
    pub const fn from_u64(value: u64) -> Result<Self, CodecError> {
        match value {
            1 => Ok(Self::License),
            2 => Ok(Self::Enroll),
            3 => Ok(Self::Revoke),
            4 => Ok(Self::TrustUpdate),
            _ => Err(CodecError::InvalidEnumValue),
        }
    }
```

Control-flow source of `decode_protected_header` is `cose/mod.rs` 95–122
(quoted; read-only, not copied as a tree):

```
fn decode_protected_header(bytes: &[u8]) -> Result<([u8; 16], Typ), CoseError> {
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
    reader.read_fixed_byte(ALG_EDDSA_BYTE).map_err(|_bad_alg| CoseError::UnsupportedAlgorithm)?;

    let key = reader.next_map_key(&mut last_key)?;
    if key != 4 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    let kid = reader.read_bstr_fixed::<16>()?;

    let key = reader.next_map_key(&mut last_key)?;
    if key != 100 {
        return Err(CoseError::MalformedProtectedHeader);
    }
    let typ = Typ::from_u64(reader.read_uint()?).map_err(|_unknown| CoseError::UnknownTyp)?;

    reader.finish()?;
    Ok((kid, typ))
}
```

Three `next_map_key` calls, not a `while` over the pair count. That unroll is
source syntax and the one allowed remodel. No generic map walker and no
`slice_validated_array`.

Called from `COSE_Sign1` `verify` after the array-of-4 envelope and `finish`,
before `build_sig_structure`. This crate does **not** compose envelope +
header into `parse_sign1`.

Public hostile-bytes wrapper (Binder `parse_one` shape):

- `decode_protected_header(bytes: &[u8]) -> Result<([u8; 16], Typ), CoseError>`

`read_bstr_fixed_16` / `read_fixed_byte` / `next_map_key` stay methods on
`Reader`. `Typ::from_u64` is the source match `1..=4` only. Other enums
(`AUD`, `VER`, `EntitlementState`, …) are not extracted.

No `while` / `for` / recursion on input length. Pair count is checked
`== 3` then three straight-line reads.

## Line map (layer 4)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `error.rs` 47 `NonCanonicalKeyOrder` | `CodecError::NonCanonicalKeyOrder` | variant kept; appended |
| `error.rs` 58 `InvalidEnumValue` | `CodecError::InvalidEnumValue` | variant kept; produced by `Typ::from_u64` |
| `error.rs` 88 `MalformedProtectedHeader` | `CoseError::MalformedProtectedHeader` | variant kept; appended |
| `error.rs` 94 `UnsupportedAlgorithm` | `CoseError::UnsupportedAlgorithm` | variant kept; appended |
| `error.rs` 97 `UnknownTyp` | `CoseError::UnknownTyp` | variant kept; appended |
| `mod.rs` 45 `MAJOR_NEGATIVE` | `MAJOR_NEGATIVE` | body identical (`0x20`) |
| `mod.rs` 61 `ALG_EDDSA_BYTE` | `ALG_EDDSA_BYTE` | body identical (`MAJOR_NEGATIVE \| 0x07` = `0x27`) |
| `types.rs` 19–28 `Typ` | `Typ` | four variants; `Hash` dropped |
| `types.rs` 47–55 `Typ::from_u64` | `Typ::from_u64` | body identical (`1..=4` / `InvalidEnumValue`) |
| `reader.rs` 194–197 `read_fixed_byte` | `Reader::read_fixed_byte` | same expected-byte check; see REMODEL |
| `reader.rs` 209–218 `next_map_key` | `Reader::next_map_key` | same strictly-ascending check; see REMODEL |
| `reader.rs` 149–152 `read_bstr_fixed::<16>` | `Reader::read_bstr_fixed_16` | monomorphized N=16; `take` then `try_from` |
| `cose/mod.rs` 95–122 | `decode_protected_header` | public; three `next_map_key`; see REMODEL |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| `decode_protected_header` is `pub` | source is crate-private; theorem needs a `&[u8]` entry point |
| `read_bstr_fixed_16` instead of `read_bstr_fixed::<N>` | only kid width 16 is on this path |
| `Typ` without `Hash` / `to_u64` / other enums | path only needs `from_u64` |
| New `CoseError` variants without dalek ones | path cannot produce `SignatureInvalid` / key errors |
| No `parse_sign1` composition | envelope + header stay separate until after layer 5 |

Source `decode_protected_header` turns `read_fixed_byte` failure into
`UnsupportedAlgorithm` (including a truncated alg byte) and
`Typ::from_u64` `InvalidEnumValue` into `UnknownTyp`. This crate does the
same via `match` instead of `map_err`. `next_map_key` `NonCanonicalKeyOrder`
and `read_bstr_fixed_16` / `finish` failures wrap as `CoseError::Codec`
via `From`. Truncated kid body stays inner `CodecError::UnexpectedEnd`
(not `WrongLength`).

## Remodel (`// REMODEL:`)

| Source | Remodel | Error change |
|---|---|---|
| `take(1)?.first().copied().ok_or(UnexpectedEnd)` in `read_fixed_byte` | `get_u8(take(1)?, 0)?` | **none** — same bounds check as layer 1 |
| `if let Some(last) = *last_key && key <= last` | nested `if let` / `if` | **none** — same strictly-ascending predicate |
| `read_fixed_byte(...).map_err(\|_bad_alg\| UnsupportedAlgorithm)` | `match` → `UnsupportedAlgorithm` on `Err(_)` | **none** — still maps every `read_fixed_byte` error |
| `Typ::from_u64(...).map_err(\|_unknown\| UnknownTyp)` | `match` → `UnknownTyp` on `Err(_)` | **none** — still maps `InvalidEnumValue` |
| `<[u8; 16]>::try_from(bytes).map_err(...)` | `match` `try_from` | **none** — same WrongLength; take-then-try_from |

The unroll of three `next_map_key` calls is source syntax, not a second
remodel. No `MAX_MESSAGE_LEN` cap. No generic map walker.

## Not extracted (after layer 4)

`slice_validated_array`, `verify`, `parse_sign1`, `Sig_structure` /
`Sink` / `SliceSink` / `write_*` / `external_aad`, unions, `MaybeUninit`,
raw pointer casts, ed25519, KNTRL `Typ` meaning, payload decode, encoder.
Unused `CoseError` variants (`SignatureInvalid`, `InvalidPublicKey`,
`InvalidSigningKey`).

---

# EXTRACT — `build_sig_structure` path (layer 5)

Same CBOR source files and provenance hashes as the layer-1 table above, plus
`kntrl-license-core/src/cose/mod.rs` (hashed in layer 3) and
`kntrl-license-core/src/domain.rs` (hashed below). Destination is still
`rust/src/lib.rs`.

## Provenance (layer 5)

Local checkout: `/Users/dzatona/Sites/MacExchange/kntrl-org/api-kntrl-org`  
HEAD: `206ec5ecab0f579d538eac7897434d9a2f43f058`  
Last commit touching `cose/mod.rs` / `cbor/mod.rs` / `domain.rs`:
`0a2f9a176ec041aaf38c4775473cd8e41406867a` `docs: fix rustdoc private and feature-gated links`

| File | sha256 |
|---|---|
| `kntrl-license-core/src/cose/mod.rs` | `8abf884d28ee63c28ff5f85aba99e74cc662c52462741d180d9ca20a2e0a7a28` |
| `kntrl-license-core/src/cbor/mod.rs` | `f4dd9ef0245f10d9bafe8afae7f08ac226657fe699861c34f30359b805f2462b` |
| `kntrl-license-core/src/domain.rs` | `e58047017e5c06463095794700d273a302d6197cdfcf041d0782c2a5d7dee059` |
| `kntrl-license-core/src/error.rs` | `74b96d0e2ae382184e7665576379cda6f234ecd6d03e5547118f39467ee64a13` |

Control-flow source of `build_sig_structure` is `cose/mod.rs` 134–149
(quoted; read-only, not copied as a tree):

```
fn build_sig_structure<'buf>(
    typ: Typ,
    protected: &[u8],
    payload: &[u8],
    out: &'buf mut [u8],
) -> Result<&'buf [u8], CoseError> {
    let written_len = {
        let mut sink = SliceSink::new(out);
        write_array_header(&mut sink, 4)?;
        write_text(&mut sink, "Signature1")?;
        write_bstr(&mut sink, protected)?;
        write_bstr(&mut sink, external_aad(typ))?;
        write_bstr(&mut sink, payload)?;
        sink.len()
    };
    out.get(..written_len).ok_or(CoseError::Codec(CodecError::BufferTooSmall))
}
```

`external_aad` (`domain.rs` 24–30) is a match on `Typ` to four ASCII literals.
Product meaning of each token is outside the no-panic claim.

Called from `COSE_Sign1` `verify` after `decode_protected_header`, before dalek.
This crate does **not** compose envelope + header + sig-structure into
`parse_sign1`.

Public entry point (Binder `parse_one` shape, Binder buffer-by-value):

- `build_sig_structure(typ, protected, payload) -> Result<SigStructure, CoseError>`

`SigStructure` owns `[u8; MAX_MESSAGE_LEN]` plus the written length. Source
takes `out: &mut [u8]` and returns a prefix slice.

No `while` / `for` / recursion on input length. `copy_from_slice` is the
Aeneas stdlib primitive (`ok src` iff dest/src lengths equal, else `fail`),
not a loop. The allowed remodel puts that copy behind `dest.len() != bytes.len()`
→ `BufferTooSmall`.

A cap of each input bstr at 4096 does **not** imply the encoded structure
fits (headers + `"Signature1"` + aad + both bstrs). Source already returns
`BufferTooSmall`; the theorem treats that as `ok(Err)`.

## Line map (layer 5)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `error.rs` 22 `BufferTooSmall` | `CodecError::BufferTooSmall` | variant kept; appended |
| `cose/mod.rs` 46 `MAX_MESSAGE_LEN` | `MAX_MESSAGE_LEN` | body identical (`4096`) |
| `mod.rs` 49 `MAJOR_TEXT` | `MAJOR_TEXT` | body identical (`0x60`) |
| `domain.rs` 13–19 `AAD_*` | `AAD_LICENSE` / `AAD_ENROLL` / `AAD_REVOKE` / `AAD_TRUST_UPDATE` | body identical |
| `domain.rs` 24–30 `external_aad` | `external_aad` | body identical (match only) |
| `mod.rs` 85–88 `SliceSink` fields | `SliceSink` | owned `[u8; 4096]` instead of `&mut [u8]`; see EXTRACT |
| `mod.rs` 117–123 `write_bytes` | `SliceSink::write_bytes` | same `checked_add` + `get_mut` + copy; see REMODEL |
| `mod.rs` 138–166 `write_head` | `write_head` | same smallest-form branches; see REMODEL |
| `mod.rs` 181–186 `write_bstr` | `write_bstr` | concrete `SliceSink`; see REMODEL |
| `mod.rs` 193–199 `write_text` | `write_text` | takes `&[u8]`; only `"Signature1"` |
| `mod.rs` 207–209 `write_array_header` | `write_array_header` | body identical (`write_head(MAJOR_ARRAY, len)`) |
| `cose/mod.rs` 134–149 | `build_sig_structure` | public; returns owned `SigStructure` |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| No `Sink` trait / no `Vec` sink | Charon/Aeneas choke on the trait; only `SliceSink` is on verify |
| `SliceSink` owns `[u8; 4096]` | Binder: Binder closed `FnOnce` + `&mut [u8; N]` with buffer-by-value |
| `build_sig_structure` does not take `out: &mut [u8]` | same Binder close; returns `SigStructure` |
| `write_*` take `&mut SliceSink`, not `impl Sink` | concrete sink only |
| `write_text` takes `&[u8]` | source `&str` / `as_bytes` was an unknown-external axiom |
| AAD written as byte literals in `build_sig_structure` | same match as `external_aad`; avoids `'static` global + `&mut` sink |
| `external_aad` / `AAD_*` still present | match-only public API; tests compare encodings |
| No `parse_sign1` composition | finale after this layer |

## Remodel (`// REMODEL:`)

| Source | Remodel | Error change |
|---|---|---|
| `x.ok_or(BufferTooSmall)?` | `match` → `BufferTooSmall` | **none** |
| `dest.copy_from_slice(bytes)` unconstrained | `if dest.len() != bytes.len() { BufferTooSmall }` then copy | **none** on the verify path — lengths already match after `get_mut(len..len+n)` |
| `u8::try_from(arg)` / `uN::try_from(arg).is_ok()` | `arg < 24` / `arg <= u64::from(uN::MAX)` | **none** — same bounds as layer 1 |
| 2/4/8-byte `copy_from_slice` in `write_head` | unrolled `be_byte` into a stack array | **none** |
| `u64::try_from(bytes.len())` | `bytes.len() as u64` | LengthOverflow cannot fire; `usize` fits in `u64` |
| `out.get(..written_len).ok_or(BufferTooSmall)` | `if written_len > MAX_MESSAGE_LEN` | **none** — `len` only advances after a successful `get_mut` |

Aeneas did **not** lower `copy_from_slice` to a loop. First extraction of
borrowed `&mut [u8; 4096]` failed (see `reports/AENEAS.md`); the owned-array
remodel is the one allowed Binder close. No second copy remodel. No loop
lemma. No `STOP.md`.

## Not extracted (after layer 5)

`slice_validated_array`, `verify`, `parse_sign1`, unions, `MaybeUninit`,
raw pointer casts, ed25519 / dalek, KNTRL `Typ` meaning, payload decode.
Unused `CoseError` variants (`SignatureInvalid`, `InvalidPublicKey`,
`InvalidSigningKey`). The `Sink` trait and `Vec` sink.

---

# EXTRACT — `parse_sign1` path (finale)

Same source files and provenance hashes as the layer-5 table above.
Destination is still `rust/src/lib.rs`. `parse_sign1` is not in the source:
it is the `// EXTRACT:` wrapper `verify` minus crypto.

## Provenance (finale)

Local checkout: `/Users/dzatona/Sites/MacExchange/kntrl-org/api-kntrl-org`  
HEAD: `206ec5ecab0f579d538eac7897434d9a2f43f058`  
Last commit touching `cose/mod.rs`:
`0a2f9a176ec041aaf38c4775473cd8e41406867a` `docs: fix rustdoc private and feature-gated links`

| File | sha256 |
|---|---|
| `kntrl-license-core/src/cose/mod.rs` | `8abf884d28ee63c28ff5f85aba99e74cc662c52462741d180d9ca20a2e0a7a28` |

Control-flow source of `parse_sign1` is `verify` lines 221–239 plus the
`Ok(Parsed { kid, typ, payload })` at 248. CUT 241–246 (dalek). Quoted
read-only, not copied as a tree:

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

    let (kid, typ) = decode_protected_header(protected)?;

    let mut sig_buf = [0_u8; MAX_MESSAGE_LEN];
    let sig_structure = build_sig_structure(typ, protected, payload, &mut sig_buf)?;

    let verifying_key = VerifyingKey::from_bytes(expected_pubkey)
        .map_err(|_bad_key| CoseError::InvalidPublicKey)?;
    let signature = Signature::from_bytes(&signature_bytes);
    verifying_key
        .verify_strict(sig_structure, &signature)
        .map_err(|_bad_signature| CoseError::SignatureInvalid)?;

    Ok(Parsed { kid, typ, payload })
}
```

CUT (not in `parse_sign1`, not in the theorem):

| Source | Why cut |
|---|---|
| 221 `expected_pubkey: &[u8; 32]` | no pubkey |
| 241–242 `VerifyingKey::from_bytes` | dalek |
| 243 `Signature::from_bytes` | dalek |
| 244–246 `verify_strict` | dalek |

Public hostile-bytes wrapper (Binder `parse_one` shape):

- `parse_sign1(bytes: &[u8]) -> Result<Parsed, CoseError>`

Body composes already-extracted helpers. That is byte-equivalent to
inlining `Reader::new` / array4 / protected bstr / empty map / payload
bstr / sig64 / `finish`:

1–7. `read_sign1_envelope` = source 222–234
8. `decode_protected_header` = source 236
9. `build_sig_structure` = source 238–239 (owned buffer; written bytes discarded; `BufferTooSmall` stays `Err`)
10. `Ok(Parsed { kid, typ, payload })` = source 248

Signature bytes are consumed inside `read_sign1_envelope` and discarded.
They are not skipped: `finish` would otherwise see the 64-byte tail.
`build_sig_structure` is not skipped: an envelope whose payload fits the
bstr but not `[u8; 4096]` still returns `Codec(BufferTooSmall)`.

`Parsed` fields match source (`kid: [u8; 16]`, `typ: Typ`,
`payload: &'a [u8]`). Product `Typ` meaning is outside the theorem.

No `while` / `for` / recursion on input length. No dalek.

## Line map (finale)

| Source | Crate (`rust/src/lib.rs`) | Notes |
|---|---|---|
| `cose/mod.rs` 55–64 `Parsed` | `Parsed` 811–818 | same three fields; `Debug`/`Clone`/`Copy` omitted |
| `cose/mod.rs` 221–234 | `read_sign1_envelope` 526–545 | already extracted; called from `parse_sign1` |
| `cose/mod.rs` 236 | `parse_sign1` 839 | `decode_protected_header(envelope.protected)` |
| `cose/mod.rs` 238–239 | `parse_sign1` 840 | `build_sig_structure`; no caller `out` buffer |
| `cose/mod.rs` 241–246 | — | CUT dalek |
| `cose/mod.rs` 248 | `parse_sign1` 841–845 | `Ok(Parsed { kid, typ, payload })` |
| `cose/mod.rs` 221–239 + 248 | `parse_sign1` 837–846 | wrapper; no pubkey |

## Intentional diffs (`// EXTRACT:`)

| Crate | Why |
|---|---|
| `parse_sign1` does not exist in source | `verify` minus crypto; theorem entry point |
| No `expected_pubkey` argument | crypto is outside the parse |
| Composes three helpers instead of inlining the reader | same bytes as 222–234; helpers already proved |
| `build_sig_structure` returns owned `SigStructure` | already extracted (Binder buffer-by-value); discarded |
| `Parsed` without `Debug`/`Clone`/`Copy` | same unused slice-`fmt` reason as `Envelope` |
| No dalek / `verify_strict` / `VerifyingKey` | CUT 241–246 |

## Remodel (`// REMODEL:`)

None on this wrapper beyond remodeled helpers already documented in
layers 1–5. Composition does not change error predicates: malformed
envelope, nonempty unprotected, bad header, truncated, trailing, and
`BufferTooSmall` stay the same variants.

## Not extracted (after finale)

`slice_validated_array`, full `verify` (dalek), unions, `MaybeUninit`,
raw pointer casts, ed25519, KNTRL `Typ` meaning, payload decode.
Unused `CoseError` variants (`SignatureInvalid`, `InvalidPublicKey`,
`InvalidSigningKey`). The `Sink` trait and `Vec` sink.
