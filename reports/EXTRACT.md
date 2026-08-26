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

## Not extracted

`read_bstr`, `next_map_key`, `slice_validated_array`, `verify`, `Sig_structure`,
unions, `MaybeUninit`, raw pointer casts, ed25519, KNTRL `Typ`, payload, encoder.
