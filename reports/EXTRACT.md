# EXTRACT — `read_uint` path

Source of truth (read-only, not copied as a tree):

- `kntrl-org/api-kntrl-org/kntrl-license-core/src/cbor/reader.rs`
- `kntrl-org/api-kntrl-org/kntrl-license-core/src/cbor/mod.rs`
- `kntrl-org/api-kntrl-org/kntrl-license-core/src/error.rs`

Destination: `rust/src/lib.rs` (single-file crate).

Chosen path: `Reader::take` + `Reader::read_head` + `Reader::read_uint`, plus a
public `&[u8]` wrapper `read_uint` so the theorem is a function of hostile bytes
(Binder `parse_one` shape). No `while` / `for` / recursion on input length.

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
| `reader.rs` 16–19 `Reader` | `Reader` | fields identical |
| `reader.rs` 23–26 `new` | `Reader::new` | body identical |
| `reader.rs` 52–57 `take` | `Reader::take` | body identical |
| `reader.rs` 68–118 `read_head` | `Reader::read_head` | body identical |
| `reader.rs` 126–128 `read_uint` | `Reader::read_uint` | body identical |

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

No `// REMODEL:` yet: `Reader<'a>` + `&mut self` is the assigned candidate.
 fallback (cursor returned as `usize`, no `Reader`) is reserved for one
Aeneas failure on the lifetime.

## Not extracted

`read_bstr`, `next_map_key`, `slice_validated_array`, `verify`, `Sig_structure`,
unions, `MaybeUninit`, raw pointer casts, ed25519, KNTRL `Typ`, payload, encoder.
