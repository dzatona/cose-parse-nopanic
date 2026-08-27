# PROOF — `read_sign1_envelope_no_panic` (layer 3)

## Claim

For every hostile byte slice, the extracted `COSE_Sign1` array-of-4 envelope
skeleton returns in the Aeneas `ok` monad. It does **not** prove RFC 8949 or
RFC 9052 correctness, and it does **not** decode the protected-header map.

```
∀ buf, ∃ r, read_array_header buf = ok r
∀ buf, ∃ r, read_map_header buf = ok r
∀ buf, ∃ r, read_sign1_envelope buf = ok r
```

`ok (Result.Ok Envelope)` is the four slots (raw protected bstr, raw payload
bstr, 64-byte signature). `ok (Result.Err CoseError)` is a normal rejection
(count ≠ 4 → `MalformedEnvelope`; nonempty unprotected map →
`NonEmptyUnprotectedHeader`; truncated / non-canonical / trailing bytes →
`Codec(CodecError)`, including `UnexpectedEnd` on a truncated signature and
`WrongLength` after a complete short signature). `fail` would be panic /
OOB / unwrap.

Theorems in `lean/NoPanic.lean`:

- `NoPanic.read_array_header_no_panic`
- `NoPanic.read_map_header_no_panic`
- `NoPanic.read_sign1_envelope_no_panic` — composition target

No `sorry`. Layer-1 `NoPanic.read_uint_no_panic` and layer-2
`NoPanic.read_bstr_no_panic` / `NoPanic.read_bstr_fixed_64_no_panic` are
unchanged and still hold.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. Ran against crate **0.8.0** (CoseError extract). Charon compile
line below is `cbor_nopanic v0.8.0`, matching `rust/Cargo.toml`.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
cdb02ef876d03a4c1b80f4884e8540359b2da5056622dd6ae56474f0b830f5c1  rust/src/lib.rs
d83c32a7c99a11ba7535ac3fb6ecc735781d650fd4e0a7f90f7c0bd13040df7b  rust/Cargo.toml
e7eb513660c980db5edabfa5f475ae46f07f6bf96425095c2bd29983e9e65627  rust/Cargo.lock
```

These hashes bind the transcripts and output artifacts below to this tree.

### `cargo test` (`rust/`)

```
$ cargo test
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.06s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-fa5bd6380d643d4e)

running 27 tests
test tests::should_reject_empty_bstr_input ... ok
test tests::should_reject_empty_array_header_input ... ok
test tests::should_reject_empty_input ... ok
test tests::should_decode_canonical_bstr ... ok
test tests::should_decode_fixed_64_bstr ... ok
test tests::should_decode_empty_map_header ... ok
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_reject_fixed_64_wrong_length_after_full_body ... ok
test tests::should_decode_minimal_sign1_envelope ... ok
test tests::should_decode_canonical_array_header_count_4 ... ok
test tests::should_reject_major_type_not_array ... ok
test tests::should_reject_major_type_not_bstr ... ok
test tests::should_reject_major_type_not_unsigned ... ok
test tests::should_reject_non_canonical_array_header ... ok
test tests::should_reject_non_canonical_bstr_length ... ok
test tests::should_reject_non_canonical_uint_length ... ok
test tests::should_reject_reserved_and_indefinite_additional ... ok
test tests::should_reject_reserved_and_indefinite_bstr ... ok
test tests::should_reject_sign1_count_not_4 ... ok
test tests::should_reject_sign1_nonempty_unprotected ... ok
test tests::should_reject_sign1_trailing_bytes ... ok
test tests::should_reject_truncated_array_header ... ok
test tests::should_reject_truncated_bstr_body ... ok
test tests::should_reject_truncated_bstr_header ... ok
test tests::should_reject_truncated_extra_length ... ok
test tests::should_reject_truncated_fixed_64_body ... ok
test tests::should_reject_truncated_sign1_slots ... ok

test result: ok. 27 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

Layer-1's 6 uint tests and layer-2's 10 bstr tests remain green. Envelope
tests: count ≠ 4 → `CoseError::MalformedEnvelope`; nonempty unprotected →
`CoseError::NonEmptyUnprotectedHeader`; trailing bytes →
`CoseError::Codec(TrailingBytes)`; truncated slots stay
`CoseError::Codec(UnexpectedEnd)` (not `WrongLength` on a short sig body).

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

Ran against the crate at **0.8.0** (same tree as the input hashes above).

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.8.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.62s
CHARON_EXIT:0
```

### Aeneas (progress bars stripped)

```
$ eval $(opam env --switch=5.3.0)
$ ~/aeneas/bin/aeneas -version
aeneas c2015b86

$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
[Info ] Imported: ../llbc/cbor_nopanic.llbc
[Info ] Generated: ../lean/CborNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 1.511681 seconds
AENEAS_EXIT:0
```

`NoPanic.lean` and `lakefile.lean` were not rewritten (handwritten
`NoPanic.lean` kept). Generated Lean has no `axiom` declarations and no loop
on input length. `read_sign1_envelope` is the source order: array4, protected
bstr, empty map, payload bstr, sig64, `finish`. `?` on `CodecError` uses
`From` → `CoseError.Codec`. The allowed 4096 cap was not used.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cbor_nopanic.llbc lean/CborNopanic.lean
e49fcacd112e6463b6a279994232eef559214c02faf36e0ba6b4d54a8e0bdbd5  llbc/cbor_nopanic.llbc
5b04bcb22078f3ea6eb34dce01c0ece2b7cfdbccd82713c4bb4a0a79dea6b8ee  lean/CborNopanic.lean
```

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:548:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:549:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:550:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:551:0: 'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:552:0: 'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:553:0: 'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (1698 jobs).
LAKE_EXIT:0
```

Aeneas stdlib replayed `sorry` warnings in unused `get_unchecked` / `StringIter`
models; they are not in these theorems' axiom sets.

### `#print axioms`

```
$ lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.read_uint_no_panic
#print axioms NoPanic.read_bstr_no_panic
#print axioms NoPanic.read_bstr_fixed_64_no_panic
#print axioms NoPanic.read_array_header_no_panic
#print axioms NoPanic.read_map_header_no_panic
#print axioms NoPanic.read_sign1_envelope_no_panic
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
AXIOMS_EXIT:0
```

These are the three standard Lean axioms. No `sorryAx`, no opaque `size_of`,
no unknown-external axioms. No new file in `reports/AXIOMS.md`.

## Reproduce

```sh
shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
shasum -a 256 ../llbc/cose_parse_nopanic.llbc ../lean/CoseParseNopanic.lean
cd ../lean && lake build
# axioms:
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.read_array_header_no_panic
#print axioms NoPanic.read_sign1_envelope_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install. Layer-1 claim remains in `PROOF.md`.
Layer-2 claim remains in `PROOF-bstr.md`.
