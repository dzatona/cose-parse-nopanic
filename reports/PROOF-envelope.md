# PROOF — `read_sign1_envelope_no_panic` (layer 3)

## Claim

For every hostile byte slice, the extracted `COSE_Sign1` array-of-4 envelope
skeleton returns in the Aeneas `ok` monad. It does **not** prove RFC 8949 or
RFC 8152 correctness, and it does **not** decode the protected-header map.

```
∀ buf, ∃ r, read_array_header buf = ok r
∀ buf, ∃ r, read_map_header buf = ok r
∀ buf, ∃ r, read_sign1_envelope buf = ok r
```

`ok (Result.Ok Envelope)` is the four slots (raw protected bstr, raw payload
bstr, 64-byte signature). `ok (Result.Err CodecError)` is a normal rejection
(truncated slot, wrong major, non-canonical length, count ≠ 4, nonempty
unprotected map, trailing bytes, `WrongLength` after a complete short
signature). `fail` would be panic / OOB / unwrap.

Theorems in `lean/NoPanic.lean`:

- `NoPanic.read_array_header_no_panic`
- `NoPanic.read_map_header_no_panic`
- `NoPanic.read_sign1_envelope_no_panic` — composition target

No `sorry`. Layer-1 `NoPanic.read_uint_no_panic` and layer-2
`NoPanic.read_bstr_no_panic` / `NoPanic.read_bstr_fixed_64_no_panic` are
unchanged and still hold.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0.

### `cargo test` (`rust/`)

```
$ cargo test
   Compiling cbor_nopanic v0.7.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.30s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-0f0dfd34b86c43f0)

running 27 tests
test tests::should_decode_canonical_array_header_count_4 ... ok
test tests::should_decode_canonical_bstr ... ok
test tests::should_decode_empty_map_header ... ok
test tests::should_decode_fixed_64_bstr ... ok
test tests::should_decode_minimal_sign1_envelope ... ok
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_reject_empty_array_header_input ... ok
test tests::should_reject_empty_bstr_input ... ok
test tests::should_reject_empty_input ... ok
test tests::should_reject_fixed_64_wrong_length_after_full_body ... ok
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

Layer-1's 6 uint tests and layer-2's 10 bstr tests remain green. New tests
cover array-header count 4, non-canonical, empty, wrong major, truncated;
minimal well-formed 4-array (empty protected/payload, empty unprotected map,
64-byte sig); trailing bytes → `TrailingBytes`; count ≠ 4 →
`MalformedEnvelope`; nonempty unprotected → `NonEmptyUnprotectedHeader`;
truncated slots stay `UnexpectedEnd` (not `WrongLength` on a short sig body).

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

Ran against the crate at 0.6.0 (envelope code; 0.7.0 is the Lean-proof
version bump only).

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.6.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.61s
CHARON_EXIT:0
```

`llbc/cbor_nopanic.llbc` sha256 after this pass:
`678160a46c864ec4cc2c4aea0f1a37cb3c53eec29d20c89a42bc051d05aca4e2`

### Aeneas (progress bars stripped)

```
$ eval $(opam env --switch=5.3.0)
$ ~/aeneas/bin/aeneas -version
aeneas c2015b86

$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
[Info ] Imported: ../llbc/cbor_nopanic.llbc
[Info ] Generated: ../lean/CborNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 1.403458 seconds
AENEAS_EXIT:0
```

`lean/CborNopanic.lean` sha256:
`ebfba7096fbd7a6110fc9b01eb76dc7e6dedfdab07ecb0aef3818accfddd9bf0`

`NoPanic.lean` and `lakefile.lean` were not rewritten. Generated Lean has no
`axiom` declarations and no loop on input length. `read_sign1_envelope` is
the source order: array4, protected bstr, empty map, payload bstr, sig64,
`finish`. The allowed 4096 cap was not used.

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:535:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:536:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:537:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:538:0: 'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:539:0: 'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:540:0: 'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
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
