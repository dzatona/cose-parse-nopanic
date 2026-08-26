# PROOF — `build_sig_structure_no_panic` (layer 5)

## Claim

For every `Typ` and pair of hostile byte slices, the extracted RFC 8152
`Sig_structure` encoder returns in the Aeneas `ok` monad. It does **not**
prove RFC 8152 correctness, and it does **not** compose with
`read_sign1_envelope` / `decode_protected_header` into `parse_sign1`.

```
∀ typ, ∀ protected, ∀ payload, ∃ r, build_sig_structure typ protected payload = ok r
```

`ok (Result.Ok SigStructure)` is a `["Signature1", protected, aad, payload]`
array that fitted in `[u8; 4096]`. `ok (Result.Err CoseError)` is a normal
rejection:

- encoded structure (headers + `"Signature1"` + aad + both bstrs) does not
  fit in 4096 → `Codec(BufferTooSmall)`

`fail` would be panic / OOB / unwrap. A cap of each input bstr at 4096 does
**not** imply the encoded structure fits.

Theorem in `lean/NoPanic.lean`:

- `NoPanic.build_sig_structure_no_panic`

No `sorry`. Layer-1 `read_uint_no_panic`, layer-2 `read_bstr_no_panic` /
`read_bstr_fixed_64_no_panic`, layer-3 `read_array_header_no_panic` /
`read_map_header_no_panic` / `read_sign1_envelope_no_panic`, and layer-4
`decode_protected_header_no_panic` are unchanged and still hold.

`copy_from_slice` is the Aeneas stdlib primitive, not a loop. The allowed
length-check remodel sits in front of it. No loop lemma. No `STOP.md`.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. Ran against crate **0.10.0**. Charon compile line below is
`cbor_nopanic v0.10.0`, matching `rust/Cargo.toml`.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
0a6807e9c5a9d9fe737ddea63409dad1e3e6fd3b897edbf8588499505e94fa03  rust/src/lib.rs
ebb3bb02db7ecc869d5a48613657c4fe1df59849afaa6244fef3c6dfcfc147d3  rust/Cargo.toml
84855b7200678e344dad20205efc20ff8589f6bacfef89c4db9f9c36b8f4dac5  rust/Cargo.lock
```

These hashes bind the transcripts and output artifacts below to this tree.

Source provenance (read-only kntrl-org, not copied as a tree) is in
`EXTRACT.md` layer 5: `cose/mod.rs` / `cbor/mod.rs` / `domain.rs` at
`206ec5ecab0f579d538eac7897434d9a2f43f058`, with `build_sig_structure`
134–149 quoted there.

### `cargo test` (`rust/`)

```
$ cargo test
   Compiling cbor_nopanic v0.10.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.48s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-5f204c0534027476)

running 40 tests
test tests::should_decode_canonical_array_header_count_4 ... ok
test tests::should_change_sig_structure_for_each_typ_aad ... ok
test tests::should_decode_canonical_protected_header ... ok
test tests::should_decode_empty_map_header ... ok
test tests::should_decode_canonical_bstr ... ok
test tests::should_decode_fixed_64_bstr ... ok
test tests::should_decode_minimal_sign1_envelope ... ok
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_encode_empty_sig_structure ... ok
test tests::should_encode_tiny_protected_and_payload ... ok
test tests::should_reject_empty_array_header_input ... ok
test tests::should_reject_empty_bstr_input ... ok
test tests::should_reject_empty_input ... ok
test tests::should_reject_fixed_64_wrong_length_after_full_body ... ok
test tests::should_reject_kid_wrong_length ... ok
test tests::should_reject_major_type_not_array ... ok
test tests::should_reject_major_type_not_bstr ... ok
test tests::should_reject_major_type_not_unsigned ... ok
test tests::should_reject_non_canonical_array_header ... ok
test tests::should_reject_non_canonical_bstr_length ... ok
test tests::should_reject_non_canonical_uint_length ... ok
test tests::should_reject_oversized_sig_structure_payload ... ok
test tests::should_reject_protected_header_duplicate_key ... ok
test tests::should_reject_protected_header_keys_out_of_order ... ok
test tests::should_reject_protected_header_trailing_bytes ... ok
test tests::should_reject_protected_header_wrong_map_count ... ok
test tests::should_reject_protected_header_unsupported_alg ... ok
test tests::should_reject_reserved_and_indefinite_bstr ... ok
test tests::should_reject_reserved_and_indefinite_additional ... ok
test tests::should_reject_sign1_count_not_4 ... ok
test tests::should_reject_sign1_nonempty_unprotected ... ok
test tests::should_reject_sign1_trailing_bytes ... ok
test tests::should_reject_truncated_array_header ... ok
test tests::should_reject_truncated_bstr_body ... ok
test tests::should_reject_truncated_bstr_header ... ok
test tests::should_reject_truncated_extra_length ... ok
test tests::should_reject_truncated_fixed_64_body ... ok
test tests::should_reject_truncated_kid_body ... ok
test tests::should_reject_truncated_sign1_slots ... ok
test tests::should_reject_unknown_typ ... ok

test result: ok. 40 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

Layer-1's 6 uint tests, layer-2's 10 bstr tests, layer-3's envelope tests,
and layer-4's header tests remain green. New tests: empty protected/payload
still produce array-4 + text `"Signature1"`; tiny protected/payload fit;
all four `Typ` AAD literals change the encoding; a 4096-byte payload or
protected bstr → `Codec(BufferTooSmall)`.

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

Ran against the crate at **0.10.0** (same tree as the input hashes above).

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.10.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.69s
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
[Info ] Total execution time: 3.179165 seconds
AENEAS_EXIT:0
```

`NoPanic.lean` and `lakefile.lean` were not rewritten (handwritten
`NoPanic.lean` kept). Generated Lean has no `axiom` declarations and no
loop on input length. `copy_from_slice` is
`core.slice.Slice.copy_from_slice` (stdlib: `ok src` iff lengths equal,
else `fail`), behind the equal-length branch. First borrowed-buffer
extraction failed; the owned-array close is in `reports/AENEAS.md`.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cbor_nopanic.llbc lean/CborNopanic.lean
1d66f95c8ced177dd089e781f79f82440ad5f59e52f0c74b673a633c498f67d2  llbc/cbor_nopanic.llbc
fd7b1d71d9ad09646df8b4608ed9e0f1dbab7c949310c435fa59d70c42f1ea39  lean/CborNopanic.lean
```

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:1124:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1125:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1126:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1127:0: 'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1128:0: 'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1129:0: 'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1130:0: 'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1131:0: 'NoPanic.build_sig_structure_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (1698 jobs).
LAKE_EXIT:0
```

Aeneas stdlib replayed `sorry` warnings in unused `get_unchecked` /
`StringIter` models; they are not in these theorems' axiom sets.

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
#print axioms NoPanic.decode_protected_header_no_panic
#print axioms NoPanic.build_sig_structure_no_panic
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.build_sig_structure_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
AXIOMS_EXIT:0
```

These are the three standard Lean axioms. No `sorryAx`, no opaque
`size_of`, no unknown-external axioms. No new file in `reports/AXIOMS.md`.
No `reports/STOP.md`.

## Reproduce

```sh
shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
shasum -a 256 ../llbc/cbor_nopanic.llbc ../lean/CborNopanic.lean
cd ../lean && lake build
# axioms:
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.build_sig_structure_no_panic
#print axioms NoPanic.decode_protected_header_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install. Layer-1 claim remains in `PROOF.md`.
Layer-2 claim remains in `PROOF-bstr.md`. Layer-3 claim remains in
`PROOF-envelope.md`. Layer-4 claim remains in `PROOF-header.md`.
