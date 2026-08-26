# PROOF — `parse_sign1_no_panic` (finale)

## Claim

For every hostile byte slice, the extracted `COSE_Sign1` envelope parse
(`verify` minus crypto) returns in the Aeneas `ok` monad. It does **not**
prove RFC 8152 correctness, Ed25519, or product `Typ` meaning.

```
∀ bytes, ∃ r, parse_sign1 bytes = ok r
```

`ok` includes `Err(CoseError)`. `ok (Result.Ok Parsed)` is kid + typ +
payload after envelope + protected header + `Sig_structure`.
`ok (Result.Err CoseError)` is a normal rejection:

- array count ≠ 4 → `MalformedEnvelope`
- unprotected map nonempty → `NonEmptyUnprotectedHeader`
- protected map not `{1:-8, 4:kid16, 100:typ}` → `MalformedProtectedHeader`
  / `UnsupportedAlgorithm` / `UnknownTyp`
- truncated / trailing / non-canonical slots → `Codec(...)`
- reconstructed `Sig_structure` does not fit `[u8; 4096]` →
  `Codec(BufferTooSmall)`

`fail` would be panic / OOB / unwrap.

Not `∀ pubkey`. Not `SignatureInvalid` / `InvalidPublicKey`. Those are
dalek, outside `parse_sign1`.

Theorem in `lean/NoPanic.lean`:

- `NoPanic.parse_sign1_no_panic`

No `sorry`. Layer-1 `read_uint_no_panic`, layer-2 `read_bstr_no_panic` /
`read_bstr_fixed_64_no_panic`, layer-3 `read_array_header_no_panic` /
`read_map_header_no_panic` / `read_sign1_envelope_no_panic`, layer-4
`decode_protected_header_no_panic`, and layer-5
`build_sig_structure_no_panic` are unchanged and still hold. The finale
only composes them.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. Ran against crate **0.11.0**. Charon compile line below is
`cbor_nopanic v0.11.0`, matching `rust/Cargo.toml`.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
afc9537577a305c668f343fc94cc6f90fb655019c827c8521e129da1795cbbb4  rust/src/lib.rs
9879da73952c6fab36ac6169a620a5e197ae00794ecadc94bddc64fe42391979  rust/Cargo.toml
b7cc72a6c002cfbc1af93c5e3533e8b9fd5eca8f0fb0206be917c537755259e0  rust/Cargo.lock
```

These hashes bind the transcripts and output artifacts below to this tree.

Source provenance (read-only kntrl-org, not copied as a tree) is in
`EXTRACT.md` finale: `cose/mod.rs` at
`206ec5ecab0f579d538eac7897434d9a2f43f058`, sha256
`8abf884d28ee63c28ff5f85aba99e74cc662c52462741d180d9ca20a2e0a7a28`.
`verify` 221–239 + 248 quoted there; CUT 241–246.

### `cargo test` (`rust/`)

```
$ cargo test
   Compiling cbor_nopanic v0.11.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.57s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-40b8f28059b60570)

running 46 tests
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
test tests::should_parse_canonical_sign1 ... ok
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
test tests::should_reject_parse_bad_protected_header ... ok
test tests::should_reject_parse_malformed_envelope ... ok
test tests::should_reject_parse_nonempty_unprotected ... ok
test tests::should_reject_parse_oversized_sig_structure ... ok
test tests::should_reject_parse_truncated_and_trailing ... ok
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

test result: ok. 46 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

Layers 1–5 tests remain green. New tests go through `parse_sign1`:
canonical `{1:-8, 4:kid16, 100:typ}` + 64-byte sig → `Ok` with that
kid/typ/payload; malformed envelope; nonempty unprotected; bad header
(`UnknownTyp` / `UnsupportedAlgorithm` / `MalformedProtectedHeader`);
truncated; trailing; 4096-byte payload → `Codec(BufferTooSmall)`.

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

Ran against the crate at **0.11.0** (same tree as the input hashes above).

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.11.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.68s
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
[Info ] Total execution time: 2.471610 seconds
AENEAS_EXIT:0
```

`NoPanic.lean` and `lakefile.lean` were not rewritten (handwritten
`NoPanic.lean` kept). Generated Lean has no `axiom` declarations and no
loop on input length. `parse_sign1` is the three proved helpers plus
`Ok(Parsed)`.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cbor_nopanic.llbc lean/CborNopanic.lean
b8d568db77782f5c8945d39286f0a81ffc698b17fb9966238da1ac708f1ae167  llbc/cbor_nopanic.llbc
352b85460fde4177bc0269b325ed9fd75db5f5fa830466fdf11b7b7cf5106ffc  lean/CborNopanic.lean
```

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:1168:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1169:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1170:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1171:0: 'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1172:0: 'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1173:0: 'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1174:0: 'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1175:0: 'NoPanic.build_sig_structure_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:1176:0: 'NoPanic.parse_sign1_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
#print axioms NoPanic.parse_sign1_no_panic
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.build_sig_structure_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.parse_sign1_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
#print axioms NoPanic.parse_sign1_no_panic
#print axioms NoPanic.build_sig_structure_no_panic
#print axioms NoPanic.decode_protected_header_no_panic
#print axioms NoPanic.read_sign1_envelope_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install. Layer-1 claim remains in `PROOF.md`.
Layer-2 claim remains in `PROOF-bstr.md`. Layer-3 claim remains in
`PROOF-envelope.md`. Layer-4 claim remains in `PROOF-header.md`. Layer-5
claim remains in `PROOF-sig.md`.
