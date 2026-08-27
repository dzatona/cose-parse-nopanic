# PROOF — `decode_protected_header_no_panic` (layer 4)

## Claim

For every hostile byte slice, the extracted unrolled `{1: alg=-8, 4: kid-16,
100: typ}` protected-header decoder returns in the Aeneas `ok` monad. It does
**not** prove RFC 8949 or RFC 9052 correctness, and it does **not** compose
with `read_sign1_envelope` into `parse_sign1`.

```
∀ bytes, ∃ r, decode_protected_header bytes = ok r
```

`ok (Result.Ok ([u8; 16], Typ))` is a canonical `{1,4,100}` map.
`ok (Result.Err CoseError)` is a normal rejection:

- map count ≠ 3 or a key other than `1` / `4` / `100` in that order →
  `MalformedProtectedHeader`
- `alg` byte ≠ `0x27` (including a truncated alg slot) →
  `UnsupportedAlgorithm`
- `typ` not in `1..=4` → `UnknownTyp`
- non-ascending / duplicate key → `Codec(NonCanonicalKeyOrder)`
- truncated kid body → `Codec(UnexpectedEnd)` (not `WrongLength`)
- complete kid of the wrong length → `Codec(WrongLength)`
- trailing bytes → `Codec(TrailingBytes)`

`fail` would be panic / OOB / unwrap.

Theorem in `lean/NoPanic.lean`:

- `NoPanic.decode_protected_header_no_panic`

No `sorry`. Layer-1 `read_uint_no_panic`, layer-2 `read_bstr_no_panic` /
`read_bstr_fixed_64_no_panic`, and layer-3 `read_array_header_no_panic` /
`read_map_header_no_panic` / `read_sign1_envelope_no_panic` are unchanged
and still hold.

The source is syntactically unrolled (three `next_map_key` calls, not a
`while` over the pair count). Aeneas kept that unroll. No loop lemma. No
`STOP.md`.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. Ran against crate **0.9.0**. Charon compile line below is
`cbor_nopanic v0.9.0`, matching `rust/Cargo.toml`.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
704f4e8d60842c41a0507d04eb959ba108e3bc2bd95e2fdce1586d7efa75513a  rust/src/lib.rs
10d60c7f60d3d247919bf7a5a59a3978a87513c6c5111bd0f861a4ed39570df8  rust/Cargo.toml
903b01a435acd983e33c6bacdf063df294bb0ad4e74ecfaed804e6d55cdc8c1f  rust/Cargo.lock
```

These hashes bind the transcripts and output artifacts below to this tree.

Source provenance (read-only kntrl-org, not copied as a tree) is in
`EXTRACT.md` layer 4: `cose/mod.rs` / `types.rs` / `reader.rs` at
`206ec5ecab0f579d538eac7897434d9a2f43f058`, with `decode_protected_header`
95–122 quoted there.

### `cargo test` (`rust/`)

```
$ cargo test
   Compiling cbor_nopanic v0.9.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.19s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-f8bbc8fdaab1d97c)

running 36 tests
test tests::should_decode_canonical_array_header_count_4 ... ok
test tests::should_decode_canonical_bstr ... ok
test tests::should_decode_canonical_protected_header ... ok
test tests::should_decode_empty_map_header ... ok
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_decode_minimal_sign1_envelope ... ok
test tests::should_decode_fixed_64_bstr ... ok
test tests::should_reject_empty_array_header_input ... ok
test tests::should_reject_empty_bstr_input ... ok
test tests::should_reject_empty_input ... ok
test tests::should_reject_fixed_64_wrong_length_after_full_body ... ok
test tests::should_reject_major_type_not_array ... ok
test tests::should_reject_kid_wrong_length ... ok
test tests::should_reject_major_type_not_bstr ... ok
test tests::should_reject_major_type_not_unsigned ... ok
test tests::should_reject_non_canonical_array_header ... ok
test tests::should_reject_non_canonical_bstr_length ... ok
test tests::should_reject_non_canonical_uint_length ... ok
test tests::should_reject_protected_header_duplicate_key ... ok
test tests::should_reject_protected_header_keys_out_of_order ... ok
test tests::should_reject_protected_header_unsupported_alg ... ok
test tests::should_reject_protected_header_trailing_bytes ... ok
test tests::should_reject_reserved_and_indefinite_additional ... ok
test tests::should_reject_protected_header_wrong_map_count ... ok
test tests::should_reject_reserved_and_indefinite_bstr ... ok
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

test result: ok. 36 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

Layer-1's 6 uint tests, layer-2's 10 bstr tests, and layer-3's envelope
tests remain green. Header tests: canon `{1:-8, 4:bstr16, 100:1..=4}`;
wrong map count → `MalformedProtectedHeader`; first key `4` →
`MalformedProtectedHeader`; duplicate key `1` →
`Codec(NonCanonicalKeyOrder)`; alg `0x26`/`0x00` →
`UnsupportedAlgorithm`; truncated kid → `Codec(UnexpectedEnd)`; complete
8-byte kid → `Codec(WrongLength)`; typ `0`/`5` → `UnknownTyp`; trailing
byte → `Codec(TrailingBytes)`.

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

Ran against the crate at **0.9.0** (same tree as the input hashes above).

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.9.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.60s
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
[Info ] Total execution time: 1.881377 seconds
AENEAS_EXIT:0
```

`NoPanic.lean` and `lakefile.lean` were not rewritten (handwritten
`NoPanic.lean` kept). Generated Lean has no `axiom` declarations and no
loop on pair count or input length. `decode_protected_header` is the
source order: map header == 3, `next_map_key` / key==1 / `read_fixed_byte`
0x27, `next_map_key` / key==4 / `read_bstr_fixed_16`, `next_map_key` /
key==100 / `Typ.from_u64`, `finish`. `&mut Option<u64>` became a
by-value `Option` returned beside the reader. The allowed unroll was
enough; no second remodel.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cbor_nopanic.llbc lean/CborNopanic.lean
7a66129ba666a28aa943076bf87c531a96b92c59799581964cbd8729c7da1952  llbc/cbor_nopanic.llbc
762167b2d6f800f900590f902a09e6fff56d28606fc65fb1157ae02c6da57e10  lean/CborNopanic.lean
```

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:711:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:712:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:713:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:714:0: 'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:715:0: 'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:716:0: 'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:717:0: 'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_array_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_map_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_sign1_envelope_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.decode_protected_header_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
shasum -a 256 ../llbc/cose_parse_nopanic.llbc ../lean/CoseParseNopanic.lean
cd ../lean && lake build
# axioms:
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.decode_protected_header_no_panic
#print axioms NoPanic.read_sign1_envelope_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install. Layer-1 claim remains in `PROOF.md`.
Layer-2 claim remains in `PROOF-bstr.md`. Layer-3 claim remains in
`PROOF-envelope.md`.
