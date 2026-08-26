# PROOF — `read_bstr_no_panic` / `read_bstr_fixed_64_no_panic` (layer 2)

## Claim

For every hostile byte slice, the extracted canonical-CBOR byte-string decoders
return in the Aeneas `ok` monad. They do **not** prove RFC 8949 correctness.

```
∀ buf, ∃ r, read_bstr buf = ok r
∀ buf, ∃ r, read_bstr_fixed_64 buf = ok r
```

`ok (Result.Ok value)` is a decoded bstr (or a 64-byte array).
`ok (Result.Err CodecError)` is a normal codec rejection (truncated header or
body, wrong major type, non-canonical length, reserved additional, indefinite,
`LengthOverflow`, `WrongLength`). `fail` would be panic / OOB / unwrap.

Theorems in `lean/NoPanic.lean`:

- `NoPanic.read_bstr_no_panic`
- `NoPanic.read_bstr_fixed_64_no_panic`

No `sorry`. Layer-1 `NoPanic.read_uint_no_panic` is unchanged and still holds.

## Live run (2026-08-26)

Pins match `TOOLCHAIN.md`: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0.

### `cargo test` (`rust/`)

```
$ cargo test
   Compiling cbor_nopanic v0.4.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.91s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-1a3797f08ca11b35)

running 16 tests
test tests::should_decode_fixed_64_bstr ... ok
test tests::should_reject_empty_bstr_input ... ok
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_decode_canonical_bstr ... ok
test tests::should_reject_empty_input ... ok
test tests::should_reject_fixed_64_wrong_length_after_full_body ... ok
test tests::should_reject_major_type_not_bstr ... ok
test tests::should_reject_major_type_not_unsigned ... ok
test tests::should_reject_non_canonical_bstr_length ... ok
test tests::should_reject_non_canonical_uint_length ... ok
test tests::should_reject_reserved_and_indefinite_additional ... ok
test tests::should_reject_reserved_and_indefinite_bstr ... ok
test tests::should_reject_truncated_bstr_body ... ok
test tests::should_reject_truncated_bstr_header ... ok
test tests::should_reject_truncated_extra_length ... ok
test tests::should_reject_truncated_fixed_64_body ... ok

test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

Layer-1's 6 uint tests remain green. New tests cover canon bstr, non-canonical
length, empty, wrong major, truncated header, truncated body (`UnexpectedEnd`
not `WrongLength`), fixed-64 success, fixed-64 wrong length after a full body
(`WrongLength`), and truncated 64-body (`UnexpectedEnd`).

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.4.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.88s
CHARON_EXIT:0
```

`llbc/cbor_nopanic.llbc` sha256 after this pass:
`9f682b03c204a1b162d2dcde8304ed3f621ea1c12271f5a6900f519d41f821fc`

### Aeneas (progress bars stripped)

```
$ eval $(opam env --switch=5.3.0)
$ ~/aeneas/bin/aeneas -version
aeneas c2015b86

$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
[Info ] Imported: ../llbc/cbor_nopanic.llbc
[Info ] Generated: ../lean/CborNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 1.305221 seconds
AENEAS_EXIT:0
```

`lean/CborNopanic.lean` sha256:
`170edb6116e337b1a62eae53703ec5ff6e3cba48beb53bd44625e1a1f8e30b84`

`NoPanic.lean` and `lakefile.lean` were not rewritten. Generated Lean has no
`axiom` declarations and no loop on input length. `take(len)` stays the layer-1
`checked_add` + `slice::get`. The allowed 4096 cap was not used.

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:428:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:429:0: 'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
info: NoPanic.lean:430:0: 'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
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
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NoPanic.read_bstr_fixed_64_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
AXIOMS_EXIT:0
```

These are the three standard Lean axioms. No `sorryAx`, no opaque `size_of`,
no unknown-external axioms. No new file in `reports/AXIOMS.md`.

## Reproduce

```sh
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
cd ../lean && lake build
# axioms:
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.read_bstr_no_panic
#print axioms NoPanic.read_bstr_fixed_64_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install. Layer-1 claim remains in `PROOF.md`.
