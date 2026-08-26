# PROOF — `read_uint_no_panic` (step 1)

Historical layer-1 transcript. The crate was later renamed
`cbor_nopanic` → `cose_parse_nopanic`; commands below are verbatim.

## Claim

For every hostile byte slice, the extracted canonical-CBOR unsigned-integer
decoder returns in the Aeneas `ok` monad. It does **not** prove RFC 8949
correctness.

```
∀ buf, ∃ r, read_uint buf = ok r
```

`ok (Result.Ok value)` is a canonical uint. `ok (Result.Err CodecError)` is a
normal codec rejection (truncated, wrong major type, non-canonical length,
reserved additional, indefinite). `fail` would be panic / OOB / unwrap.

Theorem: `NoPanic.read_uint_no_panic` in `lean/NoPanic.lean`. No `sorry`.

## Checklist (checklist)

1. `cargo test` in `rust/` — 6/6 green (canonical 0/23/24/255/…, non-canonical
   `[0x18, 0x05]`, empty → `UnexpectedEnd`, major ≠ 0 → `TypeMismatch`).
   Transcript below.
2. Charon exit 0 — `llbc/cbor_nopanic.llbc` (`charon cargo --preset=aeneas`).
3. Aeneas exit 0 — `lean/CborNopanic.lean`; `lake build` typechecks.
4. Theorem `read_uint_no_panic` without `sorry`.
5. `#print axioms` (below). Only standard Lean axioms.
6. `EXTRACT.md` covers `reader.rs`, the Aeneas remodel, and source provenance.
7. README states the claim and reproduce commands.
8. Repo remains private. Transcript below.

`CborNopanic.lean` is Aeneas-generated. `NoPanic.lean` is handwritten and was
not overwritten by the Aeneas dest pass.

## Live re-run (2026-08-26T07:25Z)

Independent of the previous `llbc/` / `CborNopanic.lean` timestamps. Pins:

```
charon version
0.1.220
exit:0
charon HEAD 909ff09ad0f144f83d354f2c3d26f631fb9f8e9a

aeneas -version
aeneas c2015b86
exit:0
aeneas HEAD c2015b8668ba6d5b41f5f19d00a881c12bbb0b5d

ocaml 5.3.0 (opam switch 5.3.0)
```

### `cargo test` (`rust/`, current tree — checklist 1)

```
$ cargo test
   Compiling cbor_nopanic v0.3.0 (/Users/dzatona/Sites/MacExchange/cose-parse-nopanic/rust)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.73s
     Running unittests src/lib.rs (target/debug/deps/cbor_nopanic-b161ad2e7f35305c)

running 6 tests
test tests::should_decode_uint_smallest_form_boundaries ... ok
test tests::should_reject_empty_input ... ok
test tests::should_reject_non_canonical_uint_length ... ok
test tests::should_reject_major_type_not_unsigned ... ok
test tests::should_reject_reserved_and_indefinite_additional ... ok
test tests::should_reject_truncated_extra_length ... ok

test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

   Doc-tests cbor_nopanic

running 0 tests

test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s

CARGO_TEST_EXIT:0
```

### Charon (`rust/`, PATH includes `$HOME/charon/bin`)

```
$ charon cargo --preset=aeneas --dest-file ../llbc/cbor_nopanic.llbc
   Compiling cbor_nopanic v0.1.0 (/Users/dzatona/Sites/MacExchange/cbor-nopanic/rust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.84s
CHARON_EXIT:0
```

`llbc/cbor_nopanic.llbc` sha256 after this pass:
`4d054fe59eb7ba2782b8df927959d5604a793500bd1ed2145cbf19a391b8c652`
(pre-run sha256 was `6bc72744e180a9d6cb87131c59564fef8ede23cbc08a8f43e2e07a8e09f2ec1d`;
Charon is not bit-stable on re-run).
Crate version is now `0.3.0` after later feat bumps; the live `cargo test` above
is against the current tree. Historical Charon hashes are not rewritten.

### Aeneas (progress bars stripped)

```
$ eval $(opam env --switch=5.3.0)
$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cbor_nopanic.llbc
[Info ] Imported: ../llbc/cbor_nopanic.llbc
[Info ] Generated: ../lean/CborNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 1.229207 seconds
AENEAS_EXIT:0
```

`lean/CborNopanic.lean` sha256 unchanged:
`9d1da8ce885c0fc8ff333a8694cfefe094ddf42cc33725c0247a96f6af962ba3`
`NoPanic.lean` and `lakefile.lean` were not rewritten.

### `lake build`

```
$ cd ../lean && lake build
info: NoPanic.lean:362:0: 'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (1698 jobs).
LAKE_EXIT:0
```

Aeneas stdlib replayed `sorry` warnings in unused `get_unchecked` / `StringIter`
models; they are not in this theorem's axiom set. `rg sorry lean/` is empty.

### GitHub privacy (checklist 8)

```
$ gh repo view --json name,isPrivate,url
{"isPrivate":true,"name":"cose-parse-nopanic","url":"https://github.com/dzatona/cose-parse-nopanic"}
GH_EXIT:0
```

Repo remains private.

## `#print axioms` (after the fresh Aeneas pass)

```
$ lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.read_uint_no_panic
EOF
'NoPanic.read_uint_no_panic' depends on axioms: [propext, Classical.choice, Quot.sound]
AXIOMS_EXIT:0
```

These are the three standard Lean axioms. No `sorryAx`, no opaque `size_of`,
no unknown-external axioms. First Aeneas output *did* emit `axiom`s for
`Option::ok_or`, `slice::first`, `TryFrom<&[u8]> for [u8; N]`, integer
`TryFrom`, and `Result::map_err`. Those were removed by a loop-free Rust
remodel (`// REMODEL:` in `rust/src/lib.rs`): `match` on `checked_add` /
`slice::get` instead of `ok_or`/`first`/`try_into`. Semantics of the test
vectors are unchanged.

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
#print axioms NoPanic.read_uint_no_panic
EOF
```

See `TOOLCHAIN.md` for pins and install.
