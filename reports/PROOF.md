# PROOF — `slice_validated_uints_no_panic` (loop) + `parse_sign1_no_panic`

Current proof. Earlier layer transcripts: [`history/`](history/).

## Loop theorem

For every hostile byte slice, the extracted looping array-of-uints
walk returns in the Aeneas `ok` monad. It does **not** prove RFC 8949
correctness or canonicity of the elements.

```
∀ bytes, ∃ r, slice_validated_uints bytes = ok r
```

`ok` includes `Err(CodecError)`. The Rust body still has
`while seen < count` (bound = array count from the bytes). Aeneas
emits `slice_validated_uints_loop` using the `loop` combinator.
Termination is `loop.spec_decr_nat` with measure
`(count − seen) * 2 + 1` while `err` is `none`, else `0`
(`NoPanic.slice_validated_uints_loop_no_div`). No `sorry`.

Theorems: `NoPanic.slice_validated_uints_no_panic`,
`NoPanic.slice_validated_uints_loop_no_div`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Finale claim

For every hostile byte slice, the extracted `COSE_Sign1` envelope parse
(`verify` minus crypto) returns in the Aeneas `ok` monad. It does **not**
prove RFC 9052 / RFC 9053 correctness, Ed25519, or product `Typ` meaning.

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
dalek, outside `parse_sign1`. This proves `cose_parse_nopanic`, not
`kntrl-license-core` in place.

Theorem in `lean/NoPanic.lean`: `NoPanic.parse_sign1_no_panic`. No `sorry`.
Layer theorems still hold: `read_uint_no_panic`, `read_bstr_no_panic`,
`read_bstr_fixed_64_no_panic`, `read_array_header_no_panic`,
`read_map_header_no_panic`, `read_sign1_envelope_no_panic`,
`decode_protected_header_no_panic`, `build_sig_structure_no_panic`,
`slice_validated_uints_no_panic`.
Leaves are `@[step]` specs; composites use `step*`; `read_head` is
`step*` then `split` on the additional-info match. The uint-array walk
uses `loop.spec_decr_nat`.

## Canonicity (`read_uint_ok_is_canonical`)

Decode-only. If `read_uint buf = ok (Result.Ok n)`, the first byte is
major type 0 and RFC 8949 §4.2.1 additional-info is smallest-form for
`n`:

- AI 0..=23: `n = ai`
- AI 24: `24 ≤ n ≤ 255`
- AI 25: `256 ≤ n ≤ 65535` (u16, not fitting u8)
- AI 26: `65536 ≤ n ≤ 4294967295` (u32, not fitting u16)
- AI 27: `n ≥ 4294967296` (not fitting u32)

The 2/4/8-byte cuts are the `value <= u8::MAX` / `u16::MAX` /
`u32::MAX` branches in `read_head`, unfolded in
`read_head_ok_smallest_form`. Reserved 28..=31 cannot be `Ok`.
Extra-width `[0x18, 0x05]` is `Err(NonCanonicalLength)`, not `Ok`.
`read_head_ai0_23` is the converse on 1-byte heads.

Does **not** claim: full RFC 8949, or encode-then-decode (`write_head`
then `read_head`).

Theorems: `NoPanic.read_head_ok_smallest_form`,
`NoPanic.read_uint_ok_is_canonical`. No `sorry`. Axioms: `propext`,
`Classical.choice`, `Quot.sound` (same as `read_uint_no_panic`).
Only handwritten `lean/NoPanic.lean` changed; `PROOF.sha256` of
Rust/llbc/generated Lean is unchanged.

## Live run

Crate **0.18.0**. Pins: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. `Debug` is `#[cfg_attr(test, derive(Debug))]` so Charon
does not extract `core.fmt`. Generated Lean has no `CoreFmtDebug`.

Binding file: [`PROOF.sha256`](PROOF.sha256). CI runs `sha256sum -c`
on it.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
31059bdbceb56286b9721db360e73db80dc9fa5860771c5a4b1a71cf99a30739  rust/src/lib.rs
ce1d2a1366ebe616b1db0ea491b1dbbdd7b7a21f953040c31cf18b9e11645130  rust/Cargo.toml
3f5e45a9f0ecb8779c1d921ae21aa2aad9cfa620f1615d2b466c428cd3540d60  rust/Cargo.lock
```

### `cargo test`

```
$ cargo test
   Compiling cose_parse_nopanic v0.18.0
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.31s
test result: ok. 53 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
CARGO_TEST_EXIT:0
```

### Charon

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
   Compiling cose_parse_nopanic v0.18.0
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.68s
CHARON_EXIT:0
```

### Aeneas

```
$ ~/aeneas/bin/aeneas -version
aeneas c2015b86

$ ~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
[Info ] Imported: ../llbc/cose_parse_nopanic.llbc
[Info ] Generated: ../lean/CoseParseNopanic.lean
[Warn ] The crate contains extracted external, unknown definitions: we advise using the option -split-files to allow manually providing these definitions in separate files.
[Info ] Total execution time: 2.308893 seconds
AENEAS_EXIT:0
```

Handwritten `NoPanic.lean` was not overwritten.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cose_parse_nopanic.llbc lean/CoseParseNopanic.lean
6a0eeb48bf8180e47d5f76a8c971c1a948b0cc2abb7b7f962c37c7dfb15b1f31  llbc/cose_parse_nopanic.llbc
81e641bbe98e96a3e0d43d8ae0c10601fe92adf42deabd0e756ad202e44cb15f  lean/CoseParseNopanic.lean
```

### `lake build` / axioms

Local `lake build` (Lean 4.31.0, Aeneas @ `c2015b86`) exit 0.
`#print axioms` on `slice_validated_uints_no_panic` and
`parse_sign1_no_panic`: `propext`, `Classical.choice`, `Quot.sound`.
No `sorryAx`. Charon/Aeneas stay local because CI does not run them.

Aeneas stdlib has `sorry` in unused `get_unchecked` / `StringIter`
models; they are not in these theorems' axiom sets.

## Reproduce

```sh
sha256sum -c reports/PROOF.sha256
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
cd ../lean && lake build
lake env lean --stdin <<'EOF'
import NoPanic
#print axioms NoPanic.parse_sign1_no_panic
#print axioms NoPanic.slice_validated_uints_no_panic
EOF
```

See `TOOLCHAIN.md` for pins. Layer transcripts: `history/`.
