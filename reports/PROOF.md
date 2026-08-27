# PROOF — `parse_sign1_no_panic` (finale)

Current proof. Earlier layer transcripts: [`history/`](history/).

## Claim

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
`decode_protected_header_no_panic`, `build_sig_structure_no_panic`.
Leaves are `@[step]` specs; composites use `step*`; `read_head` is manual.

## Live run

Crate **0.15.0**. Pins: Charon `909ff09a` v0.1.220, Aeneas `c2015b86`,
Lean 4.31.0. `Debug` is `#[cfg_attr(test, derive(Debug))]` so Charon
does not extract `core.fmt`. Generated Lean has no `CoreFmtDebug`.

Binding file: [`PROOF.sha256`](PROOF.sha256). CI runs `sha256sum -c`
on it.

### Inputs (sha256, before Charon)

```
$ shasum -a 256 rust/src/lib.rs rust/Cargo.toml rust/Cargo.lock
12f6356c89cd8c65a87c0d8c244b842c93a57c8aa3a30290104bdade9d9b783e  rust/src/lib.rs
6a6c27d37a19fba49790c90f8bc247a1ab95aad827078c310fa77bc97c3486e4  rust/Cargo.toml
79f97181da7f9202f56379d974d1c3e4b6946a627d3e75ba691c6e056105e28b  rust/Cargo.lock
```

### `cargo test`

```
$ cargo test
   Compiling cose_parse_nopanic v0.15.0
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.57s
test result: ok. 46 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.00s
CARGO_TEST_EXIT:0
```

### Charon

```
$ charon version
0.1.220

$ charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
   Compiling cose_parse_nopanic v0.15.0
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.77s
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
[Info ] Total execution time: 2.149315 seconds
AENEAS_EXIT:0
```

Handwritten `NoPanic.lean` was not overwritten.

### Outputs (sha256, after Charon + Aeneas)

```
$ shasum -a 256 llbc/cose_parse_nopanic.llbc lean/CoseParseNopanic.lean
dc13d5679ff3b2ff558b46b726c2f43a2d721ce61bcc5ffb753ce8dfe814fb0d  llbc/cose_parse_nopanic.llbc
411267ea74ecb7a05ea1a3950a4b9e8f3da41816481a37032cf491539c22f450  lean/CoseParseNopanic.lean
```

### `lake build` / axioms

CI is the witness (Lean 4.31.0, Aeneas @ `c2015b86`, axiom grep):
https://github.com/dzatona/cose-parse-nopanic/actions/runs/33041618859
(`827a165`, job `lean`). Local line numbers in an old transcript would
drift; Charon/Aeneas stay local because CI does not run them.

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
EOF
```

See `TOOLCHAIN.md` for pins. Layer transcripts: `history/`.
