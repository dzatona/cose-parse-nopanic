# cose-parse-nopanic

Machine-checked no-panic proof of a `COSE_Sign1` envelope parse: the
pre-crypto prefix of `verify`. Not Ed25519. Not RFC 8949 / RFC 9052 /
RFC 9053 correctness.

Not the KNTRL product tree. Not a Runtime Verification repository.
Work and name: Dmitrii Zatona. License: Apache-2.0.

**Proved:** for every `&[u8]`, `parse_sign1` in **this** crate returns
Aeneas `ok _` — a `Parsed` envelope or a normal `CoseError`. It does
not panic. This is an extracted copy of the `verify` pre-crypto path,
not a proof of `kntrl-license-core` in place. The product does not
depend on this crate.

That path is: array of 4, protected/payload/signature bstrs, empty
unprotected map, protected header `{1: -8, 4: kid, 100: typ}`, then
`Sig_structure` into `[u8; 4096]`. `BufferTooSmall` is `ok(Err)`.

**Not proved:** signature verification, `verify_strict`, public keys,
payload decode, trust-set.

Rust crate and Lean namespace: `cose_parse_nopanic`. Proof script:
leaves `@[step]`, composites `step*`, `read_head` via `split`. Reports
below are the proof artifacts.

Reports: [`reports/PROOF.md`](reports/PROOF.md),
[`reports/EXTRACT.md`](reports/EXTRACT.md),
[`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md).
Earlier layer transcripts: [`reports/history/`](reports/history/).
CI runs `cargo test` and `lake build` plus an axiom-set check.

[Binder](https://github.com/runtimeverification/kernel-rust-verification-spike)
is the Charon/Aeneas/Lean pipeline this proof follows (same pins).

## Reproduce

Pin Charon `909ff09a` / Aeneas `c2015b86` / Lean 4.31.0 — install
notes in [`reports/TOOLCHAIN.md`](reports/TOOLCHAIN.md).
`lean/lakefile.lean` loads Aeneas from `$HOME/aeneas/backends/lean`
(`AENEAS_LEAN` overrides). Then:

```sh
cd rust && cargo test
export PATH="$HOME/charon/bin:$PATH"
charon cargo --preset=aeneas --dest-file ../llbc/cose_parse_nopanic.llbc
eval $(opam env --switch=5.3.0)
~/aeneas/bin/aeneas -backend lean -dest ../lean ../llbc/cose_parse_nopanic.llbc
cd ../lean && lake build
```
