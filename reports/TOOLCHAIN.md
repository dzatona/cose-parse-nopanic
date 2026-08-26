# Toolchain

Recorded 2026-08-26 on aarch64-apple-darwin. Pins match the Binder spike
README (`runtimeverification/kernel-rust-verification-spike`) except where
the local stable rustc is newer; that drift is recorded, not silent.

| Component | Pin (pins) | What ran here |
|---|---|---|
| Charon | commit `909ff09a`, v0.1.220 (`--preset=aeneas`) | `/Users/dzatona/charon` @ `909ff09ad0f144f83d354f2c3d26f631fb9f8e9a`, crate version `0.1.220` |
| Charon rustc | nightly-2026-06-01 (Charon's `rust-toolchain`) | same; extra Charon targets trimmed locally to `aarch64-apple-darwin` only (disk), channel unchanged |
| Aeneas | commit `c2015b86` | `/Users/dzatona/aeneas` @ `c2015b86` (`Add bitwise operators on booleans. (#967)`); `charon-pin` matches `909ff09a` |
| Lean / mathlib | v4.31.0 | `leanprover/lean4:v4.31.0` (elan); mathlib4 `v4.31.0` via Aeneas `lakefile.lean` |
| rustc (crate tests) | stable 1.94.0 in the spike | **local stable is 1.95.0** (`59807616e 2026-04-14`); crate `rust-version = "1.92"` |

## Install (this machine)

```sh
# Charon
git clone https://github.com/AeneasVerif/charon.git ~/charon
cd ~/charon && git checkout 909ff09ad0f144f83d354f2c3d26f631fb9f8e9a
# rustfmt is required by Charon's Makefile `format` target
rustup component add --toolchain nightly-2026-06-01-aarch64-apple-darwin rustfmt
make build-charon-rust   # produces ~/charon/bin/charon

# Aeneas (OCaml 5.3.0)
brew install opam make pkgconf
opam init -y --disable-sandboxing --compiler=5.3.0
eval $(opam env --switch=5.3.0)
opam install -y --confirm-level=unsafe-yes dune calendar core_unix domainslib \
  easy_logging menhir ocamlformat.0.27.0 ocamlgraph odoc ppx_deriving \
  ppx_deriving_yojson progress unionFind visitors yojson zarith
ln -sfn ~/charon ~/aeneas/charon
# after cloning Aeneas @ c2015b86:
gmake -C ~/aeneas build   # GNU make; BSD make 3.81 is rejected

# Lean
brew install elan-init
elan toolchain install leanprover/lean4:v4.31.0
cd ~/aeneas/backends/lean && lake exe cache get && lake build Aeneas
```

`lean/lakefile.lean` requires Aeneas from `/Users/dzatona/aeneas/backends/lean`.
Change that path if the checkout moves.
