# cbor-nopanic

Machine-checked no-panic proof for one loop-free path in a hand-written
RFC 8949 deterministic CBOR decoder (the layer under `COSE_Sign1`).

Not the KNTRL product tree. Not a Runtime Verification repository.
Work and name: Dmitrii Zatona.

Toolchain (to match the Binder spike): Charon, Aeneas, Lean 4.

***REMOVED***

Status: spec written. Step 1 not started (`read_uint` / `read_head`, loop-free).
