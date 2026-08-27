-- Handwritten no-panic theorem. Aeneas generates `CoseParseNopanic.lean` from
-- `llbc/cose_parse_nopanic.llbc`; this file is not Aeneas output.
--
-- Panic model (Binder spike): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, OOB index, unwrap, ...) is
-- exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A codec
-- rejection is `ok (Result.Err CodecError)` (or `CoseError` on the envelope
-- path) — still `ok`.
--
-- `f ⦃ _ => True ⦄` is `spec f (fun _ => True)` ≡ `∃ v, f = ok v`.
-- Leaf extracted functions are tagged `@[step]` so `step*` can chain them.
-- `Reader.read_head` still uses a bind script: `step*` does not split the
-- additional-info `U8` match in bounded time.
-- This theorem does not claim RFC 8949 correctness.

import CoseParseNopanic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open cose_parse_nopanic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace NoPanic

/-- No-panic `step*`: postcondition is `True`, so skip grind. -/
macro "nstep" : tactic => `(tactic| step* -grind -threadGrindState)

/-- `spec m (fun _ => True)` is exactly “the panic monad returned `ok`”. -/
theorem of_spec {α} {m : Result α} (h : m ⦃ _ => True ⦄) : ∃ v, m = ok v := by
  cases m with
  | ok v => exact ⟨v, rfl⟩
  | fail _ => simp [spec, theta] at h
  | div => simp [spec, theta] at h

theorem spec_of_exists {α} {m : Result α} (h : ∃ v, m = ok v) : m ⦃ _ => True ⦄ := by
  obtain ⟨v, hv⟩ := h
  simp [hv]

/-- The Aeneas panic monad returns `ok`, never `fail`/`div`. -/
abbrev AlwaysOk {α : Type _} (m : Result α) : Prop := ∃ v, m = ok v

theorem AlwaysOk.of_ok {α} (v : α) : AlwaysOk (ok v) := ⟨v, rfl⟩

theorem AlwaysOk.of_lift {α} (x : α) : AlwaysOk (lift x) := ⟨x, rfl⟩

theorem AlwaysOk.bind {α β} {m : Result α} {f : α → Result β}
    (hm : AlwaysOk m) (hf : ∀ a, AlwaysOk (f a)) :
    AlwaysOk (do let x ← m; f x) := by
  obtain ⟨a, rfl⟩ := hm
  simpa [bind_tc_ok] using hf a

theorem AlwaysOk.ite {α} (c : Prop) [Decidable c] {t e : Result α}
    (ht : AlwaysOk t) (he : AlwaysOk e) :
    AlwaysOk (if c then t else e) := by
  split <;> assumption

/-! # Stdlib / extracted leaves -/

@[step]
theorem lift_spec {α} (x : α) : lift x ⦃ _ => True ⦄ := by
  simp [lift]

@[step]
theorem slice_range_get_spec {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice T) s r
      ⦃ _ => True ⦄ := by
  change core.slice.index.SliceIndexRangeUsizeSlice.get r s ⦃ _ => True ⦄
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get
  split <;> simp

@[step]
theorem slice_usize_get_spec {T} (s : Slice T) (i : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i
      ⦃ _ => True ⦄ := by
  unfold core.slice.Slice.get
  simp only [core.slice.index.Usize.get]
  simp

@[step]
theorem slice_range_get_mut_spec {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeUsizeSlice T) s r
      ⦃ _ => True ⦄ := by
  unfold core.slice.Slice.get_mut
  change core.slice.index.SliceIndexRangeUsizeSlice.get_mut r s ⦃ _ => True ⦄
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  split <;> simp

@[step]
theorem from_residual_from_same_spec {T E}
    (residual : core.result.Result core.convert.Infallible E) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T (core.convert.FromSame E) residual ⦃ _ => True ⦄ := by
  unfold core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  spec_split
  · rename_i x; nomatch x
  · simp [core.convert.FromSame]

@[step]
theorem from_residual_codec_to_cose_spec {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      T CoseError.Insts.CoreConvertFromCodecError residual ⦃ _ => True ⦄ := by
  unfold core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  spec_split
  · rename_i x; nomatch x
  · simp [CoseError.Insts.CoreConvertFromCodecError,
      CoseError.Insts.CoreConvertFromCodecError.from]

@[step]
theorem new_spec (buf : Slice U8) : Reader.new buf ⦃ _ => True ⦄ := by
  unfold Reader.new
  simp

@[step]
theorem is_empty_spec (self : Reader) : Reader.is_empty self ⦃ _ => True ⦄ := by
  unfold Reader.is_empty
  simp

@[step]
theorem take_spec (self : Reader) (n : Usize) :
    Reader.take self n ⦃ _ => True ⦄ := by
  unfold Reader.take
  nstep

@[step]
theorem get_u8_spec (bytes : Slice U8) (i : Usize) :
    get_u8 bytes i ⦃ _ => True ⦄ := by
  unfold get_u8
  nstep

@[step]
theorem finish_spec (self : Reader) : Reader.finish self ⦃ _ => True ⦄ := by
  unfold Reader.finish
  nstep

theorem take_no_panic (self : Reader) (n : Usize) : AlwaysOk (Reader.take self n) :=
  of_spec (take_spec self n)

theorem get_u8_no_panic (bytes : Slice U8) (i : Usize) : AlwaysOk (get_u8 bytes i) :=
  of_spec (get_u8_spec bytes i)

theorem branch_no_panic {T E} (r : core.result.Result T E) :
    AlwaysOk (core.result.Result.Insts.CoreOpsTry.branch r) := by
  cases r <;> exact ⟨_, rfl⟩

theorem from_residual_no_panic {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    AlwaysOk
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame CodecError) residual) :=
  of_spec (from_residual_from_same_spec residual)

/-! # `read_head` (U8 additional-info match; `step*` does not terminate here) -/

theorem read_head_always_ok (self : Reader) (major_base : U8) :
    AlwaysOk (Reader.read_head self major_base) := by
  unfold Reader.read_head
  apply AlwaysOk.bind (take_no_panic self (1#usize))
  intro pair
  rcases pair with ⟨r, self1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue val =>
    apply AlwaysOk.bind (get_u8_no_panic val (0#usize))
    intro r1
    apply AlwaysOk.bind (branch_no_panic r1)
    intro cf1
    cases cf1 with
    | Break residual =>
      apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
      intro r2
      exact AlwaysOk.of_ok _
    | Continue val1 =>
      apply AlwaysOk.bind (AlwaysOk.of_lift (val1 &&& MAJOR_MASK))
      intro i
      apply AlwaysOk.ite
      · exact AlwaysOk.of_ok _
      · apply AlwaysOk.bind (AlwaysOk.of_lift (val1 &&& ADDITIONAL_MASK))
        intro additional
        apply AlwaysOk.ite
        · apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro i1
          exact AlwaysOk.of_ok _
        · split
          · apply AlwaysOk.bind (take_no_panic self1 (1#usize))
            intro pair2
            rcases pair2 with ⟨r2, self2⟩
            apply AlwaysOk.bind (branch_no_panic r2)
            intro cf2
            cases cf2 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
              intro r3
              exact AlwaysOk.of_ok _
            | Continue val2 =>
              apply AlwaysOk.bind (get_u8_no_panic val2 (0#usize))
              intro r3
              apply AlwaysOk.bind (branch_no_panic r3)
              intro cf3
              cases cf3 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                intro r4
                exact AlwaysOk.of_ok _
              | Continue val3 =>
                apply AlwaysOk.ite
                · exact AlwaysOk.of_ok _
                · apply AlwaysOk.bind (AlwaysOk.of_lift _)
                  intro i1
                  exact AlwaysOk.of_ok _
          · apply AlwaysOk.bind (take_no_panic self1 (2#usize))
            intro pair2
            rcases pair2 with ⟨r2, self2⟩
            apply AlwaysOk.bind (branch_no_panic r2)
            intro cf2
            cases cf2 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
              intro r3
              exact AlwaysOk.of_ok _
            | Continue val2 =>
              apply AlwaysOk.bind (get_u8_no_panic val2 (0#usize))
              intro r3
              apply AlwaysOk.bind (branch_no_panic r3)
              intro cf3
              cases cf3 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                intro r4
                exact AlwaysOk.of_ok _
              | Continue val3 =>
                apply AlwaysOk.bind (get_u8_no_panic val2 (1#usize))
                intro r4
                apply AlwaysOk.bind (branch_no_panic r4)
                intro cf4
                cases cf4 with
                | Break residual =>
                  apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                  intro r5
                  exact AlwaysOk.of_ok _
                | Continue val4 =>
                  apply AlwaysOk.bind (AlwaysOk.of_lift _)
                  intro i1
                  apply AlwaysOk.bind (AlwaysOk.of_lift _)
                  intro value
                  apply AlwaysOk.bind (AlwaysOk.of_lift _)
                  intro i2
                  apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _
          · apply AlwaysOk.bind (take_no_panic self1 (4#usize))
            intro pair2
            rcases pair2 with ⟨r2, self2⟩
            apply AlwaysOk.bind (branch_no_panic r2)
            intro cf2
            cases cf2 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
              intro r3
              exact AlwaysOk.of_ok _
            | Continue val2 =>
              apply AlwaysOk.bind (get_u8_no_panic val2 (0#usize))
              intro r3
              apply AlwaysOk.bind (branch_no_panic r3)
              intro cf3
              cases cf3 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                intro r4
                exact AlwaysOk.of_ok _
              | Continue val3 =>
                apply AlwaysOk.bind (get_u8_no_panic val2 (1#usize))
                intro r4
                apply AlwaysOk.bind (branch_no_panic r4)
                intro cf4
                cases cf4 with
                | Break residual =>
                  apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                  intro r5
                  exact AlwaysOk.of_ok _
                | Continue val4 =>
                  apply AlwaysOk.bind (get_u8_no_panic val2 (2#usize))
                  intro r5
                  apply AlwaysOk.bind (branch_no_panic r5)
                  intro cf5
                  cases cf5 with
                  | Break residual =>
                    apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                    intro r6
                    exact AlwaysOk.of_ok _
                  | Continue val5 =>
                    apply AlwaysOk.bind (get_u8_no_panic val2 (3#usize))
                    intro r6
                    apply AlwaysOk.bind (branch_no_panic r6)
                    intro cf6
                    cases cf6 with
                    | Break residual =>
                      apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                      intro r7
                      exact AlwaysOk.of_ok _
                    | Continue val6 =>
                      apply AlwaysOk.bind (AlwaysOk.of_lift _)
                      intro i1
                      apply AlwaysOk.bind (AlwaysOk.of_lift _)
                      intro value
                      apply AlwaysOk.bind (AlwaysOk.of_lift _)
                      intro i2
                      apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _
          · apply AlwaysOk.bind (take_no_panic self1 (8#usize))
            intro pair2
            rcases pair2 with ⟨r2, self2⟩
            apply AlwaysOk.bind (branch_no_panic r2)
            intro cf2
            cases cf2 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
              intro r3
              exact AlwaysOk.of_ok _
            | Continue val2 =>
              apply AlwaysOk.bind (get_u8_no_panic val2 (0#usize))
              intro r3
              apply AlwaysOk.bind (branch_no_panic r3)
              intro cf3
              cases cf3 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                intro r4
                exact AlwaysOk.of_ok _
              | Continue val3 =>
                apply AlwaysOk.bind (get_u8_no_panic val2 (1#usize))
                intro r4
                apply AlwaysOk.bind (branch_no_panic r4)
                intro cf4
                cases cf4 with
                | Break residual =>
                  apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                  intro r5
                  exact AlwaysOk.of_ok _
                | Continue val4 =>
                  apply AlwaysOk.bind (get_u8_no_panic val2 (2#usize))
                  intro r5
                  apply AlwaysOk.bind (branch_no_panic r5)
                  intro cf5
                  cases cf5 with
                  | Break residual =>
                    apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                    intro r6
                    exact AlwaysOk.of_ok _
                  | Continue val5 =>
                    apply AlwaysOk.bind (get_u8_no_panic val2 (3#usize))
                    intro r6
                    apply AlwaysOk.bind (branch_no_panic r6)
                    intro cf6
                    cases cf6 with
                    | Break residual =>
                      apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                      intro r7
                      exact AlwaysOk.of_ok _
                    | Continue val6 =>
                      apply AlwaysOk.bind (get_u8_no_panic val2 (4#usize))
                      intro r7
                      apply AlwaysOk.bind (branch_no_panic r7)
                      intro cf7
                      cases cf7 with
                      | Break residual =>
                        apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                        intro r8
                        exact AlwaysOk.of_ok _
                      | Continue val7 =>
                        apply AlwaysOk.bind (get_u8_no_panic val2 (5#usize))
                        intro r8
                        apply AlwaysOk.bind (branch_no_panic r8)
                        intro cf8
                        cases cf8 with
                        | Break residual =>
                          apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                          intro r9
                          exact AlwaysOk.of_ok _
                        | Continue val8 =>
                          apply AlwaysOk.bind (get_u8_no_panic val2 (6#usize))
                          intro r9
                          apply AlwaysOk.bind (branch_no_panic r9)
                          intro cf9
                          cases cf9 with
                          | Break residual =>
                            apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                            intro r10
                            exact AlwaysOk.of_ok _
                          | Continue val9 =>
                            apply AlwaysOk.bind (get_u8_no_panic val2 (7#usize))
                            intro r10
                            apply AlwaysOk.bind (branch_no_panic r10)
                            intro cf10
                            cases cf10 with
                            | Break residual =>
                              apply AlwaysOk.bind (from_residual_no_panic (T := U64) residual)
                              intro r11
                              exact AlwaysOk.of_ok _
                            | Continue val10 =>
                              apply AlwaysOk.bind (AlwaysOk.of_lift _)
                              intro value
                              apply AlwaysOk.bind (AlwaysOk.of_lift _)
                              intro i1
                              apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _
          · apply AlwaysOk.ite
            · apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _
            · exact AlwaysOk.of_ok _

@[step]
theorem read_head_spec (self : Reader) (major_base : U8) :
    Reader.read_head self major_base ⦃ _ => True ⦄ :=
  spec_of_exists (read_head_always_ok self major_base)

@[step]
theorem Reader_read_uint_spec (self : Reader) :
    Reader.read_uint self ⦃ _ => True ⦄ := by
  unfold Reader.read_uint
  nstep

@[step]
theorem Reader_read_bstr_spec (self : Reader) :
    Reader.read_bstr self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr
  nstep

@[step]
theorem Reader_read_bstr_fixed_64_spec (self : Reader) :
    Reader.read_bstr_fixed_64 self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr_fixed_64
  nstep

@[step]
theorem Reader_read_bstr_fixed_16_spec (self : Reader) :
    Reader.read_bstr_fixed_16 self ⦃ _ => True ⦄ := by
  unfold Reader.read_bstr_fixed_16
  nstep

@[step]
theorem Reader_read_array_header_spec (self : Reader) :
    Reader.read_array_header self ⦃ _ => True ⦄ := by
  unfold Reader.read_array_header
  nstep

@[step]
theorem Reader_read_map_header_spec (self : Reader) :
    Reader.read_map_header self ⦃ _ => True ⦄ := by
  unfold Reader.read_map_header
  nstep

@[step]
theorem read_fixed_byte_spec (self : Reader) (expected : U8) :
    Reader.read_fixed_byte self expected ⦃ _ => True ⦄ := by
  unfold Reader.read_fixed_byte
  nstep

@[step]
theorem next_map_key_spec (self : Reader) (last_key : Option U64) :
    Reader.next_map_key self last_key ⦃ _ => True ⦄ := by
  unfold Reader.next_map_key
  nstep

theorem Typ_from_u64_always_ok (value : U64) : AlwaysOk (Typ.from_u64 value) := by
  unfold Typ.from_u64
  split <;> exact ⟨_, rfl⟩

@[step]
theorem Typ_from_u64_spec (value : U64) : Typ.from_u64 value ⦃ _ => True ⦄ :=
  spec_of_exists (Typ_from_u64_always_ok value)

/-! # Public parse theorems -/

/-- For every byte slice, `read_uint` returns `ok _` (decoded `u64` or `CodecError`). -/
theorem read_uint_no_panic (buf : Slice U8) : ∃ r, read_uint buf = ok r := by
  apply of_spec
  unfold read_uint
  nstep

/-- For every byte slice, `read_bstr` returns `ok _` (a slice or `CodecError`). -/
theorem read_bstr_no_panic (buf : Slice U8) : ∃ r, read_bstr buf = ok r := by
  apply of_spec
  unfold read_bstr
  nstep

/-- For every byte slice, `read_bstr_fixed_64` returns `ok _` (64 bytes or `CodecError`). -/
theorem read_bstr_fixed_64_no_panic (buf : Slice U8) :
    ∃ r, read_bstr_fixed_64 buf = ok r := by
  apply of_spec
  unfold read_bstr_fixed_64
  nstep

/-- For every byte slice, `read_array_header` returns `ok _` (a count or `CodecError`). -/
theorem read_array_header_no_panic (buf : Slice U8) :
    ∃ r, read_array_header buf = ok r := by
  apply of_spec
  unfold read_array_header
  nstep

/-- For every byte slice, `read_map_header` returns `ok _` (a count or `CodecError`). -/
theorem read_map_header_no_panic (buf : Slice U8) :
    ∃ r, read_map_header buf = ok r := by
  apply of_spec
  unfold read_map_header
  nstep

@[step]
theorem read_sign1_envelope_spec (buf : Slice U8) :
    read_sign1_envelope buf ⦃ _ => True ⦄ := by
  unfold read_sign1_envelope
  nstep

/-- For every byte slice, `read_sign1_envelope` returns `ok _` (`Envelope` or `CoseError`). -/
theorem read_sign1_envelope_no_panic (buf : Slice U8) :
    ∃ r, read_sign1_envelope buf = ok r :=
  of_spec (read_sign1_envelope_spec buf)

@[step]
theorem decode_protected_header_spec (bytes : Slice U8) :
    decode_protected_header bytes ⦃ _ => True ⦄ := by
  unfold decode_protected_header
  nstep

/-- For every byte slice, `decode_protected_header` returns `ok _`
    (`([u8; 16], Typ)` or `CoseError`). -/
theorem decode_protected_header_no_panic (bytes : Slice U8) :
    ∃ r, decode_protected_header bytes = ok r :=
  of_spec (decode_protected_header_spec bytes)

/-! # `Sig_structure` writer -/

@[step]
theorem SliceSink_new_spec : SliceSink.new ⦃ _ => True ⦄ := by
  unfold SliceSink.new
  simp

@[step]
theorem SliceSink_len_spec (self : SliceSink) :
    SliceSink.impl.len self ⦃ _ => True ⦄ := by
  unfold SliceSink.impl.len
  simp

@[step]
theorem write_bytes_spec (self : SliceSink) (bytes : Slice U8) :
    SliceSink.write_bytes self bytes ⦃ _ => True ⦄ := by
  unfold SliceSink.write_bytes
  step* -threadGrindState

@[step]
theorem be_byte_spec (be : Array U8 8#usize) (i : Usize) :
    be_byte be i ⦃ _ => True ⦄ := by
  unfold be_byte
  nstep

@[step]
theorem write_head_spec (sink : SliceSink) (major_base : U8) (arg : U64) :
    write_head sink major_base arg ⦃ _ => True ⦄ := by
  unfold write_head
  nstep

@[step]
theorem write_bstr_spec (sink : SliceSink) (bytes : Slice U8) :
    write_bstr sink bytes ⦃ _ => True ⦄ := by
  unfold write_bstr
  nstep

@[step]
theorem write_text_spec (sink : SliceSink) (text : Slice U8) :
    write_text sink text ⦃ _ => True ⦄ := by
  unfold write_text
  nstep

@[step]
theorem write_array_header_spec (sink : SliceSink) (len : U64) :
    write_array_header sink len ⦃ _ => True ⦄ := by
  unfold write_array_header
  nstep

@[step]
theorem build_sig_structure_spec (typ : Typ) (protected1 payload : Slice U8) :
    build_sig_structure typ protected1 payload ⦃ _ => True ⦄ := by
  unfold build_sig_structure
  nstep

/-- For every `Typ` and pair of byte slices, `build_sig_structure` returns `ok _`
    (`SigStructure` or `CoseError`). -/
theorem build_sig_structure_no_panic (typ : Typ) (protected1 payload : Slice U8) :
    ∃ r, build_sig_structure typ protected1 payload = ok r :=
  of_spec (build_sig_structure_spec typ protected1 payload)

@[step]
theorem parse_sign1_spec (bytes : Slice U8) :
    parse_sign1 bytes ⦃ _ => True ⦄ := by
  unfold parse_sign1
  nstep
  try rcases val with ⟨kid, typ⟩
  nstep

/-- For every byte slice, `parse_sign1` returns `ok _` (`Parsed` or `CoseError`).
    Composition of envelope + protected header + `Sig_structure`. Not `∀ pubkey`.
    Signature verification is outside this function. -/
theorem parse_sign1_no_panic (bytes : Slice U8) :
    ∃ r, parse_sign1 bytes = ok r :=
  of_spec (parse_sign1_spec bytes)

-- Expected: propext, Classical.choice, Quot.sound. See reports/PROOF.md.
#print axioms read_uint_no_panic
#print axioms read_bstr_no_panic
#print axioms read_bstr_fixed_64_no_panic
#print axioms read_array_header_no_panic
#print axioms read_map_header_no_panic
#print axioms read_sign1_envelope_no_panic
#print axioms decode_protected_header_no_panic
#print axioms build_sig_structure_no_panic
#print axioms parse_sign1_no_panic

end NoPanic
