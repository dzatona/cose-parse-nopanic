-- Handwritten no-panic theorem. Aeneas generates `CborNopanic.lean` from
-- `llbc/cbor_nopanic.llbc`; this file is not Aeneas output.
--
-- Panic model (Binder spike / panic model): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, OOB index, unwrap, ...) is
-- exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A codec
-- rejection is `ok (Result.Err CodecError)` — still `ok`.
--
-- This theorem does not claim RFC 8949 correctness.

import CborNopanic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open cbor_nopanic

set_option linter.unusedSimpArgs false

namespace NoPanic

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

theorem range_get_no_panic {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    AlwaysOk (core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice T) s r) := by
  change AlwaysOk (core.slice.index.SliceIndexRangeUsizeSlice.get r s)
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get
  split <;> exact ⟨_, rfl⟩

theorem usize_get_no_panic {T} (s : Slice T) (i : Usize) :
    AlwaysOk (core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice T) s i) := by
  unfold core.slice.Slice.get
  simp only [core.slice.index.Usize.get]
  exact ⟨_, rfl⟩

theorem take_no_panic (self : Reader) (n : Usize) : AlwaysOk (Reader.take self n) := by
  unfold Reader.take
  simp only [lift, bind_tc_ok]
  cases Usize.checked_add self.pos n with
  | none => exact ⟨_, rfl⟩
  | some end1 =>
    obtain ⟨o1, ho1⟩ := range_get_no_panic self.buf { start := self.pos, «end» := end1 }
    simp only [ho1, bind_tc_ok]
    cases o1 <;> exact ⟨_, rfl⟩

theorem get_u8_no_panic (bytes : Slice U8) (i : Usize) : AlwaysOk (get_u8 bytes i) := by
  unfold get_u8
  obtain ⟨o, ho⟩ := usize_get_no_panic (T := U8) bytes i
  simp only [ho, bind_tc_ok]
  cases o <;> exact ⟨_, rfl⟩

theorem branch_no_panic {T E} (r : core.result.Result T E) :
    AlwaysOk (core.result.Result.Insts.CoreOpsTry.branch r) := by
  cases r <;> exact ⟨_, rfl⟩

theorem from_residual_no_panic {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    AlwaysOk
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame CodecError) residual) := by
  cases residual with
  | Ok x => nomatch x
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame, bind_tc_ok, AlwaysOk]

theorem new_no_panic (buf : Slice U8) : AlwaysOk (Reader.new buf) :=
  ⟨_, rfl⟩

theorem read_head_no_panic (self : Reader) (major_base : U8) :
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
        · -- additional ≥ 24: 1-byte / 2-byte / 4-byte / 8-byte / reserved
          split
          · -- 24
            apply AlwaysOk.bind (take_no_panic self1 (1#usize))
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
          · -- 25
            apply AlwaysOk.bind (take_no_panic self1 (2#usize))
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
          · -- 26
            apply AlwaysOk.bind (take_no_panic self1 (4#usize))
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
          · -- 27
            apply AlwaysOk.bind (take_no_panic self1 (8#usize))
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
          · -- reserved / indefinite
            apply AlwaysOk.ite
            · apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _
            · exact AlwaysOk.of_ok _

theorem Reader_read_uint_no_panic (self : Reader) : AlwaysOk (Reader.read_uint self) := by
  unfold Reader.read_uint
  exact read_head_no_panic self MAJOR_UNSIGNED

/-- For every byte slice, `read_uint` returns `ok _` (decoded `u64` or `CodecError`). -/
theorem read_uint_no_panic (buf : Slice U8) : ∃ r, read_uint buf = ok r := by
  unfold read_uint
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_uint_no_panic reader)
  intro pair
  rcases pair with ⟨r, _⟩
  exact AlwaysOk.of_ok r

-- Expected: propext, Classical.choice, Quot.sound. See reports/PROOF.md.
#print axioms read_uint_no_panic

end NoPanic
