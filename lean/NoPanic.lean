-- Handwritten no-panic theorem. Aeneas generates `CoseParseNopanic.lean` from
-- `llbc/cose_parse_nopanic.llbc`; this file is not Aeneas output.
--
-- Panic model (Binder spike): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, OOB index, unwrap, ...) is
-- exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A codec
-- rejection is `ok (Result.Err CodecError)` (or `CoseError` on the envelope
-- path) — still `ok`.
--
-- This theorem does not claim RFC 8949 correctness.

import CoseParseNopanic

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open cose_parse_nopanic

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

theorem from_cose_residual_no_panic {T}
    (residual : core.result.Result core.convert.Infallible CodecError) :
    AlwaysOk
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T CoseError.Insts.CoreConvertFromCodecError residual) := by
  cases residual with
  | Ok x => nomatch x
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      CoseError.Insts.CoreConvertFromCodecError,
      CoseError.Insts.CoreConvertFromCodecError.from, bind_tc_ok, AlwaysOk]

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

theorem try_from_array_64_no_panic (val : Slice U8) :
    AlwaysOk (core.array.TryFromArrayCopySlice.try_from 64#usize core.marker.CopyU8 val) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  split <;> exact ⟨_, rfl⟩

theorem Reader_read_bstr_no_panic (self : Reader) : AlwaysOk (Reader.read_bstr self) := by
  unfold Reader.read_bstr
  apply AlwaysOk.bind (read_head_no_panic self MAJOR_BSTR)
  intro pair
  rcases pair with ⟨r, self1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Slice U8) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue val =>
    apply AlwaysOk.bind (AlwaysOk.of_lift (UScalar.cast .U64 core.num.Usize.MAX))
    intro i
    apply AlwaysOk.ite
    · exact AlwaysOk.of_ok _
    · apply AlwaysOk.bind (AlwaysOk.of_lift (UScalar.cast .Usize val))
      intro len
      exact take_no_panic self1 len

/-- For every byte slice, `read_bstr` returns `ok _` (a slice or `CodecError`). -/
theorem read_bstr_no_panic (buf : Slice U8) : ∃ r, read_bstr buf = ok r := by
  unfold read_bstr
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_bstr_no_panic reader)
  intro pair
  rcases pair with ⟨r, _⟩
  exact AlwaysOk.of_ok r

theorem Reader_read_bstr_fixed_64_no_panic (self : Reader) :
    AlwaysOk (Reader.read_bstr_fixed_64 self) := by
  unfold Reader.read_bstr_fixed_64
  apply AlwaysOk.bind (Reader_read_bstr_no_panic self)
  intro pair
  rcases pair with ⟨r, self1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Array U8 64#usize) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue val =>
    apply AlwaysOk.bind (try_from_array_64_no_panic val)
    intro r1
    cases r1 <;> exact AlwaysOk.of_ok _

/-- For every byte slice, `read_bstr_fixed_64` returns `ok _` (64 bytes or `CodecError`). -/
theorem read_bstr_fixed_64_no_panic (buf : Slice U8) :
    ∃ r, read_bstr_fixed_64 buf = ok r := by
  unfold read_bstr_fixed_64
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_bstr_fixed_64_no_panic reader)
  intro pair
  rcases pair with ⟨r, _⟩
  exact AlwaysOk.of_ok r

theorem is_empty_no_panic (self : Reader) : AlwaysOk (Reader.is_empty self) := by
  unfold Reader.is_empty
  exact AlwaysOk.of_ok _

theorem finish_no_panic (self : Reader) : AlwaysOk (Reader.finish self) := by
  unfold Reader.finish
  apply AlwaysOk.bind (is_empty_no_panic self)
  intro b
  apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _

theorem Reader_read_array_header_no_panic (self : Reader) :
    AlwaysOk (Reader.read_array_header self) := by
  unfold Reader.read_array_header
  exact read_head_no_panic self MAJOR_ARRAY

theorem Reader_read_map_header_no_panic (self : Reader) :
    AlwaysOk (Reader.read_map_header self) := by
  unfold Reader.read_map_header
  exact read_head_no_panic self MAJOR_MAP

/-- For every byte slice, `read_array_header` returns `ok _` (a count or `CodecError`). -/
theorem read_array_header_no_panic (buf : Slice U8) :
    ∃ r, read_array_header buf = ok r := by
  unfold read_array_header
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_array_header_no_panic reader)
  intro pair
  rcases pair with ⟨r, _⟩
  exact AlwaysOk.of_ok r

/-- For every byte slice, `read_map_header` returns `ok _` (a count or `CodecError`). -/
theorem read_map_header_no_panic (buf : Slice U8) :
    ∃ r, read_map_header buf = ok r := by
  unfold read_map_header
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_map_header_no_panic reader)
  intro pair
  rcases pair with ⟨r, _⟩
  exact AlwaysOk.of_ok r

/-- For every byte slice, `read_sign1_envelope` returns `ok _` (`Envelope` or `CoseError`). -/
theorem read_sign1_envelope_no_panic (buf : Slice U8) :
    ∃ r, read_sign1_envelope buf = ok r := by
  unfold read_sign1_envelope
  apply AlwaysOk.bind (new_no_panic buf)
  intro reader
  apply AlwaysOk.bind (Reader_read_array_header_no_panic reader)
  intro pair
  rcases pair with ⟨r, reader1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    exact from_cose_residual_no_panic (T := Envelope) residual
  | Continue val =>
    apply AlwaysOk.ite
    · exact AlwaysOk.of_ok _
    · apply AlwaysOk.bind (Reader_read_bstr_no_panic reader1)
      intro pair1
      rcases pair1 with ⟨r1, reader2⟩
      apply AlwaysOk.bind (branch_no_panic r1)
      intro cf1
      cases cf1 with
      | Break residual =>
        exact from_cose_residual_no_panic (T := Envelope) residual
      | Continue val1 =>
        apply AlwaysOk.bind (Reader_read_map_header_no_panic reader2)
        intro pair2
        rcases pair2 with ⟨r2, reader3⟩
        apply AlwaysOk.bind (branch_no_panic r2)
        intro cf2
        cases cf2 with
        | Break residual =>
          exact from_cose_residual_no_panic (T := Envelope) residual
        | Continue val2 =>
          apply AlwaysOk.ite
          · exact AlwaysOk.of_ok _
          · apply AlwaysOk.bind (Reader_read_bstr_no_panic reader3)
            intro pair3
            rcases pair3 with ⟨r3, reader4⟩
            apply AlwaysOk.bind (branch_no_panic r3)
            intro cf3
            cases cf3 with
            | Break residual =>
              exact from_cose_residual_no_panic (T := Envelope) residual
            | Continue val3 =>
              apply AlwaysOk.bind (Reader_read_bstr_fixed_64_no_panic reader4)
              intro pair4
              rcases pair4 with ⟨r4, reader5⟩
              apply AlwaysOk.bind (branch_no_panic r4)
              intro cf4
              cases cf4 with
              | Break residual =>
                exact from_cose_residual_no_panic (T := Envelope) residual
              | Continue val4 =>
                apply AlwaysOk.bind (finish_no_panic reader5)
                intro r5
                apply AlwaysOk.bind (branch_no_panic r5)
                intro cf5
                cases cf5 with
                | Break residual =>
                  exact from_cose_residual_no_panic (T := Envelope) residual
                | Continue _ =>
                  exact AlwaysOk.of_ok _

theorem try_from_array_16_no_panic (val : Slice U8) :
    AlwaysOk (core.array.TryFromArrayCopySlice.try_from 16#usize core.marker.CopyU8 val) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  split <;> exact ⟨_, rfl⟩

theorem Reader_read_bstr_fixed_16_no_panic (self : Reader) :
    AlwaysOk (Reader.read_bstr_fixed_16 self) := by
  unfold Reader.read_bstr_fixed_16
  apply AlwaysOk.bind (Reader_read_bstr_no_panic self)
  intro pair
  rcases pair with ⟨r, self1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Array U8 16#usize) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue val =>
    apply AlwaysOk.bind (try_from_array_16_no_panic val)
    intro r1
    cases r1 <;> exact AlwaysOk.of_ok _

theorem Typ_from_u64_no_panic (value : U64) : AlwaysOk (Typ.from_u64 value) := by
  unfold Typ.from_u64
  split <;> exact AlwaysOk.of_ok _

theorem Reader_read_fixed_byte_no_panic (self : Reader) (expected : U8) :
    AlwaysOk (Reader.read_fixed_byte self expected) := by
  unfold Reader.read_fixed_byte
  apply AlwaysOk.bind (take_no_panic self (1#usize))
  intro pair
  rcases pair with ⟨r, self1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue val =>
    apply AlwaysOk.bind (get_u8_no_panic val (0#usize))
    intro r1
    apply AlwaysOk.bind (branch_no_panic r1)
    intro cf1
    cases cf1 with
    | Break residual =>
      apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
      intro r2
      exact AlwaysOk.of_ok _
    | Continue val1 =>
      apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _

theorem Reader_next_map_key_no_panic (self : Reader) (last_key : Option U64) :
    AlwaysOk (Reader.next_map_key self last_key) := by
  unfold Reader.next_map_key
  apply AlwaysOk.bind (Reader_read_uint_no_panic self)
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
    cases last_key with
    | none => exact AlwaysOk.of_ok _
    | some _ => apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _

/-- For every byte slice, `decode_protected_header` returns `ok _`
    (`([u8; 16], Typ)` or `CoseError`). -/
theorem decode_protected_header_no_panic (bytes : Slice U8) :
    ∃ r, decode_protected_header bytes = ok r := by
  unfold decode_protected_header
  apply AlwaysOk.bind (new_no_panic bytes)
  intro reader
  apply AlwaysOk.bind (Reader_read_map_header_no_panic reader)
  intro pair
  rcases pair with ⟨r, reader1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    exact from_cose_residual_no_panic (T := (Array U8 16#usize) × Typ) residual
  | Continue val =>
    apply AlwaysOk.ite
    · exact AlwaysOk.of_ok _
    · apply AlwaysOk.bind (Reader_next_map_key_no_panic reader1 none)
      intro pair1
      rcases pair1 with ⟨r1, reader2, last_key⟩
      apply AlwaysOk.bind (branch_no_panic r1)
      intro cf1
      cases cf1 with
      | Break residual =>
        exact from_cose_residual_no_panic (T := (Array U8 16#usize) × Typ) residual
      | Continue val1 =>
        apply AlwaysOk.ite
        · exact AlwaysOk.of_ok _
        · apply AlwaysOk.bind (Reader_read_fixed_byte_no_panic reader2 ALG_EDDSA_BYTE)
          intro pair2
          rcases pair2 with ⟨r2, reader3⟩
          cases r2 with
          | Err _ => exact AlwaysOk.of_ok _
          | Ok _ =>
            apply AlwaysOk.bind (Reader_next_map_key_no_panic reader3 last_key)
            intro pair3
            rcases pair3 with ⟨r3, reader4, last_key1⟩
            apply AlwaysOk.bind (branch_no_panic r3)
            intro cf2
            cases cf2 with
            | Break residual =>
              exact from_cose_residual_no_panic (T := (Array U8 16#usize) × Typ) residual
            | Continue val2 =>
              apply AlwaysOk.ite
              · exact AlwaysOk.of_ok _
              · apply AlwaysOk.bind (Reader_read_bstr_fixed_16_no_panic reader4)
                intro pair4
                rcases pair4 with ⟨r4, reader5⟩
                apply AlwaysOk.bind (branch_no_panic r4)
                intro cf3
                cases cf3 with
                | Break residual =>
                  exact from_cose_residual_no_panic (T := (Array U8 16#usize) × Typ) residual
                | Continue val3 =>
                  apply AlwaysOk.bind (Reader_next_map_key_no_panic reader5 last_key1)
                  intro pair5
                  rcases pair5 with ⟨r5, reader6, _⟩
                  apply AlwaysOk.bind (branch_no_panic r5)
                  intro cf4
                  cases cf4 with
                  | Break residual =>
                    exact from_cose_residual_no_panic (T := (Array U8 16#usize) × Typ) residual
                  | Continue val4 =>
                    apply AlwaysOk.ite
                    · exact AlwaysOk.of_ok _
                    · apply AlwaysOk.bind (Reader_read_uint_no_panic reader6)
                      intro pair6
                      rcases pair6 with ⟨r6, reader7⟩
                      apply AlwaysOk.bind (branch_no_panic r6)
                      intro cf5
                      cases cf5 with
                      | Break residual =>
                        exact from_cose_residual_no_panic
                          (T := (Array U8 16#usize) × Typ) residual
                      | Continue val5 =>
                        apply AlwaysOk.bind (Typ_from_u64_no_panic val5)
                        intro r7
                        cases r7 with
                        | Err _ => exact AlwaysOk.of_ok _
                        | Ok _ =>
                          apply AlwaysOk.bind (finish_no_panic reader7)
                          intro r8
                          apply AlwaysOk.bind (branch_no_panic r8)
                          intro cf6
                          cases cf6 with
                          | Break residual =>
                            exact from_cose_residual_no_panic
                              (T := (Array U8 16#usize) × Typ) residual
                          | Continue _ =>
                            exact AlwaysOk.of_ok _

theorem range_get_mut_no_panic {T} (s : Slice T) (r : core.ops.range.Range Usize) :
    AlwaysOk (core.slice.Slice.get_mut (core.slice.index.SliceIndexRangeUsizeSlice T) s r) := by
  unfold core.slice.Slice.get_mut
  change AlwaysOk (core.slice.index.SliceIndexRangeUsizeSlice.get_mut r s)
  unfold core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  split <;> exact ⟨_, rfl⟩

theorem copy_from_slice_length_eq_no_panic (s src : Slice U8)
    (h : s.val.length = src.val.length) :
    AlwaysOk (core.slice.Slice.copy_from_slice core.marker.CopyU8 s src) := by
  unfold core.slice.Slice.copy_from_slice
  split
  · exact ⟨_, rfl⟩
  · next hne =>
    have hlen : s.len = src.len :=
      UScalar.eq_of_val_eq (by simp [Slice.len_val, h])
    exact (hne hlen).elim

theorem SliceSink_new_no_panic : AlwaysOk SliceSink.new := by
  unfold SliceSink.new
  exact ⟨_, rfl⟩

theorem SliceSink_len_no_panic (self : SliceSink) : AlwaysOk (SliceSink.impl.len self) := by
  unfold SliceSink.impl.len
  exact AlwaysOk.of_ok _

theorem SliceSink_write_bytes_no_panic (self : SliceSink) (bytes : Slice U8) :
    AlwaysOk (SliceSink.write_bytes self bytes) := by
  unfold SliceSink.write_bytes
  apply AlwaysOk.bind (AlwaysOk.of_lift (Usize.checked_add self.len (Slice.len bytes)))
  intro o
  cases o with
  | none => exact AlwaysOk.of_ok _
  | some end1 =>
    apply AlwaysOk.bind (AlwaysOk.of_lift (Array.to_slice_mut self.buf))
    intro pair
    rcases pair with ⟨s, _to_slice_mut_back⟩
    apply AlwaysOk.bind
      (range_get_mut_no_panic s { start := self.len, «end» := end1 })
    intro pair1
    rcases pair1 with ⟨o1, _get_mut_back⟩
    cases o1 with
    | none => exact AlwaysOk.of_ok _
    | some dest =>
      simp
      split
      · next h =>
        obtain ⟨dest1, hd⟩ := copy_from_slice_length_eq_no_panic dest bytes h
        simp only [hd, bind_tc_ok]
        exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩

theorem be_byte_no_panic (be : Array U8 8#usize) (i : Usize) :
    AlwaysOk (be_byte be i) := by
  unfold be_byte
  apply AlwaysOk.bind (AlwaysOk.of_lift _)
  intro s
  apply AlwaysOk.bind (usize_get_no_panic (T := U8) s i)
  intro o
  cases o <;> exact AlwaysOk.of_ok _

theorem write_head_no_panic (sink : SliceSink) (major_base : U8) (arg : U64) :
    AlwaysOk (write_head sink major_base arg) := by
  unfold write_head
  apply AlwaysOk.ite
  · apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro small
    apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro i
    apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro s
    exact SliceSink_write_bytes_no_panic sink s
  · apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro be
    apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro i
    apply AlwaysOk.ite
    · apply AlwaysOk.bind (be_byte_no_panic be (7#usize))
      intro r
      apply AlwaysOk.bind (branch_no_panic r)
      intro cf
      cases cf with
      | Break residual =>
        apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
        intro r1
        exact AlwaysOk.of_ok _
      | Continue val =>
        apply AlwaysOk.bind (AlwaysOk.of_lift _)
        intro i1
        apply AlwaysOk.bind (AlwaysOk.of_lift _)
        intro s
        exact SliceSink_write_bytes_no_panic sink s
    · apply AlwaysOk.bind (AlwaysOk.of_lift _)
      intro i1
      apply AlwaysOk.ite
      · apply AlwaysOk.bind (AlwaysOk.of_lift _)
        intro i2
        apply AlwaysOk.bind (be_byte_no_panic be (6#usize))
        intro r
        apply AlwaysOk.bind (branch_no_panic r)
        intro cf
        cases cf with
        | Break residual =>
          apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
          intro r1
          exact AlwaysOk.of_ok _
        | Continue val =>
          apply AlwaysOk.bind (be_byte_no_panic be (7#usize))
          intro r1
          apply AlwaysOk.bind (branch_no_panic r1)
          intro cf1
          cases cf1 with
          | Break residual =>
            apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
            intro r2
            exact AlwaysOk.of_ok _
          | Continue val1 =>
            apply AlwaysOk.bind (AlwaysOk.of_lift _)
            intro s
            exact SliceSink_write_bytes_no_panic sink s
      · apply AlwaysOk.bind (AlwaysOk.of_lift _)
        intro i2
        apply AlwaysOk.ite
        · apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro i3
          apply AlwaysOk.bind (be_byte_no_panic be (4#usize))
          intro r
          apply AlwaysOk.bind (branch_no_panic r)
          intro cf
          cases cf with
          | Break residual =>
            apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
            intro r1
            exact AlwaysOk.of_ok _
          | Continue val =>
            apply AlwaysOk.bind (be_byte_no_panic be (5#usize))
            intro r1
            apply AlwaysOk.bind (branch_no_panic r1)
            intro cf1
            cases cf1 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
              intro r2
              exact AlwaysOk.of_ok _
            | Continue val1 =>
              apply AlwaysOk.bind (be_byte_no_panic be (6#usize))
              intro r2
              apply AlwaysOk.bind (branch_no_panic r2)
              intro cf2
              cases cf2 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                intro r3
                exact AlwaysOk.of_ok _
              | Continue val2 =>
                apply AlwaysOk.bind (be_byte_no_panic be (7#usize))
                intro r3
                apply AlwaysOk.bind (branch_no_panic r3)
                intro cf3
                cases cf3 with
                | Break residual =>
                  apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                  intro r4
                  exact AlwaysOk.of_ok _
                | Continue val3 =>
                  apply AlwaysOk.bind (AlwaysOk.of_lift _)
                  intro s
                  exact SliceSink_write_bytes_no_panic sink s
        · apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro i3
          apply AlwaysOk.bind (be_byte_no_panic be (0#usize))
          intro r
          apply AlwaysOk.bind (branch_no_panic r)
          intro cf
          cases cf with
          | Break residual =>
            apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
            intro r1
            exact AlwaysOk.of_ok _
          | Continue val =>
            apply AlwaysOk.bind (be_byte_no_panic be (1#usize))
            intro r1
            apply AlwaysOk.bind (branch_no_panic r1)
            intro cf1
            cases cf1 with
            | Break residual =>
              apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
              intro r2
              exact AlwaysOk.of_ok _
            | Continue val1 =>
              apply AlwaysOk.bind (be_byte_no_panic be (2#usize))
              intro r2
              apply AlwaysOk.bind (branch_no_panic r2)
              intro cf2
              cases cf2 with
              | Break residual =>
                apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                intro r3
                exact AlwaysOk.of_ok _
              | Continue val2 =>
                apply AlwaysOk.bind (be_byte_no_panic be (3#usize))
                intro r3
                apply AlwaysOk.bind (branch_no_panic r3)
                intro cf3
                cases cf3 with
                | Break residual =>
                  apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                  intro r4
                  exact AlwaysOk.of_ok _
                | Continue val3 =>
                  apply AlwaysOk.bind (be_byte_no_panic be (4#usize))
                  intro r4
                  apply AlwaysOk.bind (branch_no_panic r4)
                  intro cf4
                  cases cf4 with
                  | Break residual =>
                    apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                    intro r5
                    exact AlwaysOk.of_ok _
                  | Continue val4 =>
                    apply AlwaysOk.bind (be_byte_no_panic be (5#usize))
                    intro r5
                    apply AlwaysOk.bind (branch_no_panic r5)
                    intro cf5
                    cases cf5 with
                    | Break residual =>
                      apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                      intro r6
                      exact AlwaysOk.of_ok _
                    | Continue val5 =>
                      apply AlwaysOk.bind (be_byte_no_panic be (6#usize))
                      intro r6
                      apply AlwaysOk.bind (branch_no_panic r6)
                      intro cf6
                      cases cf6 with
                      | Break residual =>
                        apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                        intro r7
                        exact AlwaysOk.of_ok _
                      | Continue val6 =>
                        apply AlwaysOk.bind (be_byte_no_panic be (7#usize))
                        intro r7
                        apply AlwaysOk.bind (branch_no_panic r7)
                        intro cf7
                        cases cf7 with
                        | Break residual =>
                          apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
                          intro r8
                          exact AlwaysOk.of_ok _
                        | Continue val7 =>
                          apply AlwaysOk.bind (AlwaysOk.of_lift _)
                          intro s
                          exact SliceSink_write_bytes_no_panic sink s

theorem write_bstr_no_panic (sink : SliceSink) (bytes : Slice U8) :
    AlwaysOk (write_bstr sink bytes) := by
  unfold write_bstr
  apply AlwaysOk.bind (AlwaysOk.of_lift _)
  intro len
  apply AlwaysOk.bind (write_head_no_panic sink MAJOR_BSTR len)
  intro pair
  rcases pair with ⟨r, sink1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue _ =>
    exact SliceSink_write_bytes_no_panic sink1 bytes

theorem write_text_no_panic (sink : SliceSink) (text : Slice U8) :
    AlwaysOk (write_text sink text) := by
  unfold write_text
  apply AlwaysOk.bind (AlwaysOk.of_lift _)
  intro len
  apply AlwaysOk.bind (write_head_no_panic sink MAJOR_TEXT len)
  intro pair
  rcases pair with ⟨r, sink1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    apply AlwaysOk.bind (from_residual_no_panic (T := Unit) residual)
    intro r1
    exact AlwaysOk.of_ok _
  | Continue _ =>
    exact SliceSink_write_bytes_no_panic sink1 text

theorem write_array_header_no_panic (sink : SliceSink) (len : U64) :
    AlwaysOk (write_array_header sink len) := by
  unfold write_array_header
  exact write_head_no_panic sink MAJOR_ARRAY len

theorem sig_payload_finish_no_panic (sink : SliceSink) (payload : Slice U8) :
    AlwaysOk
      (do
        let (r4, sink5) ← write_bstr sink payload
        let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
        match cf4 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let written_len ← SliceSink.impl.len sink5
          if written_len > MAX_MESSAGE_LEN then
            ok (core.result.Result.Err (CoseError.Codec CodecError.BufferTooSmall))
          else
            ok (core.result.Result.Ok
              ({ buf := sink5.buf, len := written_len } : SigStructure))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            SigStructure CoseError.Insts.CoreConvertFromCodecError residual) := by
  apply AlwaysOk.bind (write_bstr_no_panic sink payload)
  intro pair
  rcases pair with ⟨r4, sink5⟩
  apply AlwaysOk.bind (branch_no_panic r4)
  intro cf4
  cases cf4 with
  | Break residual =>
    exact from_cose_residual_no_panic (T := SigStructure) residual
  | Continue _ =>
    apply AlwaysOk.bind (SliceSink_len_no_panic sink5)
    intro written_len
    apply AlwaysOk.ite <;> exact AlwaysOk.of_ok _

theorem sig_after_aad_no_panic (sink : SliceSink) (aad payload : Slice U8) :
    AlwaysOk
      (do
        let (r3, sink4) ← write_bstr sink aad
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let (r4, sink5) ← write_bstr sink4 payload
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let written_len ← SliceSink.impl.len sink5
            if written_len > MAX_MESSAGE_LEN then
              ok (core.result.Result.Err (CoseError.Codec CodecError.BufferTooSmall))
            else
              ok (core.result.Result.Ok
                ({ buf := sink5.buf, len := written_len } : SigStructure))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              SigStructure CoseError.Insts.CoreConvertFromCodecError residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            SigStructure CoseError.Insts.CoreConvertFromCodecError residual) := by
  apply AlwaysOk.bind (write_bstr_no_panic sink aad)
  intro pair
  rcases pair with ⟨r3, sink4⟩
  apply AlwaysOk.bind (branch_no_panic r3)
  intro cf3
  cases cf3 with
  | Break residual =>
    exact from_cose_residual_no_panic (T := SigStructure) residual
  | Continue _ =>
    exact sig_payload_finish_no_panic sink4 payload

/-- For every `Typ` and pair of byte slices, `build_sig_structure` returns `ok _`
    (`SigStructure` or `CoseError`). -/
theorem build_sig_structure_no_panic (typ : Typ) (protected1 payload : Slice U8) :
    ∃ r, build_sig_structure typ protected1 payload = ok r := by
  unfold build_sig_structure
  apply AlwaysOk.bind SliceSink_new_no_panic
  intro sink
  apply AlwaysOk.bind (write_array_header_no_panic sink (4#u64))
  intro pair
  rcases pair with ⟨r, sink1⟩
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    exact from_cose_residual_no_panic (T := SigStructure) residual
  | Continue _ =>
    apply AlwaysOk.bind (AlwaysOk.of_lift _)
    intro s
    apply AlwaysOk.bind (write_text_no_panic sink1 s)
    intro pair1
    rcases pair1 with ⟨r1, sink2⟩
    apply AlwaysOk.bind (branch_no_panic r1)
    intro cf1
    cases cf1 with
    | Break residual =>
      exact from_cose_residual_no_panic (T := SigStructure) residual
    | Continue _ =>
      apply AlwaysOk.bind (write_bstr_no_panic sink2 protected1)
      intro pair2
      rcases pair2 with ⟨r2, sink3⟩
      apply AlwaysOk.bind (branch_no_panic r2)
      intro cf2
      cases cf2 with
      | Break residual =>
        exact from_cose_residual_no_panic (T := SigStructure) residual
      | Continue _ =>
        cases typ with
        | License =>
          apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro s1
          exact sig_after_aad_no_panic sink3 s1 payload
        | Enroll =>
          apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro s1
          exact sig_after_aad_no_panic sink3 s1 payload
        | Revoke =>
          apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro s1
          exact sig_after_aad_no_panic sink3 s1 payload
        | TrustUpdate =>
          apply AlwaysOk.bind (AlwaysOk.of_lift _)
          intro s1
          exact sig_after_aad_no_panic sink3 s1 payload

theorem from_cose_same_residual_no_panic {T}
    (residual : core.result.Result core.convert.Infallible CoseError) :
    AlwaysOk
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T (core.convert.FromSame CoseError) residual) := by
  cases residual with
  | Ok x => nomatch x
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame, bind_tc_ok, AlwaysOk]

/-- For every byte slice, `parse_sign1` returns `ok _` (`Parsed` or `CoseError`).
    Composition of envelope + protected header + `Sig_structure`. Not `∀ pubkey`.
    Signature verification is outside this function. -/
theorem parse_sign1_no_panic (bytes : Slice U8) :
    ∃ r, parse_sign1 bytes = ok r := by
  unfold parse_sign1
  apply AlwaysOk.bind (read_sign1_envelope_no_panic bytes)
  intro r
  apply AlwaysOk.bind (branch_no_panic r)
  intro cf
  cases cf with
  | Break residual =>
    exact from_cose_same_residual_no_panic (T := Parsed) residual
  | Continue e =>
    apply AlwaysOk.bind (decode_protected_header_no_panic e.protected)
    intro r1
    apply AlwaysOk.bind (branch_no_panic r1)
    intro cf1
    cases cf1 with
    | Break residual =>
      exact from_cose_same_residual_no_panic (T := Parsed) residual
    | Continue val =>
      rcases val with ⟨kid, typ⟩
      apply AlwaysOk.bind (build_sig_structure_no_panic typ e.protected e.payload)
      intro r2
      apply AlwaysOk.bind (branch_no_panic r2)
      intro cf2
      cases cf2 with
      | Break residual =>
        exact from_cose_same_residual_no_panic (T := Parsed) residual
      | Continue _ =>
        exact AlwaysOk.of_ok _

-- Expected: propext, Classical.choice, Quot.sound. See reports/PROOF.md,
-- reports/PROOF-bstr.md, reports/PROOF-envelope.md, reports/PROOF-header.md,
-- reports/PROOF-sig.md, and reports/PROOF-parse.md.
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
