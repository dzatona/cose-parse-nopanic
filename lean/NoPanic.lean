-- Handwritten no-panic theorem. Aeneas generates `CborNopanic.lean` from
-- `llbc/cbor_nopanic.llbc`; this file is not Aeneas output.
--
-- Panic model (Binder spike / panic model): Aeneas puts every function in the `Result`
-- monad `ok v | fail e | div`. A panic (overflow, OOB index, unwrap, ...) is
-- exactly `fail`. No-panic is `∀ inputs, ∃ v, f inputs = ok v`. A codec
-- rejection is `ok (Result.Err CodecError)` (or `CoseError` on the envelope
-- path) — still `ok`.
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

-- Expected: propext, Classical.choice, Quot.sound. See reports/PROOF.md,
-- reports/PROOF-bstr.md, reports/PROOF-envelope.md, and reports/PROOF-header.md.
#print axioms read_uint_no_panic
#print axioms read_bstr_no_panic
#print axioms read_bstr_fixed_64_no_panic
#print axioms read_array_header_no_panic
#print axioms read_map_header_no_panic
#print axioms read_sign1_envelope_no_panic
#print axioms decode_protected_header_no_panic

end NoPanic
