import Mathlib
import Mathieu.BasicM11
import Mathieu.BasicM12
import Mathieu.BasicM23
import Mathieu.BasicM24

/-!
# Primitivity of the Mathieu actions

The natural action of each Mathieu group is **primitive** (`IsPreprimitive`), hence
**quasi-primitive** (`IsQuasiPreprimitive`).  This is the first ingredient of the Iwasawa
criterion for simplicity (see `PLAN.md` §3.5).

Primitivity follows immediately from `2`-transitivity
(`MulAction.isPreprimitive_of_is_two_pretransitive`), and each Mathieu group is at least
`2`-transitive (indeed `M₁₁` is `4`-transitive, `M₁₂` and `M₂₄` are `5`-transitive, `M₂₃`
is `4`-transitive, and `M₂₂` is `3`-transitive on its `22`-point set).

The relevant `FaithfulSMul` instances are automatic (a subgroup of `Equiv.Perm α` acts
faithfully on `α`).
-/

namespace Mathieu

open MulAction

/-- `M₁₁` acts primitively on its `11` points. -/
instance M11_isPreprimitive : IsPreprimitive (↥M11) (Fin 11) := by
  haveI : IsMultiplyPretransitive (↥M11) (Fin 11) 4 := M11_isMultiplyPretransitive_four
  haveI h2 : IsMultiplyPretransitive (↥M11) (Fin 11) 2 :=
    isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)
  exact isPreprimitive_of_is_two_pretransitive h2

/-- `M₁₂` acts primitively on its `12` points. -/
instance M12_isPreprimitive : IsPreprimitive (↥M12) (Fin 12) := by
  haveI : IsMultiplyPretransitive (↥M12) (Fin 12) 5 := M12_isMultiplyPretransitive_five
  haveI h2 : IsMultiplyPretransitive (↥M12) (Fin 12) 2 :=
    isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by simp)
  exact isPreprimitive_of_is_two_pretransitive h2

/-- `M₂₃` acts primitively on its `23` points. -/
instance M23_isPreprimitive : IsPreprimitive (↥M23) (Fin 23) := by
  haveI : IsMultiplyPretransitive (↥M23) (Fin 23) 4 := M23_isMultiplyPretransitive_four
  haveI h2 : IsMultiplyPretransitive (↥M23) (Fin 23) 2 :=
    isMultiplyPretransitive_of_le (n := 4) (by norm_num) (by simp)
  exact isPreprimitive_of_is_two_pretransitive h2

/-- `M₂₄` acts primitively on its `24` points. -/
instance M24_isPreprimitive : IsPreprimitive (↥M24) (Fin 24) := by
  haveI : IsMultiplyPretransitive (↥M24) (Fin 24) 5 := M24_isMultiplyPretransitive_five
  haveI h2 : IsMultiplyPretransitive (↥M24) (Fin 24) 2 :=
    isMultiplyPretransitive_of_le (n := 5) (by norm_num) (by simp)
  exact isPreprimitive_of_is_two_pretransitive h2

/-- The cardinality of the `22`-point set on which `M₂₂` acts. -/
theorem card_ofStabilizer_M23_22 :
    Nat.card (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) = 22 := by
  have h : Nat.card (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23))
      = Nat.card ({(22 : Fin 23)}ᶜ : Set (Fin 23)) := rfl
  rw [h, Nat.card_eq_fintype_card, Fintype.card_compl_set]
  simp

/-- `M₂₂` (= the stabiliser of `22` in `M₂₃`) acts primitively on the remaining `22` points. -/
instance M22_isPreprimitive :
    IsPreprimitive (stabilizer (↥M23) (22 : Fin 23))
      (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) := by
  haveI : IsMultiplyPretransitive (stabilizer (↥M23) (22 : Fin 23))
      (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) 3 := M22_isMultiplyPretransitive_three
  haveI h2 : IsMultiplyPretransitive (stabilizer (↥M23) (22 : Fin 23))
      (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) 2 :=
    isMultiplyPretransitive_of_le (n := 3) (by norm_num)
      (by rw [card_ofStabilizer_M23_22]; norm_num)
  exact isPreprimitive_of_is_two_pretransitive h2

/-! Quasi-primitivity (the precise hypothesis of the Iwasawa criterion) follows from
primitivity via `MulAction.IsPreprimitive.isQuasiPreprimitive`. -/

example : IsQuasiPreprimitive (↥M11) (Fin 11) := inferInstance
example : IsQuasiPreprimitive (↥M12) (Fin 12) := inferInstance
example : IsQuasiPreprimitive (↥M23) (Fin 23) := inferInstance
example : IsQuasiPreprimitive (↥M24) (Fin 24) := inferInstance
example : IsQuasiPreprimitive (stabilizer (↥M23) (22 : Fin 23))
    (SubMulAction.ofStabilizer (↥M23) (22 : Fin 23)) := inferInstance

/-! Faithfulness of the actions (automatic). -/
example : FaithfulSMul (↥M11) (Fin 11) := inferInstance
example : FaithfulSMul (↥M12) (Fin 12) := inferInstance
example : FaithfulSMul (↥M23) (Fin 23) := inferInstance
example : FaithfulSMul (↥M24) (Fin 24) := inferInstance

end Mathieu
