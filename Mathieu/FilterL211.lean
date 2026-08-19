import Mathieu.ActL211

/-!
# The centre of `SL(2,𝔽₁₁)` is `{±I}`

The single fact needed for the faithfulness-modulo-centre step of the exceptional action
(`PSL211.ker_eq_center`): the centre of `SL(2, 𝔽₁₁)` is `{±I}`.  This is a special case of
Mathlib's characterisation `Matrix.SpecialLinearGroup.mem_center_iff` (the scalar matrices
`r·I` with `r² = 1`, and `r² = 1` in `𝔽₁₁` forces `r = ±1`).

This file is now **`native_decide`-free**: the earlier `native_decide` enumerations
`kerFilter` / `centerFilter` (which quantified over all of `SL(2,𝔽₁₁)`) have been removed —
`ker_eq_center` is now proved structurally from the simplicity of `PSL(2,𝔽₁₁)`.
-/

namespace Mathieu

open Matrix Equiv
open scoped MatrixGroups

namespace PSL211

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- **The centre of `SL(2, 𝔽₁₁)` is `{±I}`.** -/
lemma center_eq_pm_one (g : SL(2, ZMod 11)) :
    g ∈ Subgroup.center (SL(2, ZMod 11)) ↔ g = 1 ∨ g = -1 := by
  revert g;
  intro g
  rw [Matrix.SpecialLinearGroup.mem_center_iff];
  constructor;
  · rintro ⟨ r, hr, hr' ⟩;
    fin_cases r <;> simp +decide at hr hr' ⊢;
    · exact Or.inl <| Subtype.ext hr'.symm;
    · exact Or.inr <| Subtype.ext <| hr'.symm.trans <| by ext i j; fin_cases i <;> fin_cases j <;> rfl;
  · rintro ( rfl | rfl ) <;> [ refine' ⟨ 1, _, _ ⟩ ; refine' ⟨ -1, _, _ ⟩ ] <;> norm_cast

end PSL211

end Mathieu
