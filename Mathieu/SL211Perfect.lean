import Mathieu.SL211Gen

/-!
# Perfectness of `SL(2, 𝔽₁₁)`

`SL(2, 𝔽₁₁)` is a **perfect** group: its commutator subgroup is the whole group.  The proof is
the classical one — every elementary transvection is a commutator with a diagonal matrix, and
transvections generate `SL(2, 𝔽₁₁)` (`SL211Gen.closure_eq_top`).  No `native_decide` is used.

Concretely, with `d = diag(2, 6)` (note `2 · 6 = 1` in `𝔽₁₁`):
`⁅d, upper b⁆ = upper ((2² - 1) b) = upper (3 b)` and `⁅d, lower b⁆ = upper ((2⁻² - 1) b)`,
so both standard generators `S = upper 1` and `T = lower 1` are commutators.
-/

namespace Mathieu

open Matrix
open scoped MatrixGroups

namespace SL211Gen

/-- The diagonal matrix `diag(2, 6) ∈ SL(2, 𝔽₁₁)` (`2 · 6 = 1`). -/
def diagElt : SL(2, ZMod 11) := ⟨!![2,0;0,6], by decide⟩

/-
`S = upper 1` is a commutator, hence lies in the commutator subgroup.
-/
theorem Smat_mem_commutator : Smat ∈ commutator (SL(2, ZMod 11)) := by
  -- To prove the first part, we show that `Smat` is a commutator.
  have hSmat : Smat = ⁅diagElt, upper 4⁆ := by
    erw [ Subtype.ext_iff ] ; simp +decide [ ] ;
  rw [hSmat, commutator_def];
  exact Subgroup.commutator_mem_commutator ( Subgroup.mem_top _ ) ( Subgroup.mem_top _ )

/-
`T = lower 1` is a commutator, hence lies in the commutator subgroup.
-/
theorem Tmat_mem_commutator : Tmat ∈ commutator (SL(2, ZMod 11)) := by
  -- The key identity is `Tmat = ⁅diagElt, lower 6⁆` where `⁅a,b⁆ = a * b * a⁻¹ * b⁻¹`.
  have hkey : Tmat = ⁅diagElt, lower 6⁆ := by
    erw [ Subtype.ext_iff ] ; simp +decide [ ] ;
  exact hkey ▸ Subgroup.commutator_mem_commutator ( Subgroup.mem_top _ ) ( Subgroup.mem_top _ )

/-- **`SL(2, 𝔽₁₁)` is perfect.**  Its commutator subgroup is everything. -/
theorem commutator_eq_top : commutator (SL(2, ZMod 11)) = ⊤ := by
  rw [eq_top_iff, ← closure_eq_top]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x hx
  rcases hx with rfl | rfl
  · exact Smat_mem_commutator
  · exact Tmat_mem_commutator

end SL211Gen

end Mathieu