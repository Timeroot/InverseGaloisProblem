import Mathlib
import InverseGalois.CFT.Brauer.BaseChange

/-!
# Relative Brauer groups in a tower

The relative Brauer group `Br(L / K)` is the kernel of base change `Br(K) → Br(L)`, so it grows
with `L`: a class split by `L` is split by any extension of `L`.  This file records that
monotonicity, together with the two degenerate cases — nothing is split by `K` itself beyond the
trivial class, and everything is split by an algebraically closed extension.

## Main results

* `BrauerGroup.relative_self`: the relative Brauer group of the trivial extension is trivial.
* `BrauerGroup.relative_le_relative`: `Br(L / K) ≤ Br(M / K)` for a tower `K ⊆ L ⊆ M`.
* `BrauerGroup.relative_mono`: the same, phrased for two intermediate fields of a common
  extension.
-/

universe u

namespace BrauerGroup

/-- Only the trivial class is split by the base field itself. -/
theorem relative_self (K : Type u) [Field K] : relative K K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  rw [relative, MonoidHom.mem_ker, baseChangeHom_self] at hx
  exact hx

/-- **A class split by `L` is split by any extension of `L`.** -/
theorem relative_le_relative (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] : relative K L ≤ relative K M := by
  intro x hx
  rw [relative, MonoidHom.mem_ker, ← baseChangeHom_comp K L M, MonoidHom.comp_apply]
  rw [relative, MonoidHom.mem_ker] at hx
  rw [hx, map_one]

/-- The relative Brauer groups of the intermediate fields of a fixed extension are ordered by
inclusion. -/
theorem relative_mono {K M : Type u} [Field K] [Field M] [Algebra K M]
    {A B : IntermediateField K M} (h : A ≤ B) : relative K A ≤ relative K B := by
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K ↥A ↥B :=
    IsScalarTower.of_algebraMap_eq fun x => by rfl
  exact relative_le_relative K ↥A ↥B

end BrauerGroup
