/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.FrobeniusBaseChange

/-!
# The Frobenius automorphism over a base field with the same residues

Let `k ⊆ M ⊆ N` be a tower of nonarchimedean local fields in which the absolute value of `M`
extends the absolute value of `k`, and suppose `M` has no more residues than `k`.  The absolute
value of `N` is then the same whether computed over `k` or over `M`, and raising a residue to the
power counted by the residues of `M` is the same as raising it to the power counted by the residues
of `k`.  So an automorphism of `N` over `M` is a Frobenius automorphism over `M` exactly when it is
a Frobenius automorphism over `k`.

Nothing here asks `M / k` to be unramified; on the contrary, the interesting case is the opposite
one, a totally ramified `M / k`, where the residues really are unchanged.  Combined with the fact
that a Frobenius automorphism restricts to a Frobenius automorphism, this says that **the Frobenius
automorphism of an unramified extension of `M` restricts to the Frobenius automorphism of an
unramified extension of `k` inside it.**

## Main results

* `InverseGalois.CFT.isDivisionFrobenius_restrictScalars`: **an automorphism of an extension of a
  base field with the same residues is a Frobenius automorphism over the smaller base field as soon
  as it is one over the larger.**
* `InverseGalois.CFT.restrictNormal_restrictScalars_divisionFrobenius`: **the Frobenius
  automorphism of an unramified extension of `M` restricts to the Frobenius automorphism of an
  unramified extension of `k` inside it.**

## Tags

local field, unramified extension, totally ramified extension, Frobenius, residue field
-/

set_option synthInstance.maxHeartbeats 800000

universe u

namespace InverseGalois.CFT

open Module

/-! ### The Frobenius condition over the smaller base field -/

section Restrict

variable {k M N : Type u} [NontriviallyNormedField k] [IsUltrametricDist k] [ProperSpace k]
variable [NontriviallyNormedField M] [IsUltrametricDist M] [ProperSpace M]
variable [Algebra k M] [FiniteDimensional k M]
variable [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra k N] [IsScalarTower k M N]
variable [FiniteDimensional k N]

/-- **An automorphism of an extension of a base field with the same residues is a Frobenius
automorphism over the smaller base field as soon as it is one over the larger.**  The two absolute
values of the extension agree, so the two integer rings agree, and the two Frobenius conditions ask
for the same power. -/
theorem isDivisionFrobenius_restrictScalars (hnorm : ∀ x : k, ‖algebraMap k M x‖ = ‖x‖)
    (hq : Nat.card (DivisionResidue M M) = Nat.card (DivisionResidue k k)) {σ : N ≃ₐ[M] N}
    (hσ : IsDivisionFrobenius σ) : IsDivisionFrobenius (σ.restrictScalars k) := by
  rw [isDivisionFrobenius_iff] at hσ ⊢
  intro x
  have hmem : (x : N) ∈ divisionIntegers M N := by
    rw [mem_divisionIntegers, divisionNorm_eq_of_base hnorm]
    exact mem_divisionIntegers.1 x.2
  have h := hσ ⟨(x : N), hmem⟩
  rw [hq, divisionNorm_eq_of_base hnorm] at h
  exact h

end Restrict

/-! ### Restriction to an unramified subextension of the smaller base field -/

section RestrictNormal

variable {k E M N : Type u} [NontriviallyNormedField k] [IsUltrametricDist k] [ProperSpace k]
variable [NontriviallyNormedField M] [IsUltrametricDist M] [ProperSpace M]
variable [Algebra k M] [FiniteDimensional k M]
variable [Field N] [Algebra M N] [FiniteDimensional M N] [Algebra k N] [IsScalarTower k M N]
variable [FiniteDimensional k N]
variable [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra E N] [IsScalarTower k E N]
variable [Normal k E]

/-- **The Frobenius automorphism of an unramified extension of `M` restricts to the Frobenius
automorphism of an unramified extension of `k` inside it**, when `M` has no more residues than `k`.
Over `k` the automorphism is still a Frobenius automorphism, and the restriction of a Frobenius
automorphism to a normal subextension is a Frobenius automorphism. -/
theorem restrictNormal_restrictScalars_divisionFrobenius (hnorm : ∀ x : k, ‖algebraMap k M x‖ = ‖x‖)
    (hq : Nat.card (DivisionResidue M M) = Nat.card (DivisionResidue k k))
    (hurN : ∀ z : N, z ≠ 0 → ∃ c : M, c ≠ 0 ∧ divisionNorm M N z = ‖c‖)
    (hurE : ∀ z : E, z ≠ 0 → ∃ c : k, c ≠ 0 ∧ divisionNorm k E z = ‖c‖) :
    ((divisionFrobenius M N hurN).restrictScalars k).restrictNormal E
      = divisionFrobenius k E hurE :=
  eq_divisionFrobenius k E hurE
    (isDivisionFrobenius_restrictNormal
      (isDivisionFrobenius_restrictScalars hnorm hq
        (isDivisionFrobenius_divisionFrobenius M N hurN)))

end RestrictNormal

end InverseGalois.CFT
