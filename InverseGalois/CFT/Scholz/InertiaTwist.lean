/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralTwist
import InverseGalois.CFT.InertiaFixedField

/-!
# Cancelling the inertia of a solution at one prime

A solution of a central embedding problem may be multiplied pointwise by a character with central
values without ceasing to be a solution.  The effect of the twist on the ramification is read off
one prime at a time, on the fixed field of the kernel of the twisted homomorphism.

At a prime where the inertia subgroup is cyclic — which is the case whenever the ramification there
is tame — and where the character already reaches on inertia everything the solution reaches, a
single power of the character cancels the solution on inertia, and the fixed field of the kernel of
the twist becomes unramified there.  At a prime where both the solution and the character are
already trivial on inertia nothing is lost: the twist is trivial on inertia too.  Together these
two statements are the ramification bookkeeping of the correction step: the auxiliary field
supplying the character is ramified only where the correction is wanted, so the corrected solution
loses the unwanted ramification and keeps everything else.

## Main results

* `InverseGalois.CFT.exists_zpow_notMem_ramifiedSet_fixedField_ker`: **a power of the character
  cancels the solution on a cyclic inertia subgroup**, so that the fixed field of the kernel of the
  twist is unramified at the prime below it.
* `InverseGalois.CFT.notMem_ramifiedSet_fixedField_ker_mulCentral`: **a twist of a solution which is
  unramified at a prime by a character which is unramified there is unramified there.**

## Tags

embedding problem, twist, character, inertia subgroup, ramified prime
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M] {p : ℕ}
variable {G : Type*} [Group G]

/-- **A power of a character cancels a solution on a cyclic inertia subgroup**, so that the fixed
field of the kernel of the twisted homomorphism is unramified at the rational prime below.  The
exponent is read off at a generator of the inertia subgroup, and one prime above `p` suffices
because the kernel is normal and the Galois group permutes the primes above `p` transitively. -/
theorem exists_zpow_notMem_ramifiedSet_fixedField_ker (hp : p.Prime) (ψ χ : Gal(M/ℚ) →* G)
    (hχ : ∀ x, χ x ∈ Subgroup.center G) (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] [IsCyclic ↥(Ideal.inertia Gal(M/ℚ) P)]
    (hle : (Ideal.inertia Gal(M/ℚ) P).map ψ ≤ (Ideal.inertia Gal(M/ℚ) P).map χ) :
    ∃ a : ℤ, p ∉ ramifiedSet ↥(IntermediateField.fixedField
      (mulCentral ψ (zpowCentral χ hχ a) (zpowCentral_mem_center χ hχ a)).ker) := by
  obtain ⟨a, ha⟩ := exists_zpow_mul_eq_one_of_isCyclic_subgroup ψ χ hle
  exact ⟨a, notMem_ramifiedSet_fixedField_ker_of_inertia _ hp P fun σ hσ => ha σ hσ⟩

/-- **A twist of a solution which is trivial on the inertia subgroup of a prime by a character
which is trivial there is again trivial there**, so the fixed field of the kernel of the twist is
unramified at the rational prime below. -/
theorem notMem_ramifiedSet_fixedField_ker_mulCentral (hp : p.Prime) (ψ χ : Gal(M/ℚ) →* G)
    (hχ : ∀ x, χ x ∈ Subgroup.center G) (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hψP : ∀ σ ∈ Ideal.inertia Gal(M/ℚ) P, ψ σ = 1)
    (hχP : ∀ σ ∈ Ideal.inertia Gal(M/ℚ) P, χ σ = 1) :
    p ∉ ramifiedSet ↥(IntermediateField.fixedField (mulCentral ψ χ hχ).ker) :=
  notMem_ramifiedSet_fixedField_ker_of_inertia _ hp P fun σ hσ => by
    rw [mulCentral_apply, hψP σ hσ, hχP σ hσ, mul_one]

end InverseGalois.CFT
