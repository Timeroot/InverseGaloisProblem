/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.AbelianInertia
import InverseGalois.CFT.Scholz.CentralCyclicLift

/-!
# Extending a solution from inertia to the decomposition group

A solution of a central embedding problem which is unramified at a prime takes values in the kernel
of the problem on the inertia subgroup there.  The quotient of the decomposition group by the
inertia subgroup is cyclic, being the Galois group of the residue field extension, so as soon as
that quotient is large enough to kill the group of the embedding problem the restriction of the
solution to the inertia subgroup extends to a character of the whole decomposition group with
values in the kernel.

Making the quotient large is a choice of field: the residue degree at the prime grows when a
cyclotomic field in which the prime has large residue degree is adjoined.  The extension produced
here is the character whose square root the dyadic correction then computes.

## Main results

* `InverseGalois.CFT.exists_monoidHom_stabilizer_eqOn_inertia`: **a solution unramified at a prime
  extends from the inertia subgroup to the decomposition group** as a character with values in the
  kernel of the embedding problem.

## Tags

number field, embedding problem, decomposition group, inertia, residue degree, central extension
-/

namespace InverseGalois.CFT

open MulAction NumberField

open scoped Pointwise

variable {M : Type} [Field M] [NumberField M] [IsGalois ℚ M]
variable {G H : Type*} [Group G] [Finite G] [Group H] {ℓ : ℕ}

omit [IsGalois ℚ M] in
/-- **A solution unramified at a prime extends from the inertia subgroup to the decomposition
group.**  The quotient of the decomposition group by the inertia subgroup is cyclic, and by
hypothesis its order kills the group of the embedding problem, so the restriction of the solution
to the inertia subgroup is the restriction of a character of the decomposition group taking values
in the kernel throughout. -/
theorem exists_monoidHom_stabilizer_eqOn_inertia (hℓ : ℓ.Prime) (P : Ideal (𝓞 M)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ℓ : ℤ)})] {f : G →* H} (hZ : f.ker ≤ Subgroup.center G)
    {θ : Gal(M/ℚ) →* G} (hI : ∀ σ ∈ Ideal.inertia Gal(M/ℚ) P, θ σ ∈ f.ker)
    (hdvd : Nat.card G ∣ Nat.card (↥(stabilizer Gal(M/ℚ) P) ⧸
      (Ideal.inertia Gal(M/ℚ) P).subgroupOf (stabilizer Gal(M/ℚ) P))) :
    ∃ μ : ↥(stabilizer Gal(M/ℚ) P) →* G, μ.range ≤ f.ker ∧
      ∀ σ : ↥(stabilizer Gal(M/ℚ) P),
        (σ : Gal(M/ℚ)) ∈ Ideal.inertia Gal(M/ℚ) P → μ σ = θ σ := by
  set D := stabilizer Gal(M/ℚ) P with hD
  set N := (Ideal.inertia Gal(M/ℚ) P).subgroupOf D with hN
  haveI : IsCyclic (↥D ⧸ N) := isCyclic_stabilizer_quotient_inertia hℓ P
  obtain ⟨μ, hμrange, hμeq⟩ :=
    exists_monoidHom_range_le_ker_eqOn_of_card_dvd (I := N) inferInstance hdvd hZ
      (θ := θ.comp D.subtype) (fun σ hσ => hI σ (Subgroup.mem_subgroupOf.mp hσ))
  exact ⟨μ, hμrange, fun σ hσ => hμeq σ (Subgroup.mem_subgroupOf.mpr hσ)⟩

end InverseGalois.CFT
