import Mathlib
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.TameCharacter

/-!
# Tame inertia is cyclic, and so is a split decomposition group

The tame inertia character embeds the inertia group at a prime `P` into the units of the residue
field at `P` as soon as the residue characteristic does not divide the order of that group.  The
residue field is finite, and a finite subgroup of the units of a domain is cyclic; so tame inertia
is cyclic.

Under Serre's condition the decomposition group at a ramified prime *is* the inertia group there,
so the same conclusion holds for the decomposition group.  That is the form the local hypotheses of
the central embedding criterion are stated in: they ask for a cyclic decomposition group at every
ramified place.

## Main results

* `InverseGalois.CFT.isCyclic_inertia_of_tame`: **tame inertia is cyclic.**
* `InverseGalois.CFT.isCyclic_stabilizer_of_isSplitInertia`: **under Serre's residue-degree
  condition the decomposition group at a tamely ramified prime is cyclic.**

## Tags

inertia group, decomposition group, tame ramification, cyclic group
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Tame inertia is cyclic.**  The tame character is an injective homomorphism from the inertia
group at `P` into the units of the residue field at `P`, and a finite subgroup of the units of a
domain is cyclic. -/
theorem isCyclic_inertia_of_tame {P : Ideal (𝓞 K)} [P.IsPrime] (hP : P ≠ ⊥)
    (htame : ¬ ringChar (𝓞 K ⧸ P) ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    IsCyclic ↥(Ideal.inertia Gal(K/ℚ) P) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer hP
  exact isCyclic_of_subgroup_isDomain ((Units.coeHom (𝓞 K ⧸ P)).comp (tameChar hπ))
    (Units.val_injective.comp (tameChar_injective hπ htame))

/-- **Tame inertia over a rational prime is cyclic**, with the tameness hypothesis phrased in terms
of the rational prime rather than the residue characteristic. -/
theorem isCyclic_inertia_of_not_dvd {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (htame : ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    IsCyclic ↥(Ideal.inertia Gal(K/ℚ) P) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact isCyclic_inertia_of_tame (ne_bot_of_liesOver p P) (by rwa [ringChar_quotient_eq p hp P])

/-- **Under Serre's residue-degree condition the decomposition group at a tamely ramified prime is
cyclic.**  Split inertia identifies the decomposition group with the inertia group, which is cyclic
by tameness. -/
theorem isCyclic_stabilizer_of_isSplitInertia (h : IsSplitInertia K) {p : ℕ}
    (hmem : p ∈ ramifiedSet K) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (htame : ¬ p ∣ Nat.card (Ideal.inertia Gal(K/ℚ) P)) :
    IsCyclic ↥(MulAction.stabilizer Gal(K/ℚ) P) := by
  rw [← inertia_eq_stabilizer_of_isSplitInertia h hmem P]
  exact isCyclic_inertia_of_not_dvd hmem.1 P htame

end InverseGalois.CFT
