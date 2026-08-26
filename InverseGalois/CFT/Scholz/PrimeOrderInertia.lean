/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaFixedField

/-!
# Split inertia is automatic at a prime whose decomposition image has prime order

The last step of the Scholz–Reichardt construction adjoins the auxiliary primes used to correct the
residue degrees.  Those primes split completely in the field already built, so the image of their
decomposition group under the corrected homomorphism lands in the kernel of the central step, a
group of prime order.  A subgroup of a group of prime order is either trivial or everything, so as
soon as the prime ramifies in the field cut out by the corrected homomorphism the image of its
inertia group is already the whole kernel, and in particular contains the image of the decomposition
group.  No further work is needed at such a prime: the split inertia condition holds for free.

## Main results

* `InverseGalois.CFT.map_le_map_of_card_prime`: **inside a subgroup of prime order, a nontrivial
  image of a subgroup absorbs the image of any larger subgroup.**
* `InverseGalois.CFT.map_stabilizer_le_map_inertia_of_card_prime`: **at a ramified prime whose
  decomposition group maps into a subgroup of prime order the image of the decomposition group lies
  in the image of the inertia group.**

## Tags

inertia subgroup, decomposition group, prime order, split inertia, Scholz–Reichardt
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

/-! ### A subgroup of prime order -/

/-- **Inside a subgroup of prime order, a nontrivial image absorbs everything.**  If the image of a
subgroup `D` lies in a subgroup `Z` of prime order and the image of a smaller subgroup `I` is
nontrivial, then the image of `I` is all of `Z`, hence contains the image of `D`. -/
theorem map_le_map_of_card_prime {Γ G : Type*} [Group Γ] [Group G] {ψ : Γ →* G} {I D : Subgroup Γ}
    (hID : I ≤ D) {Z : Subgroup G} {ℓ : ℕ} (hℓ : ℓ.Prime) (hcard : Nat.card ↥Z = ℓ)
    (hD : D.map ψ ≤ Z) (hI : I.map ψ ≠ ⊥) :
    D.map ψ ≤ I.map ψ := by
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have hIZ : I.map ψ ≤ Z := (Subgroup.map_mono hID).trans hD
  have hdvd : Nat.card ↥(I.map ψ) ∣ ℓ := hcard ▸ Subgroup.card_dvd_of_le hIZ
  rcases (Nat.Prime.eq_one_or_self_of_dvd hℓ _ hdvd) with h1 | hle
  · exact absurd (Subgroup.card_eq_one.mp h1) hI
  · exact (Subgroup.eq_of_le_of_card_ge hIZ (by rw [hcard, hle])) ▸ hD

/-! ### The arithmetic consequence -/

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

/-- **At a ramified prime whose decomposition group maps into a subgroup of prime order the image of
the decomposition group lies in the image of the inertia group.**  Ramification in the field cut out
by the homomorphism forces the image of the inertia group to be nontrivial, and a nontrivial
subgroup of a group of prime order is the whole of it. -/
theorem map_stabilizer_le_map_inertia_of_card_prime (hp : p.Prime) (P : Ideal (𝓞 N)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] {G : Type*} [Group G] (ψ : Gal(N/ℚ) →* G) {Z : Subgroup G}
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hcard : Nat.card ↥Z = ℓ)
    (hD : (MulAction.stabilizer Gal(N/ℚ) P).map ψ ≤ Z)
    (hram : p ∈ ramifiedSet ↥(IntermediateField.fixedField ψ.ker)) :
    (MulAction.stabilizer Gal(N/ℚ) P).map ψ ≤ (Ideal.inertia Gal(N/ℚ) P).map ψ := by
  refine map_le_map_of_card_prime (Ideal.inertia_le_stabilizer P) hℓ hcard hD fun hbot => ?_
  exact notMem_ramifiedSet_fixedField_ker_of_inertia ψ hp P
    (fun σ hσ => Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_map_of_mem ψ hσ)) hram

end InverseGalois.CFT
