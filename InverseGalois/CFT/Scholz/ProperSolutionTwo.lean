/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CentralEmbeddingSqrtNegOne
import InverseGalois.CFT.Kummer.RootsInBase
import InverseGalois.CFT.Scholz.Tame
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Solving the central step of order two over the rational numbers

For a kernel of odd prime order `ℓ` the local-global criterion for a central Frattini embedding
problem is applied over the cyclotomic field `ℚ(μ_ℓ)`, because it needs a primitive `ℓ`-th root of
unity in its base field.  For `ℓ = 2` that root of unity is `-1`, which is already rational, so the
detour through a cyclotomic base is unnecessary and the criterion applies over `ℚ` itself.  What
made the even case delicate was instead the archimedean condition of the local-global criterion,
and over `ℚ` that condition is not needed at all.

The arithmetic input is Serre's condition for `A`, read directly at the places of `A` rather than
transported to a compositum.

## Main results

* `InverseGalois.CFT.isCyclic_and_exists_hasResidueChar_rat`: **the complete local hypothesis of
  the criterion for solving a central embedding problem**, at a place of a field of `ℓ`-power
  degree satisfying Serre's condition that is ramified over the rational numbers.
* `InverseGalois.CFT.hasProperSolution_two`: **a central Frattini embedding problem with kernel of
  order two is solvable over an extension of `A`**, whenever `A` has two-power degree and satisfies
  Serre's condition one level above that power.

## Tags

embedding problem, Scholz condition, central extension, square root of unity
-/

namespace InverseGalois.CFT

open IsDedekindDomain IntermediateField MulAction NumberField InverseGalois.NumberTheory

/-! ### The local hypothesis over the rational base -/

section Local

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

/-- **The complete local hypothesis of the criterion for solving a central embedding problem**, at
a place of `K` ramified over the rational numbers.  Such a place lies over a rational prime that
ramifies in `K`, so Serre's condition makes its decomposition group cyclic, of order dividing
`ℓ ^ M`, and its residue degree one; the residue field of the completion is therefore prime, and
the level condition one step further makes `ℓ` times the order of the decomposition group divide
`p - 1`. -/
theorem isCyclic_and_exists_hasResidueChar_rat {ℓ M : ℕ} (hℓ : ℓ.Prime)
    (hG : IsPGroup ℓ Gal(K/ℚ)) (hs : IsScholz ℓ (M + 1) K) (hdvd : Nat.card Gal(K/ℚ) ∣ ℓ ^ M)
    (v : HeightOneSpectrum (𝓞 K)) (hnr : ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal) :
    IsCyclic ↥(stabilizer Gal(K/ℚ) v) ∧ ∃ p e : ℕ,
      HasResidueChar (v.adicCompletion K) p e ∧
        (∀ x : v.adicCompletion K, Valued.v x ≤ 1 →
          ∃ b : ℤ, Valued.v (x - (b : v.adicCompletion K)) < 1) ∧
        ℓ * Nat.card ↥(stabilizer Gal(K/ℚ) v) ∣ p - 1 := by
  haveI := v.isPrime
  obtain ⟨p, hp, hlo⟩ := exists_prime_liesOver v
  haveI := hlo
  have hmem : p ∈ ramifiedSet K := by
    refine (inertia_ne_bot_iff_mem_ramifiedSet hp v.asIdeal).mp fun hbot => hnr ?_
    exact (inertia_eq_bot_iff_isUnramifiedAt_base (k := ℚ) v.asIdeal v.ne_bot).mp hbot
  rw [stabilizer_eq_stabilizer_asIdeal]
  refine ⟨IsScholz.isCyclic_stabilizer hℓ (Nat.succ_ne_zero M) hG hs hmem v.asIdeal, ?_⟩
  exact exists_hasResidueChar_and_primeResidue hp v (hs.2 p hmem v.asIdeal v.isPrime hlo)
    (mul_card_stabilizer_dvd_sub_one hs.isLevel hdvd hmem v.asIdeal)

end Local

/-! ### The embedding problem of order two -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **A central Frattini embedding problem with kernel of order two is solvable over an extension
of `A`.**  The field `A` is required to have two-power degree and to satisfy Serre's condition one
level above that power; those are exactly the hypotheses under which the decomposition group at a
ramified place of `A` is cyclic and the residue characteristic is congruent to one modulo twice its
order.  No base change is needed, because `-1` is a primitive square root of unity in `ℚ`, and no
condition at the archimedean places is needed either. -/
theorem hasProperSolution_two {G H : Type} [Group G] [Group H] [Finite G] {f : G →* H}
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G) (hcard : Nat.card ↥f.ker = 2)
    {t : H → G} (ht : ∀ h, f (t h) = h) {M : ℕ}
    (A : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥A] [NumberField ↥A]
    (hG : IsPGroup 2 Gal(↥A/ℚ)) (hs : IsScholz 2 (M + 1) ↥A)
    (hdvd : Nat.card Gal(↥A/ℚ) ∣ 2 ^ M)
    {π : Gal(↥A/ℚ) →* H} (hπ : Function.Surjective π) :
    HasProperSolution A f π := by
  haveI : IsCyclic ↥f.ker := isCyclic_of_prime_card hcard
  have hζ : IsPrimitiveRoot (-1 : ℚ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨χ, hχinj, -, hχsurj⟩ := exists_monoidHom_units_of_card (k := ℚ) hζ hcard
  exact exists_surjective_hom_rat_of_forall_ramified_primeResidue hζ hZ hfr hcard hπ hχinj hχsurj
    ht fun v hnr => isCyclic_and_exists_hasResidueChar_rat Nat.prime_two hG hs hdvd v hnr

end InverseGalois.CFT
