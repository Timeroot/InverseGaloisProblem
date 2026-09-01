/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.PlaceCyclic

/-!
# The completion at an unramified place

Let `K / k` be a Galois extension of number fields and let `w` be a prime of `K` whose
ramification index over the prime `v` below it is one.  Then the completion `K_w` is unramified
over `k_v` in the sense the splitting theory of division algebras asks for: every absolute value
of `K_w` is an absolute value of a scalar.

The reason is that the two valuations already have the same value group, and the absolute value
of a division algebra is a root of the absolute value of the algebra norm.  Over a Galois
extension the algebra norm is the product of the conjugates, and every automorphism of the
completion comes from the decomposition group, hence is an isometry.  So the value of the norm of
an element is the degree-th power of the value of that element, which by unramifiedness is the
degree-th power of the value of a scalar.

Consequently a place of the base which is unramified in the extension and at which the coefficient
of a cyclic algebra is a unit contributes nothing to the sum of the local invariants: the local
degree is the order of a Frobenius, and the invariant is the value of the coefficient divided by
that degree.

## Main results

* `InverseGalois.CFT.valued_algEquiv_adicCompletion`: an automorphism of the completion over the
  completion of the base is an isometry.
* `InverseGalois.CFT.valued_algebraNorm_adicCompletion`: **at an unramified place the value of the
  norm is the degree-th power of the value.**
* `InverseGalois.CFT.exists_divisionNorm_eq_norm_adicCompletion`: **at an unramified place every
  absolute value of the completion is an absolute value of a scalar.**
* `InverseGalois.CFT.placeInvariant_cyclicBrauerHom_eq_one_of_ramIdx_eq_one`: **a cyclic algebra
  whose coefficient is a unit at an unramified finite place has trivial invariant there.**

## Tags

number field, completion, unramified place, decomposition group, division algebra, local
invariant, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain Module MulAction NumberField

section PlaceUnramified

attribute [local instance] isGalois_adicCompletion

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **An automorphism of the completion over the completion of the base is an isometry**, because
it comes from the decomposition group, which acts on the completion by isometries. -/
theorem valued_algEquiv_adicCompletion
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
    (z : w.adicCompletion K) : Valued.v (τ z) = Valued.v z := by
  rw [← adicCompletionAut_restrictToBase k w τ z]
  exact valued_adicCompletionAut w _ _ z

variable (k) in
/-- **At an unramified place the value of the norm of the completion is the degree-th power of the
value.**  The norm is the product of the conjugates, all of which have the same value, and the
comparison of the two valuations costs nothing when the ramification index is one. -/
theorem valued_algebraNorm_adicCompletion (hram : ramIdx (𝓞 k) w = 1)
    (z : w.adicCompletion K) :
    Valued.v (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z)
      = Valued.v z ^ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) := by
  have hmap : Valued.v (algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
        (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z))
      = Valued.v (Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z) := by
    rw [algebraMap_adicCompletion k w, valued_adicCompletionComap (𝓞 k) w, hram, pow_one]
  have hconj : ∀ τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
      w.adicCompletion K, Valued.v (τ z) = Valued.v z :=
    fun τ => valued_algEquiv_adicCompletion k w τ z
  rw [← hmap, Algebra.norm_eq_prod_automorphisms, map_prod]
  simp only [hconj, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [IsGalois.card_aut_eq_finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)]

variable (k) in
/-- **At an unramified place every absolute value of the completion is an absolute value of a
scalar.**  The value of an element is the value of a scalar, the ramification index being one, and
the absolute value of a division algebra is the degree-th root of the absolute value of the
norm. -/
theorem exists_divisionNorm_eq_norm_adicCompletion (hram : ramIdx (𝓞 k) w = 1)
    (z : w.adicCompletion K) (hz : z ≠ 0) :
    ∃ c : (primeUnder (𝓞 k) w).adicCompletion k, c ≠ 0 ∧
      divisionNorm ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) z = ‖c‖ := by
  obtain ⟨c, hc⟩ := valued_adicCompletion_surjective (primeUnder (𝓞 k) w) (Valued.v z)
  have hz0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  have hc0 : c ≠ 0 := fun h => hz0 (by rw [← hc, h, map_zero])
  have hN : (finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Module.finrank_pos
      (R := (primeUnder (𝓞 k) w).adicCompletion k) (M := w.adicCompletion K)).ne'
  refine ⟨c, hc0, ?_⟩
  have hn : ‖Algebra.norm ((primeUnder (𝓞 k) w).adicCompletion k) z‖
      = ‖c ^ finrank ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)‖ :=
    norm_eq_of_valued_eq (by
      rw [valued_algebraNorm_adicCompletion k w hram z, map_pow, hc])
  rw [divisionNorm, hn, norm_pow, ← Real.rpow_natCast ‖c‖ _,
    ← Real.rpow_mul (norm_nonneg _), mul_one_div, div_self hN, Real.rpow_one]

variable (k) in
/-- **The Frobenius of an unramified completion is a power of any generator** of the Galois group
of the completions, that group being finite. -/
theorem exists_divisionFrobenius_eq_pow_adicCompletion (hram : ramIdx (𝓞 k) w = 1)
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hσ : ∀ x : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K,
      x ∈ Subgroup.zpowers σ) :
    ∃ s : ℕ, divisionFrobenius ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
      (fun z hz => exists_divisionNorm_eq_norm_adicCompletion k w hram z hz) = σ ^ s := by
  obtain ⟨s, hs⟩ := mem_powers_iff_mem_zpowers.mpr (hσ (divisionFrobenius
    ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K)
    (fun z hz => exists_divisionNorm_eq_norm_adicCompletion k w hram z hz)))
  exact ⟨s, hs.symm⟩

variable (k) in
/-- **A cyclic algebra whose coefficient is a unit at an unramified finite place has trivial
invariant there.**  Only the places dividing the coefficient and the places ramified in the
extension can contribute to the sum of the local invariants. -/
theorem placeInvariant_cyclicBrauerHom_eq_one_of_ramIdx_eq_one {σ₀ : Gal(K/k)}
    (hσ₀ : ∀ x : Gal(K/k), x ∈ Subgroup.zpowers σ₀)
    {σ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K}
    (hσ : ∀ x : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K,
      x ∈ Subgroup.zpowers σ)
    (hres : (localDecompositionEquiv k w σ).restrictScalars k
      = σ₀ ^ (stabilizer Gal(K/k) w).index)
    (hram : ramIdx (𝓞 k) w = 1) {a : kˣ}
    (ha : Valued.v (algebraMap k ((primeUnder (𝓞 k) w).adicCompletion k) (a : k)) = 1) :
    placeInvariant k (primeUnder (𝓞 k) w) (cyclicBrauerHom hσ₀ a) = 1 := by
  obtain ⟨s, hs⟩ := exists_divisionFrobenius_eq_pow_adicCompletion k w hram hσ
  exact placeInvariant_cyclicBrauerHom_eq_one k w hσ₀ hσ hres _ hs ha

end PlaceUnramified

end InverseGalois.CFT
