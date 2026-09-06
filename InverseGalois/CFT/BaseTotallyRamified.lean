/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.BaseRamification
import InverseGalois.CFT.Units.PlaceTower

/-!
# Total ramification in a compositum with a new base field

A Galois extension of the rationals which is totally ramified at a rational prime stays totally
ramified when it is composed with a number field in which that prime is unramified.  This is the
complement of the transfer of unramifiedness: there the restriction of automorphisms embeds the
inertia group of the compositum into the inertia group of the original extension, and an embedding
can only make inertia smaller, so a trivial inertia group upstairs forces a trivial inertia group
downstairs.  Here the argument runs the other way, and it is a counting argument rather than a
group-theoretic one.

The ramification index is multiplicative in a tower, and the tower can be climbed on either side of
the compositum square.  Going up through the original extension, the ramification index over the
rationals is divisible by the degree of that extension, because that extension is totally ramified.
Going up through the new base field, the ramification index over the rationals is the ramification
index over the new base, because the prime is unramified in the new base.  So the degree of the
original extension divides the ramification index of the compositum over the new base.  That
ramification index is the order of an inertia subgroup, hence at most the degree of the compositum
over the new base, which in turn is at most the degree of the original extension because
restriction of automorphisms is injective.  The three inequalities close up, the inertia subgroup
has the order of the whole group, and so it is the whole group.

## Main results

* `InverseGalois.CFT.ramIdx_tower`: **the ramification index is multiplicative in a tower of
  number fields.**
* `InverseGalois.CFT.inertia_eq_top_of_inertia_base_eq_top`: **total ramification in a Galois
  extension of the rationals passes to a compositum with a number field in which the place is
  unramified.**

## Tags

number field, compositum, ramification index, inertia group, totally ramified, class field theory
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Multiplicativity of the ramification index in a tower -/

section Tower

variable {k F K : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field K]
  [NumberField K] [Algebra k F] [Algebra F K] [Algebra k K] [IsScalarTower k F K]

/-- **The ramification index is multiplicative in a tower of number fields.**  The ramification
index of a place over the bottom field is the product of the ramification index of the place below
it in the middle field over the bottom field and the ramification index of the place over the
middle field. -/
theorem ramIdx_tower (w : HeightOneSpectrum (𝓞 K)) :
    ramIdx (𝓞 k) w = ramIdx (𝓞 k) (primeUnder (𝓞 F) w) * ramIdx (𝓞 F) w := by
  haveI : (primeUnder (𝓞 F) w).asIdeal.IsPrime := (primeUnder (𝓞 F) w).isPrime
  haveI : w.asIdeal.IsPrime := w.isPrime
  have h := Ideal.ramificationIdx_algebra_tower (R := 𝓞 k) (S := 𝓞 F) (T := 𝓞 K)
    (p := (primeUnder (𝓞 k) w).asIdeal) (P := (primeUnder (𝓞 F) w).asIdeal) (Q := w.asIdeal)
    (map_primeUnder_ne_bot (A := 𝓞 F) w) (map_primeUnder_ne_bot (A := 𝓞 k) w)
    (map_primeUnder_le (A := 𝓞 F) w)
  show Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 K)) (primeUnder (𝓞 k) w).asIdeal w.asIdeal
      = Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 F))
          (primeUnder (𝓞 k) (primeUnder (𝓞 F) w)).asIdeal (primeUnder (𝓞 F) w).asIdeal
        * Ideal.ramificationIdx (algebraMap (𝓞 F) (𝓞 K)) (primeUnder (𝓞 F) w).asIdeal w.asIdeal
  rw [primeUnder_primeUnder k F w]
  exact h

end Tower

/-! ### Total ramification passes to the compositum -/

section TotallyRamified

variable {k F₀ E : Type} [Field k] [NumberField k] [Field F₀] [NumberField F₀] [IsGalois ℚ F₀]
  [Field E] [NumberField E] [Algebra k E] [Algebra F₀ E] [IsScalarTower ℚ k E]
  [IsScalarTower ℚ F₀ E] [IsGalois k E]

/-- **Total ramification in a Galois extension of the rationals passes to a compositum with a
number field in which the place is unramified.**  The degree of the original extension divides the
ramification index of the compositum over the new base, by multiplicativity of the ramification
index along the two sides of the compositum square; that ramification index is the order of an
inertia subgroup of the Galois group of the compositum over the new base, whose order is in turn at
most the degree of the original extension because restriction of automorphisms is injective. -/
theorem inertia_eq_top_of_inertia_base_eq_top
    (hgen : Algebra.adjoin k (Set.range (algebraMap F₀ E)) = ⊤) (w : HeightOneSpectrum (𝓞 E))
    (hk : ramIdx (𝓞 ℚ) (primeUnder (𝓞 k) w) = 1)
    (h : Ideal.inertia Gal(F₀/ℚ) (primeUnder (𝓞 F₀) w).asIdeal = ⊤) :
    Ideal.inertia Gal(E/k) w.asIdeal = ⊤ := by
  have hF₀ : ramIdx (𝓞 ℚ) (primeUnder (𝓞 F₀) w) = Nat.card Gal(F₀/ℚ) := by
    rw [← card_inertia_eq_ramIdx, h]
    exact Nat.card_congr (Subgroup.topEquiv).toEquiv
  have h1 : ramIdx (𝓞 ℚ) w = ramIdx (𝓞 ℚ) (primeUnder (𝓞 F₀) w) * ramIdx (𝓞 F₀) w :=
    ramIdx_tower (F := F₀) w
  have h2 : ramIdx (𝓞 ℚ) w = ramIdx (𝓞 ℚ) (primeUnder (𝓞 k) w) * ramIdx (𝓞 k) w :=
    ramIdx_tower (F := k) w
  rw [hk, one_mul] at h2
  have hdvd : Nat.card Gal(F₀/ℚ) ∣ ramIdx (𝓞 k) w := by
    rw [← h2, h1, hF₀]
    exact dvd_mul_right _ _
  have hcardle : Nat.card Gal(E/k) ≤ Nat.card Gal(F₀/ℚ) :=
    Nat.card_le_card_of_injective _ (galRestrictSub_injective hgen)
  have hle : ramIdx (𝓞 k) w ≤ Nat.card Gal(E/k) := by
    rw [← card_inertia_eq_ramIdx]
    exact Subgroup.card_le_card_group _
  have hpos : 0 < ramIdx (𝓞 k) w := Nat.pos_of_ne_zero (ramIdx_ne_zero w)
  have hge := Nat.le_of_dvd hpos hdvd
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [card_inertia_eq_ramIdx]
  omega

end TotallyRamified

end InverseGalois.CFT
