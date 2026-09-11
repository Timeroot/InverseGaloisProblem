/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.NormPlaceValue
import InverseGalois.CFT.Units.SUnit

/-!
# Removing a place from an `S`-unit at the cost of a power

The value of a unit of a number field at a finite place is minus its order at the corresponding
prime, so an `S`-unit is exactly a unit whose value vanishes away from `S`.  Adding one prime to
`S` therefore enlarges the group of `S`-units by exactly one value, and if that value is divisible
by an exponent then the new `S`-unit differs from an old one by a power of that exponent, provided
the field has enough units to realise a prescribed system of orders away from `S`.

That last proviso is the one the construction of a Chebotarev place is run with anyway: it says
that every finitely supported system of orders away from the finite set is realised by a unit,
which is a form of the finiteness of the class group relative to the set.  The reduction it buys
is what lets a character killed by the exponent be tested on the smaller group only, since a power
of the exponent is invisible to such a character.

## Main results

* `InverseGalois.CFT.placeValue_eq_neg_ord`: the value of a unit at a finite place is minus its
  order there.
* `InverseGalois.CFT.mem_sUnits_iff_forall_placeValue_eq_zero`: an `S`-unit is a unit whose value
  vanishes away from `S`.
* `InverseGalois.CFT.exists_mul_pow_mem_sUnits`: **an `S`-unit for one more place, whose value
  there is divisible by the exponent, is an `S`-unit times a power of that exponent.**

## Tags

S-unit, place, order, power, class group
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### The value of a unit and its order -/

section Value

variable {K : Type} [Field K] [NumberField K]

/-- **The value of a unit of a number field at a finite place is minus its order there.**  Both
sides read the exponent of the prime in the element, with opposite signs. -/
theorem placeValue_eq_neg_ord (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    placeValue v a = -ord K v (a : K) := by
  rw [placeValue_eq_placeOrd, placeOrd_apply,
    valuation_eq_exp_neg_ord K v (Units.ne_zero a), WithZero.log_exp]

/-- **An `S`-unit is a unit whose value vanishes at every place outside `S`.** -/
theorem mem_sUnits_iff_forall_placeValue_eq_zero {X : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ} :
    u ∈ sUnits K X ↔ ∀ v ∉ X, placeValue v u = 0 := by
  refine ⟨fun hu v hv => ?_, fun h => mem_sUnits.mpr fun v hv => ?_⟩
  · rw [placeValue_eq_neg_ord, mem_sUnits.mp hu v hv, neg_zero]
  · have := h v hv
    rw [placeValue_eq_neg_ord, neg_eq_zero] at this
    exact this

/-- The value of an `S`-unit vanishes at every place outside `S`. -/
theorem placeValue_eq_zero_of_mem_sUnits {X : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ}
    (hu : u ∈ sUnits K X) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ X) : placeValue v u = 0 :=
  mem_sUnits_iff_forall_placeValue_eq_zero.1 hu v hv

end Value

/-! ### Reducing an `S`-unit by a power -/

section Reduce

variable {K : Type} [Field K] [NumberField K]

/-- **An `S`-unit for one more place, whose value at that place is divisible by the exponent, is an
`S`-unit for the smaller set times a power of that exponent.**  A unit realising minus a fraction
of the extra value at the extra place, and no order at all elsewhere outside the set, is raised to
the exponent and divided out. -/
theorem exists_mul_pow_mem_sUnits {p : ℕ} {X : Set (HeightOneSpectrum (𝓞 K))}
    {Q : HeightOneSpectrum (𝓞 K)} (hQX : Q ∉ X)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ X, ord K v (a : K) = m v)
    {u : Kˣ} (hu : u ∈ sUnits K (insert Q X)) (hdvd : (p : ℤ) ∣ placeValue Q u) :
    ∃ u₀ a : Kˣ, u₀ ∈ sUnits K X ∧ u = u₀ * a ^ p := by
  classical
  obtain ⟨d, hd⟩ := hdvd
  have hordQu : ord K Q ((u : Kˣ) : K) = -((p : ℤ) * d) := by
    rw [← hd, placeValue_eq_neg_ord, neg_neg]
  have hmfin : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (if v = Q then -d else 0) = 0 := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton Q) fun v hv => ?_
    simp only [Set.mem_setOf_eq] at hv
    by_cases hvq : v = Q
    · exact Set.mem_singleton_iff.2 hvq
    · exact absurd (if_neg hvq) hv
  obtain ⟨a, ha⟩ := hrepr (fun v => if v = Q then -d else 0) hmfin
  have haQ : ord K Q ((a : Kˣ) : K) = -d := by
    rw [ha Q hQX]
    exact if_pos rfl
  refine ⟨u * (a ^ p)⁻¹, a, mem_sUnits.mpr fun v hv => ?_, by group⟩
  have hcoe : ((u * (a ^ p)⁻¹ : Kˣ) : K) = ((u : Kˣ) : K) * (((a : Kˣ) : K) ^ p)⁻¹ := by
    push_cast
    ring
  rw [hcoe, ord_mul v (Units.ne_zero u) (inv_ne_zero (pow_ne_zero _ (Units.ne_zero a))), ord_inv,
    ord_pow v (Units.ne_zero a)]
  by_cases hvq : v = Q
  · subst hvq
    rw [hordQu, haQ]
    ring
  · have h1 : ord K v ((u : Kˣ) : K) = 0 := by
      refine mem_sUnits.mp hu v ?_
      rw [Set.mem_insert_iff]
      rintro (rfl | hvX)
      · exact hvq rfl
      · exact hv hvX
    have h2 : ord K v ((a : Kˣ) : K) = 0 := by
      rw [ha v hv]
      exact if_neg hvq
    rw [h1, h2]
    ring

end Reduce

end InverseGalois.CFT
