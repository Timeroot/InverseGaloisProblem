/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Approximation.Basic

/-!
# The places of a number field are independent

The absolute values attached to the places of a number field, both the infinite ones and those
attached to the prime ideals of the ring of integers, are nontrivial and pairwise inequivalent.
A prime ideal is not contained in another, so an element of one which avoids the other is small at
the first place and of absolute value one at the second; and a finite place makes every integer at
most one whereas an infinite place makes two equal to two.

Weak approximation therefore applies to any family consisting of all the infinite places together
with finitely many finite ones.

## Main results

* `InverseGalois.CFT.isNontrivial_adicAbv`: the absolute value of a prime is nontrivial.
* `InverseGalois.CFT.not_isEquiv_adicAbv`: **distinct primes give inequivalent absolute values.**
* `InverseGalois.CFT.not_isEquiv_adicAbv_infinitePlace`: **a finite place is never equivalent to an
  infinite one.**
* `InverseGalois.CFT.denseRange_algebraMap_placeAbv`: **weak approximation for the places of a
  number field**, at all the infinite places and finitely many finite ones at once.
* `InverseGalois.CFT.exists_dist_lt_placeAbv`: the same, read as the simultaneous solution of the
  approximation conditions.

## Tags

number field, place, weak approximation, absolute value
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField NumberField.RingOfIntegers.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-! ### Independence of the places -/

omit [NumberField K] in
/-- A prime of the ring of integers contains a nonzero element. -/
theorem exists_mem_asIdeal_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    ∃ r : 𝓞 K, r ∈ v.asIdeal ∧ r ≠ 0 := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  exact ⟨r, hr, hr0⟩

/-- **The absolute value of a prime is nontrivial**: a nonzero element of the prime has absolute
value less than one. -/
theorem isNontrivial_adicAbv (v : HeightOneSpectrum (𝓞 K)) : (adicAbv v).IsNontrivial := by
  obtain ⟨r, hr, hr0⟩ := exists_mem_asIdeal_ne_zero v
  refine ⟨algebraMap (𝓞 K) K r, by simpa using hr0, ne_of_lt ?_⟩
  exact (HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := K) v (one_lt_absNorm_nnreal v) r).mpr hr

/-- **Distinct primes give inequivalent absolute values.**  Neither prime contains the other, and an
element of the first avoiding the second is small there and of absolute value one at the second. -/
theorem not_isEquiv_adicAbv {v w : HeightOneSpectrum (𝓞 K)} (h : v ≠ w) :
    ¬(adicAbv v).IsEquiv (adicAbv w) := by
  intro he
  obtain ⟨r, hrv, hrw⟩ : ∃ r : 𝓞 K, r ∈ v.asIdeal ∧ r ∉ w.asIdeal := by
    by_contra hc
    push_neg at hc
    exact h (HeightOneSpectrum.ext
      ((v.isPrime.isMaximal v.ne_bot).eq_of_le w.isPrime.ne_top hc))
  have h1 : adicAbv v (algebraMap (𝓞 K) K r) < 1 :=
    (HeightOneSpectrum.adicAbv_coe_lt_one_iff (K := K) v (one_lt_absNorm_nnreal v) r).mpr hrv
  have h2 : adicAbv w (algebraMap (𝓞 K) K r) = 1 :=
    (HeightOneSpectrum.adicAbv_coe_eq_one_iff (K := K) w (one_lt_absNorm_nnreal w) r).mpr hrw
  exact absurd (he.lt_one_iff.mp h1) (by rw [h2]; exact lt_irrefl 1)

/-- **A finite place is never equivalent to an infinite one**: a finite place makes every integer
at most one, whereas an infinite place makes two equal to two. -/
theorem not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬(adicAbv v).IsEquiv w.1 := by
  intro he
  have h1 : adicAbv v ((2 : ℕ) : K) ≤ 1 := adicAbv_natCast_le_one v 2
  have h2 : w.1 ((2 : ℕ) : K) ≤ 1 := he.le_one_iff.mp h1
  rw [show w.1 ((2 : ℕ) : K) = w ((2 : ℕ) : K) from rfl, InfinitePlace.map_natCast] at h2
  norm_num at h2

/-! ### Weak approximation at the places of a number field -/

variable {Y : Type*} [Finite Y]

/-- The absolute values of all the infinite places of a number field together with those of a
finite family of primes. -/
noncomputable def placeAbv (ι : Y → HeightOneSpectrum (𝓞 K)) :
    InfinitePlace K ⊕ Y → AbsoluteValue K ℝ :=
  Sum.elim (fun w => w.1) fun y => adicAbv (ι y)

variable {ι : Y → HeightOneSpectrum (𝓞 K)}

omit [Finite Y] in
/-- Every one of those absolute values is nontrivial. -/
theorem isNontrivial_placeAbv (i : InfinitePlace K ⊕ Y) : (placeAbv ι i).IsNontrivial := by
  cases i with
  | inl w => exact InfinitePlace.isNontrivial w
  | inr y => exact isNontrivial_adicAbv (ι y)

omit [Finite Y] in
/-- **Those absolute values are pairwise inequivalent**, provided the family of primes is
injective. -/
theorem pairwise_not_isEquiv_placeAbv (hinj : Function.Injective ι) :
    Pairwise fun i j => ¬(placeAbv ι i).IsEquiv (placeAbv ι j) := by
  intro i j hij
  cases i with
  | inl w =>
    cases j with
    | inl w' =>
      exact fun he => hij (congrArg Sum.inl ((InfinitePlace.eq_iff_isEquiv (K := K)).mpr he))
    | inr y => exact fun he => not_isEquiv_adicAbv_infinitePlace (ι y) w he.symm
  | inr y =>
    cases j with
    | inl w => exact not_isEquiv_adicAbv_infinitePlace (ι y) w
    | inr y' =>
      exact not_isEquiv_adicAbv fun hv => hij (congrArg Sum.inr (hinj hv))

/-- **Weak approximation for the places of a number field**: the field is dense in the product of
its copies carrying the topologies of all the infinite places and of finitely many primes. -/
theorem denseRange_algebraMap_placeAbv (hinj : Function.Injective ι) :
    DenseRange (algebraMap K (∀ i, WithAbs (placeAbv ι i))) :=
  denseRange_algebraMap_withAbs isNontrivial_placeAbv (pairwise_not_isEquiv_placeAbv hinj)

/-- **Weak approximation for the places of a number field, read as the simultaneous solution of the
approximation conditions**: prescribed targets at all the infinite places and at finitely many
primes are matched to any accuracy by a single element of the field. -/
theorem exists_dist_lt_placeAbv (hinj : Function.Injective ι) (z : InfinitePlace K ⊕ Y → K)
    {r : ℝ} (hr : 0 < r) : ∃ b : K, ∀ i, placeAbv ι i (b - z i) < r :=
  exists_dist_lt_withAbs isNontrivial_placeAbv (pairwise_not_isEquiv_placeAbv hinj) z hr

end InverseGalois.CFT
