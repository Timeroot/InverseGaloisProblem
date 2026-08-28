/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.PowNeighbourhood

/-!
# Elements of a completion close to a given one differ from it by an `n`-th power

At a finite place of a number field the exponential turns a unit congruent to one to sufficient
accuracy into an `n`-th power, and the accuracy is measured by the valuation; reading the valuation
through the rank one homomorphism that defines the norm of the completion turns that into a
statement about the norm.  At an infinite place the completion is the reals or the complexes, and
there an element within distance one of one is a positive real or an arbitrary complex number, in
both cases an `n`-th power.

Dividing by a prescribed nonzero element turns these into the form used by approximation: an
element of the completion close enough to a prescribed nonzero one differs from it by a factor that
is an `n`-th power.  The accuracy needed depends on the place and on the prescribed element, but not
on the element being approximated, so finitely many such conditions can be met at once.

## Main results

* `InverseGalois.CFT.exists_pow_eq_of_norm_sub_one_lt_adicCompletion`: **at a finite place the
  `n`-th powers contain every element close enough to one.**
* `InverseGalois.CFT.exists_pow_eq_of_norm_sub_one_lt_infiniteCompletion`: **at an infinite place
  the `n`-th powers contain every element within distance one of one.**
* `InverseGalois.CFT.exists_pow_mul_eq_of_norm_sub_lt_adicCompletion`,
  `InverseGalois.CFT.exists_pow_mul_eq_of_norm_sub_lt_infiniteCompletion`: **an element close enough
  to a prescribed nonzero element differs from it by an `n`-th power.**

## Tags

number field, completion, place, power, approximation, norm
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

/-! ### The finite places -/

section Adic

variable (v : HeightOneSpectrum (𝓞 K))

/-- The norm of the completion at a finite place is the rank one homomorphism applied to the
valuation. -/
theorem norm_adicCompletion_eq (x : v.adicCompletion K) :
    ‖x‖ = (Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (Valued.v x) :
      ℝ) :=
  rfl

/-- The rank one homomorphism is positive at a nonzero value. -/
theorem zero_lt_rankOne_hom {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    (0 : ℝ) < (Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) γ : ℝ) := by
  have hne : Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) γ ≠ 0 := by
    simp only [ne_eq, Valuation.RankOne.hom_eq_zero_iff]
    exact hγ
  positivity

/-- A norm smaller than the value of the rank one homomorphism at a value of the valuation group
means a valuation smaller than that value. -/
theorem valued_lt_of_norm_lt_hom {x : v.adicCompletion K} {γ : ℤᵐ⁰}
    (h : ‖x‖ < (Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) γ : ℝ)) :
    Valued.v x < γ := by
  have h1 : Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (Valued.v x)
      < Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) γ := by
    rw [norm_adicCompletion_eq] at h
    exact_mod_cast h
  exact (Valuation.RankOne.strictMono
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).lt_iff_lt.mp h1

/-- **At a finite place the `n`-th powers contain every element close enough to one.**  The
accuracy is the one supplied by the exponential, read through the rank one homomorphism. -/
theorem exists_pow_eq_of_norm_sub_one_lt_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : v.adicCompletion K, ‖u - 1‖ < r →
      ∃ y : v.adicCompletion K, y ^ n = u := by
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion v
  obtain ⟨i, hi⟩ := exists_pow_eq_of_valued_sub_one_le hres hn
  exact ⟨(Valuation.RankOne.hom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (WithZero.exp (-(i : ℤ))) : ℝ), zero_lt_rankOne_hom v WithZero.exp_ne_zero,
    fun u hu => hi u (le_of_lt (valued_lt_of_norm_lt_hom v hu))⟩

/-- **An element of the completion at a finite place close enough to a prescribed nonzero element
differs from it by an `n`-th power.** -/
theorem exists_pow_mul_eq_of_norm_sub_lt_adicCompletion {n : ℕ} (hn : n ≠ 0)
    {c : v.adicCompletion K} (hc : c ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ b : v.adicCompletion K, ‖b - c‖ < r →
      ∃ y : v.adicCompletion K, y ^ n * c = b := by
  obtain ⟨r, hr, hpow⟩ := exists_pow_eq_of_norm_sub_one_lt_adicCompletion v hn
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  refine ⟨r * ‖c‖, by positivity, fun b hb => ?_⟩
  have hlt : ‖b * c⁻¹ - 1‖ < r := by
    have h1 : b * c⁻¹ - 1 = (b - c) * c⁻¹ := by field_simp
    rw [h1, norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_iff₀ hcpos]
    exact hb
  obtain ⟨y, hy⟩ := hpow (b * c⁻¹) hlt
  exact ⟨y, by rw [hy, inv_mul_cancel_right₀ hc]⟩

end Adic

/-! ### The infinite places -/

section Infinite

variable (w : InfinitePlace K)

omit [NumberField K] in
/-- The isomorphism onto the reals at a real place preserves the norm. -/
theorem norm_ringEquivRealOfIsReal (hw : w.IsReal) (x : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  rw [dist_eq_norm, dist_eq_norm] at h
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = (0 : ℝ) :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rwa [h0, sub_zero, sub_zero] at h

omit [NumberField K] in
/-- **At an infinite place the `n`-th powers contain every element within distance one of one.**
At a real place such an element is positive, and at a complex place every element is an `n`-th
power. -/
theorem exists_pow_eq_of_norm_sub_one_lt_infiniteCompletion {n : ℕ} (hn : n ≠ 0)
    {u : w.Completion} (hu : ‖u - 1‖ < 1) : ∃ y : w.Completion, y ^ n = u := by
  rcases w.isReal_or_isComplex with hw | hw
  · set f := InfinitePlace.Completion.ringEquivRealOfIsReal hw with hf
    have hnorm : ‖f u - 1‖ < 1 := by
      rw [show f u - 1 = f (u - 1) by rw [map_sub, map_one], norm_ringEquivRealOfIsReal]
      exact hu
    have hpos : (0 : ℝ) < f u := by
      rcases abs_lt.mp (by rwa [Real.norm_eq_abs] at hnorm) with ⟨h1, -⟩
      linarith
    refine ⟨f.symm ((f u) ^ ((n : ℝ)⁻¹)), ?_⟩
    rw [← map_pow, Real.rpow_inv_natCast_pow hpos.le hn, RingEquiv.symm_apply_apply]
  · set g := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with hg
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (g u) (Nat.pos_of_ne_zero hn)
    exact ⟨g.symm y, by rw [← map_pow, hy, RingEquiv.symm_apply_apply]⟩

omit [NumberField K] in
/-- **An element of the completion at an infinite place close enough to a prescribed nonzero
element differs from it by an `n`-th power.** -/
theorem exists_pow_mul_eq_of_norm_sub_lt_infiniteCompletion {n : ℕ} (hn : n ≠ 0)
    {c : w.Completion} (hc : c ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ b : w.Completion, ‖b - c‖ < r → ∃ y : w.Completion, y ^ n * c = b := by
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  refine ⟨‖c‖, hcpos, fun b hb => ?_⟩
  have hlt : ‖b * c⁻¹ - 1‖ < 1 := by
    have h1 : b * c⁻¹ - 1 = (b - c) * c⁻¹ := by field_simp
    rw [h1, norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hcpos]
    exact hb
  obtain ⟨y, hy⟩ := exists_pow_eq_of_norm_sub_one_lt_infiniteCompletion w hn hlt
  exact ⟨y, by rw [hy, inv_mul_cancel_right₀ hc]⟩

end Infinite

end InverseGalois.CFT
