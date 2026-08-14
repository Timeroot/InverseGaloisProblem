/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Entire functions of polynomial growth are polynomials

Liouville's theorem says that a bounded entire function is constant.  This file records the
quantitative refinement: an entire function bounded by a constant times `(1 + ‖z‖) ^ n` is a
polynomial of degree at most `n`.

The proof is an induction on `n`.  A bound with `n = 0` is a genuine bound, so Liouville applies
and the function is constant.  For the inductive step one divides out the value at the origin: the
difference quotient `dslope f 0`, which is entire because the singularity at the origin is
removable, satisfies a bound one degree lower — away from the unit disc because dividing by `z`
gains a factor of `z`, and inside the unit disc because a continuous function on a compact set is
bounded.  The induction hypothesis turns the difference quotient into a polynomial `q`, and then
`f = f 0 + X * q`.

This is the growth half of the classical argument that recovers an algebraic factorization from an
analytic one: symmetric functions of a family of roots are holomorphic away from the degeneracy
locus, extend across it because roots of a monic polynomial are bounded by its coefficients, and
grow polynomially at infinity for the same reason — so they are polynomials.

## Main results

* `Rigidity.RET.Analytic.exists_polynomial_of_growth` — an entire function bounded by
  `C * (1 + ‖z‖) ^ n` agrees with a polynomial of degree at most `n`.
* `Rigidity.RET.Analytic.exists_polynomial_of_growth_le` — the same with the bound only assumed
  outside a bounded region.
-/

open Metric Filter

noncomputable section

namespace Rigidity.RET.Analytic

/-- **An entire function of polynomial growth is a polynomial**, in the form the induction on the
degree needs: all the data quantified inside. -/
theorem exists_polynomial_of_growth_forall (n : ℕ) : ∀ (f : ℂ → ℂ) (C : ℝ),
    Differentiable ℂ f → (∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ n) →
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z, f z = p.eval z := by
  induction n with
  | zero =>
    intro f C hf hgrowth
    obtain ⟨c, hc⟩ := hf.exists_const_forall_eq_of_bounded
      (isBounded_iff_forall_norm_le.2 ⟨C, by rintro x ⟨z, rfl⟩; simpa using hgrowth z⟩)
    exact ⟨Polynomial.C c, by simp, fun z => by simp [hc z]⟩
  | succ n ih =>
    intro f C hf hgrowth
    have hf0 : ‖f 0‖ ≤ C := by simpa using hgrowth 0
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hf0
    have hg : Differentiable ℂ (dslope f 0) :=
      differentiableOn_univ.mp
        ((Complex.differentiableOn_dslope Filter.univ_mem).2 hf.differentiableOn)
    have hkey : ∀ z : ℂ, z * dslope f 0 z = f z - f 0 := fun z => by
      simpa [smul_eq_mul] using sub_smul_dslope f 0 z
    -- Outside the unit disc, dividing by `z` gains a whole degree.
    have hbig : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖dslope f 0 z‖ ≤ (2 * C + ‖f 0‖) * (1 + ‖z‖) ^ n := by
      intro z hz
      have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz
      have hA1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (by linarith [norm_nonneg z])
      have hA0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ n := le_trans zero_le_one hA1
      have hpow : (1 + ‖z‖) ^ (n + 1) = (1 + ‖z‖) * (1 + ‖z‖) ^ n := by ring
      have h1 : ‖z‖ * ‖dslope f 0 z‖ = ‖f z - f 0‖ := by rw [← norm_mul, hkey z]
      have step1 : ‖f z - f 0‖ ≤ C * ((1 + ‖z‖) * (1 + ‖z‖) ^ n) + ‖f 0‖ := by
        have h := hgrowth z
        rw [hpow] at h
        linarith [norm_sub_le (f z) (f 0)]
      have step2 : C * ((1 + ‖z‖) * (1 + ‖z‖) ^ n) ≤ 2 * C * ‖z‖ * (1 + ‖z‖) ^ n := by
        have hle2 : 1 + ‖z‖ ≤ 2 * ‖z‖ := by linarith
        have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle2 hA0) hC0
        linarith
      have step3 : ‖f 0‖ ≤ ‖f 0‖ * ‖z‖ * (1 + ‖z‖) ^ n := by
        have h1 : ‖f 0‖ * 1 ≤ ‖f 0‖ * ‖z‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        have h2 : ‖f 0‖ * ‖z‖ * 1 ≤ ‖f 0‖ * ‖z‖ * (1 + ‖z‖) ^ n :=
          mul_le_mul_of_nonneg_left hA1 (by positivity)
        linarith
      have hexp : ‖z‖ * ((2 * C + ‖f 0‖) * (1 + ‖z‖) ^ n)
          = 2 * C * ‖z‖ * (1 + ‖z‖) ^ n + ‖f 0‖ * ‖z‖ * (1 + ‖z‖) ^ n := by ring
      refine le_of_mul_le_mul_left ?_ hz0
      rw [h1, hexp]
      linarith
    -- Inside the unit disc, continuity on a compact set is enough.
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    have hsmall : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖dslope f 0 z‖ ≤ max M 0 * (1 + ‖z‖) ^ n := by
      intro z hz
      have hmem : z ∈ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, dist_zero_right] using hz
      have hA1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (by linarith [norm_nonneg z])
      have h3 : max M 0 * 1 ≤ max M 0 * (1 + ‖z‖) ^ n :=
        mul_le_mul_of_nonneg_left hA1 (le_max_right M 0)
      linarith [hM z hmem, le_max_left M (0 : ℝ)]
    have hCn : 0 ≤ 2 * C + ‖f 0‖ := by linarith [norm_nonneg (f 0)]
    have hbound : ∀ z : ℂ,
        ‖dslope f 0 z‖ ≤ (2 * C + ‖f 0‖ + max M 0) * (1 + ‖z‖) ^ n := by
      intro z
      have hA0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ n := by positivity
      rcases le_or_gt 1 ‖z‖ with h | h
      · linarith [hbig z h, mul_nonneg (le_max_right M (0 : ℝ)) hA0]
      · linarith [hsmall z h.le, mul_nonneg hCn hA0]
    obtain ⟨q, hqdeg, hq⟩ := ih (dslope f 0) (2 * C + ‖f 0‖ + max M 0) hg hbound
    refine ⟨Polynomial.C (f 0) + Polynomial.X * q, ?_, fun z => ?_⟩
    · have h1 : (Polynomial.X * q : Polynomial ℂ).natDegree ≤ n + 1 := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        simp only [Polynomial.natDegree_X]
        omega
      exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) h1)
    · have h := hkey z
      rw [hq z] at h
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
      linear_combination -h

/-- **An entire function of polynomial growth is a polynomial.** -/
theorem exists_polynomial_of_growth {f : ℂ → ℂ} {C : ℝ} {n : ℕ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ n) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z, f z = p.eval z :=
  exists_polynomial_of_growth_forall n f C hf hgrowth

/-- **An entire function is a polynomial as soon as it grows polynomially away from a bounded
region**: on the bounded region continuity supplies its own bound. -/
theorem exists_polynomial_of_growth_le {f : ℂ → ℂ} {C R : ℝ} {n : ℕ} (hf : Differentiable ℂ f)
    (hgrowth : ∀ z, R ≤ ‖z‖ → ‖f z‖ ≤ C * (1 + ‖z‖) ^ n) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z, f z = p.eval z := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  refine exists_polynomial_of_growth (C := max C 0 + max M 0) hf fun z => ?_
  have hA1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (by linarith [norm_nonneg z])
  have hA0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ n := le_trans zero_le_one hA1
  rcases le_or_gt R ‖z‖ with h | h
  · have h1 : C * (1 + ‖z‖) ^ n ≤ max C 0 * (1 + ‖z‖) ^ n :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hA0
    linarith [hgrowth z h, mul_nonneg (le_max_right M (0 : ℝ)) hA0]
  · have hmem : z ∈ closedBall (0 : ℂ) R := by
      simpa [mem_closedBall, dist_zero_right] using h.le
    have h3 : max M 0 * 1 ≤ max M 0 * (1 + ‖z‖) ^ n :=
      mul_le_mul_of_nonneg_left hA1 (le_max_right M 0)
    linarith [hM z hmem, le_max_left M (0 : ℝ),
      mul_nonneg (le_max_right C (0 : ℝ)) hA0]

end Rigidity.RET.Analytic

end
