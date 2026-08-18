/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.CoverWeak
import InverseGalois.Rigidity.RET.Analytic.Dbar.Puncture

/-!
# A weight of positive curvature and polynomial size

The estimate for the Cauchy–Riemann operator is driven by a weight, and two demands are made of
it.  Its curvature must be positive everywhere, for that is what gives the estimate its content;
and the weight itself must be of polynomial size, for the estimate then bounds a solution by a
polynomial rather than by an exponential.  The logarithm of `1 + |z|²` meets both demands at once:
its curvature is `(1 + |z|²)⁻²`, and its exponential is `1 + |z|²`.

## Main definitions

* `Rigidity.RET.sqWeight` — the polynomial `1 + |z|²`.
* `Rigidity.RET.logWeight` — the weight `log (1 + |z|²)`.

## Main results

* `Rigidity.RET.curv_logWeight` — the curvature of the weight.
* `Rigidity.RET.curv_logWeight_pos` — the curvature is positive.
* `Rigidity.RET.exp_logWeight_re` — the exponential of the weight.
-/

open ComplexConjugate

noncomputable section

namespace Rigidity.RET

/-! ### The polynomial `1 + |z|²` -/

/-- **The polynomial `1 + |z|²`**, read as a function of a complex variable with complex values. -/
def sqWeight (w : ℂ) : ℂ := ((1 + sqDist 0 w : ℝ) : ℂ)

theorem one_add_sqDist_pos (w : ℂ) : (0 : ℝ) < 1 + sqDist 0 w := by
  have := sqDist_nonneg 0 w
  linarith

theorem sqWeight_ne_zero (w : ℂ) : sqWeight w ≠ 0 := by
  rw [sqWeight, ne_eq, Complex.ofReal_eq_zero]
  exact (one_add_sqDist_pos w).ne'

/-- The polynomial is the value of a difference of squares. -/
theorem sqWeight_eq_mul_conj (w : ℂ) : sqWeight w = 1 + w * conj w := by
  rw [sqWeight, Complex.ofReal_add, Complex.ofReal_one, ofReal_sqDist]
  simp

theorem sqWeight_eq_add_one (w : ℂ) : sqWeight w = ((sqDist 0 w : ℝ) : ℂ) + 1 := by
  rw [sqWeight, Complex.ofReal_add, Complex.ofReal_one]
  ring

theorem differentiable_sqWeight : Differentiable ℝ sqWeight := by
  have h : sqWeight = fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ) + 1 := funext sqWeight_eq_add_one
  rw [h]
  exact fun t => ((differentiable_ofReal_sqDist 0) t).add_const 1

theorem conj_sqWeight (w : ℂ) : conj (sqWeight w) = sqWeight w := Complex.conj_ofReal _

theorem contDiff_sqWeight : ContDiff ℝ 2 sqWeight := by
  have h : sqWeight = fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ) + 1 := funext sqWeight_eq_add_one
  rw [h]
  have h1 : ContDiff ℝ 2 fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_sqDist 0).of_le (by decide))
  exact h1.add contDiff_const

theorem sqWeight_mem_slitPlane (w : ℂ) : sqWeight w ∈ Complex.slitPlane := by
  rw [sqWeight]
  exact Complex.ofReal_mem_slitPlane.mpr (one_add_sqDist_pos w)

/-! ### The two derivatives of the polynomial -/

theorem dbar_sqWeight (w : ℂ) : dbar sqWeight w = w := by
  have hfun : sqWeight = fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ) + 1 := funext sqWeight_eq_add_one
  have hd : dbar (fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ) + 1) w
      = dbar (fun t : ℂ => ((sqDist 0 t : ℝ) : ℂ)) w :=
    dbar_add_const 1 ((differentiable_ofReal_sqDist 0) w)
  rw [hfun, hd, dbar_ofReal_sqDist]
  ring

theorem dz_sqWeight (w : ℂ) : dz sqWeight w = conj w := by
  have h := dbar_eq_conj_dz (differentiable_sqWeight w) conj_sqWeight
  rw [dbar_sqWeight] at h
  have := congrArg (starRingEnd ℂ) h
  simpa using this.symm

/-! ### The weight -/

/-- **The weight `log (1 + |z|²)`**. -/
def logWeight (w : ℂ) : ℂ := Complex.log (sqWeight w)

theorem logWeight_eq_ofReal (w : ℂ) :
    logWeight w = ((Real.log (1 + sqDist 0 w) : ℝ) : ℂ) := by
  rw [logWeight, sqWeight, Complex.ofReal_log (one_add_sqDist_pos w).le]

theorem conj_logWeight (w : ℂ) : conj (logWeight w) = logWeight w := by
  rw [logWeight_eq_ofReal]
  exact Complex.conj_ofReal _

theorem logWeight_re (w : ℂ) : (logWeight w).re = Real.log (1 + ‖w‖ ^ 2) := by
  rw [logWeight_eq_ofReal, Complex.ofReal_re, sqDist]
  simp

/-- **The exponential of the weight is a polynomial.** -/
theorem exp_logWeight_re (w : ℂ) : Real.exp ((logWeight w).re) = 1 + ‖w‖ ^ 2 := by
  rw [logWeight_re, Real.exp_log (by positivity)]

theorem contDiff_logWeight : ContDiff ℝ 2 logWeight := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hout : ContDiffAt ℝ 2 Complex.log (sqWeight w) :=
    (Complex.contDiffAt_log (sqWeight_mem_slitPlane w)).restrict_scalars ℝ
  have := hout.comp w contDiff_sqWeight.contDiffAt
  simpa [Function.comp_def, logWeight] using this

/-! ### The curvature of the weight -/

theorem dz_logWeight (w : ℂ) : dz logWeight w = (sqWeight w)⁻¹ * conj w := by
  have hlog : DifferentiableAt ℂ Complex.log (sqWeight w) :=
    (Complex.hasDerivAt_log (sqWeight_mem_slitPlane w)).differentiableAt
  have h : dz (fun t : ℂ => Complex.log (sqWeight t)) w
      = deriv Complex.log (sqWeight w) * dz sqWeight w :=
    dz_comp_holo (differentiable_sqWeight w) hlog
  have hfun : logWeight = fun t : ℂ => Complex.log (sqWeight t) := rfl
  rw [hfun, h, (Complex.hasDerivAt_log (sqWeight_mem_slitPlane w)).deriv, dz_sqWeight]

theorem dbar_inv_sqWeight (w : ℂ) :
    dbar (fun t : ℂ => (sqWeight t)⁻¹) w = -((sqWeight w) ^ 2)⁻¹ * w := by
  have hFinv : DifferentiableAt ℂ (fun t : ℂ => t⁻¹) (sqWeight w) :=
    differentiableAt_inv (sqWeight_ne_zero w)
  have h : dbar (fun t : ℂ => (sqWeight t)⁻¹) w
      = deriv (fun t : ℂ => t⁻¹) (sqWeight w) * dbar sqWeight w :=
    dbar_comp_holo (differentiable_sqWeight w) hFinv
  rw [h, deriv_inv, dbar_sqWeight]

theorem dbar_dz_logWeight (w : ℂ) : dbar (dz logWeight) w = ((sqWeight w) ^ 2)⁻¹ := by
  have hfun : dz logWeight = fun t : ℂ => (sqWeight t)⁻¹ * conj t := funext dz_logWeight
  have hFinv : DifferentiableAt ℂ (fun t : ℂ => t⁻¹) (sqWeight w) :=
    differentiableAt_inv (sqWeight_ne_zero w)
  have hinv : DifferentiableAt ℝ (fun t : ℂ => (sqWeight t)⁻¹) w := by
    have := (hFinv.restrictScalars ℝ).comp w (differentiable_sqWeight w)
    simpa [Function.comp_def] using this
  have hconj : DifferentiableAt ℝ (fun t : ℂ => conj t) w := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt (x := w)
  have hdconj : dbar (fun t : ℂ => conj t) w = 1 := by simpa using dbar_conj_sub 0 w
  have hS : w * conj w = sqWeight w - 1 := by
    rw [sqWeight_eq_mul_conj]
    ring
  rw [hfun, dbar_mul hinv hconj, hdconj, dbar_inv_sqWeight]
  have hne := sqWeight_ne_zero w
  field_simp
  linear_combination -hS

/-- **The curvature of the weight.** -/
theorem curv_logWeight (w : ℂ) : curv logWeight w = ((1 + ‖w‖ ^ 2) ^ 2)⁻¹ := by
  rw [curv, dbar_dz_logWeight, sqWeight, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    Complex.ofReal_re, sqDist]
  simp

/-- **The curvature of the weight is positive.** -/
theorem curv_logWeight_pos (w : ℂ) : 0 < curv logWeight w := by
  rw [curv_logWeight]
  positivity

/-! ### The size of the weight -/

/-- **The weight attached to the exponent is the reciprocal of a polynomial.** -/
theorem weightOf_logWeight (z : ℂ) : weightOf logWeight z = (1 + ‖z‖ ^ 2)⁻¹ := by
  rw [weightOf, Real.exp_neg, exp_logWeight_re]

/-- **On a bounded set the reciprocal of the weight is bounded**, by a bound depending only on the
set. -/
theorem one_le_mul_weightOf_logWeight {z : ℂ} {M : ℝ} (h : ‖z‖ ≤ M) :
    1 ≤ (1 + M ^ 2) * weightOf logWeight z := by
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hle : (1 : ℝ) + ‖z‖ ^ 2 ≤ 1 + M ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  rw [weightOf_logWeight]
  calc (1 : ℝ) = (1 + ‖z‖ ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ := by field_simp
    _ ≤ (1 + M ^ 2) * (1 + ‖z‖ ^ 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hle (by positivity)

end Rigidity.RET

end
