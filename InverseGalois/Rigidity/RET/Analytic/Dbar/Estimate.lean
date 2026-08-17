/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.BochnerKodaira

/-!
# The a priori estimate for the Cauchy–Riemann operator

Read on a real exponent, the Bochner–Kodaira identity becomes an identity between real quadratic
forms, and dropping the term that carries a sign leaves an inequality: a weight whose curvature is
bounded below by a positive constant forces the weighted norm of the adjoint to dominate the
weighted norm of the function.  That inequality is the a priori estimate on which the `L²`
existence theory for `∂/∂z̄` rests.

## Main definitions

* `Rigidity.RET.wnorm2` — the weighted square norm `∫ |f|² e^{-φ}`.

## Main results

* `Rigidity.RET.wip_self` — the weighted inner product of a function with itself is its weighted
  square norm.
* `Rigidity.RET.conj_dbar_dz` — the curvature of a real weight is real.
* `Rigidity.RET.bochner_kodaira_real` — the identity, read on real quadratic forms.
* `Rigidity.RET.curvature_estimate` — **the a priori estimate**.
-/

open MeasureTheory Set ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Φ v : ℂ → ℂ}

/-! ### A real exponent -/

/-- A real exponent has a real weight. -/
theorem exp_neg_eq_ofReal (hreal : ∀ t, conj (Φ t) = Φ t) (z : ℂ) :
    Complex.exp (-(Φ z)) = ((Real.exp (-(Φ z).re) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  rw [Complex.ofReal_neg, Complex.conj_eq_iff_re.mp (hreal z)]

/-- **The curvature of a real weight is real.**  Conjugation exchanges the two first-order
operators, and they commute, so the second derivative of a real function is its own conjugate. -/
theorem conj_dbar_dz (hΦ : ContDiff ℝ 2 Φ) (hreal : ∀ t, conj (Φ t) = Φ t) (z : ℂ) :
    conj (dbar (dz Φ) z) = dbar (dz Φ) z := by
  have hfun : (fun w => conj (dbar Φ w)) = dz Φ := by
    funext w
    rw [dbar_eq_conj_dz (hΦ.differentiable (by norm_num) w) hreal, Complex.conj_conj]
  have h1 : dbar (dz Φ) z = conj (dz (dbar Φ) z) := by
    have h := dbar_conj (f := dbar Φ) (z := z)
      (differentiableAt_dbar (differentiableAt_fderiv_of_contDiff_two hΦ))
    rwa [hfun] at h
  calc conj (dbar (dz Φ) z) = conj (dz (dbar Φ) z) := by rw [dbar_dz_comm hΦ]
    _ = dbar (dz Φ) z := h1.symm

/-! ### The weighted square norm -/

/-- **The weighted square norm** `∫ |f|² e^{-φ}` of a function of a complex variable. -/
def wnorm2 (Φ f : ℂ → ℂ) : ℝ := ∫ z : ℂ, ‖f z‖ ^ 2 * Real.exp (-(Φ z).re)

/-- The weighted square norm is nonnegative. -/
theorem wnorm2_nonneg (Φ f : ℂ → ℂ) : 0 ≤ wnorm2 Φ f :=
  integral_nonneg fun z => by positivity

/-- **The weighted inner product of a function with itself is its weighted square norm.** -/
theorem wip_self (hreal : ∀ t, conj (Φ t) = Φ t) (f : ℂ → ℂ) :
    wip Φ f f = ((wnorm2 Φ f : ℝ) : ℂ) := by
  rw [wip, wnorm2, ← integral_complex_ofReal]
  refine integral_congr_ae (.of_forall fun z => ?_)
  show f z * conj (f z) * Complex.exp (-(Φ z)) = ((‖f z‖ ^ 2 * Real.exp (-(Φ z).re) : ℝ) : ℂ)
  rw [Complex.mul_conj, exp_neg_eq_ofReal hreal z, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ### The identity on real quadratic forms -/

/-- **The Bochner–Kodaira identity**, read on real quadratic forms. -/
theorem bochner_kodaira_real (hΦ : ContDiff ℝ 2 Φ) (hv : ContDiff ℝ 2 v)
    (hs : HasCompactSupport v) (hreal : ∀ t, conj (Φ t) = Φ t) :
    wnorm2 Φ (deltaOp Φ v) - wnorm2 Φ (dbar v)
      = ∫ z : ℂ, (dbar (dz Φ) z).re * ‖v z‖ ^ 2 * Real.exp (-(Φ z).re) := by
  have hR : (∫ z : ℂ, dbar (dz Φ) z * (v z * conj (v z)) * Complex.exp (-(Φ z)))
      = ((∫ z : ℂ, (dbar (dz Φ) z).re * ‖v z‖ ^ 2 * Real.exp (-(Φ z).re) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun z => ?_)
    show dbar (dz Φ) z * (v z * conj (v z)) * Complex.exp (-(Φ z))
      = (((dbar (dz Φ) z).re * ‖v z‖ ^ 2 * Real.exp (-(Φ z).re) : ℝ) : ℂ)
    set κ : ℝ := (dbar (dz Φ) z).re with hκdef
    have hκ : dbar (dz Φ) z = (κ : ℂ) :=
      (Complex.conj_eq_iff_re.mp (conj_dbar_dz hΦ hreal z)).symm
    rw [hκ, Complex.mul_conj, exp_neg_eq_ofReal hreal z, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h := bochner_kodaira hΦ hv hs hreal
  rw [wip_self hreal, wip_self hreal, hR] at h
  exact_mod_cast h

/-! ### The estimate -/

/-- **The a priori estimate.**  If the curvature of the weight is bounded below by `c`, then the
weighted norm of the adjoint dominates `c` times the weighted norm of the function. -/
theorem curvature_estimate (hΦ : ContDiff ℝ 2 Φ) (hv : ContDiff ℝ 2 v)
    (hs : HasCompactSupport v) (hreal : ∀ t, conj (Φ t) = Φ t) {c : ℝ}
    (hc : ∀ z, c ≤ (dbar (dz Φ) z).re) :
    c * wnorm2 Φ v ≤ wnorm2 Φ (deltaOp Φ v) := by
  -- the two integrands
  have hexp : Continuous fun z : ℂ => Real.exp (-(Φ z).re) :=
    Real.continuous_exp.comp (Complex.continuous_re.comp (hΦ.continuous)).neg
  have hv2 : Continuous fun z : ℂ => ‖v z‖ ^ 2 := (hv.continuous.norm).pow 2
  have hsv2 : HasCompactSupport fun z : ℂ => ‖v z‖ ^ 2 :=
    hs.comp_left (g := fun t : ℂ => ‖t‖ ^ 2) (by simp)
  have hκc : Continuous fun z : ℂ => (dbar (dz Φ) z).re :=
    Complex.continuous_re.comp (continuous_dbar (contDiff_one_dz hΦ))
  have hi1 : Integrable fun z : ℂ => c * (‖v z‖ ^ 2 * Real.exp (-(Φ z).re)) :=
    ((continuous_const.mul (hv2.mul hexp))).integrable_of_hasCompactSupport
      ((hsv2.mul_right).mul_left)
  have hi2 : Integrable fun z : ℂ => (dbar (dz Φ) z).re * ‖v z‖ ^ 2 * Real.exp (-(Φ z).re) :=
    (((hκc.mul hv2).mul hexp)).integrable_of_hasCompactSupport ((hsv2.mul_left).mul_right)
  -- the curvature bound
  have hstep : c * wnorm2 Φ v
      ≤ ∫ z : ℂ, (dbar (dz Φ) z).re * ‖v z‖ ^ 2 * Real.exp (-(Φ z).re) := by
    rw [wnorm2, ← integral_const_mul]
    refine integral_mono hi1 hi2 fun z => ?_
    have h1 : c * ‖v z‖ ^ 2 ≤ (dbar (dz Φ) z).re * ‖v z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hc z) (by positivity)
    calc c * (‖v z‖ ^ 2 * Real.exp (-(Φ z).re))
        = (c * ‖v z‖ ^ 2) * Real.exp (-(Φ z).re) := by ring
      _ ≤ ((dbar (dz Φ) z).re * ‖v z‖ ^ 2) * Real.exp (-(Φ z).re) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  -- and the term that is dropped
  have hid := bochner_kodaira_real hΦ hv hs hreal
  have hnn := wnorm2_nonneg Φ (dbar v)
  linarith [hstep, hid, hnn]

end Rigidity.RET

end
