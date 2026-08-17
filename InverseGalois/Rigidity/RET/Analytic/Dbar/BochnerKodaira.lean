/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Dbar.Commutator

/-!
# The Bochner–Kodaira identity for the Cauchy–Riemann operator

Integrating the pointwise commutator against a weighted plane integral turns it into an identity
between three quadratic forms: the weighted norm of `δv`, the weighted norm of `∂̄v`, and the
integral of the curvature `∂∂̄φ` of the weight against `|v|²`.  Because the middle term enters
with a sign, a weight whose curvature is large forces the adjoint to be large; that is the
mechanism by which an `L²` estimate for `∂/∂z̄` is produced.

## Main definitions

* `Rigidity.RET.wip` — the weighted inner product `⟨f, g⟩ = ∫ f ḡ e^{-φ}`.

## Main results

* `Rigidity.RET.conj_wip` — the weighted inner product is conjugate symmetric.
* `Rigidity.RET.wip_dbar` , `Rigidity.RET.wip_deltaOp` — the two adjoint formulas.
* `Rigidity.RET.bochner_kodaira` — **the Bochner–Kodaira identity**.
-/

open MeasureTheory Set ComplexConjugate

noncomputable section

namespace Rigidity.RET

variable {Φ u v w : ℂ → ℂ}

/-! ### The weighted inner product -/

/-- **The weighted inner product** `⟨f, g⟩ = ∫ f ḡ e^{-φ}` on the plane. -/
def wip (Φ f g : ℂ → ℂ) : ℂ := ∫ z : ℂ, f z * conj (g z) * Complex.exp (-(Φ z))

/-- A real exponent has a real weight. -/
theorem conj_exp_neg (hreal : ∀ w, conj (Φ w) = Φ w) (z : ℂ) :
    conj (Complex.exp (-(Φ z))) = Complex.exp (-(Φ z)) := by
  rw [← Complex.exp_conj]
  simp [hreal z]

/-- A continuous weight against a compactly supported factor gives an integrable product. -/
theorem integrable_wip_integrand {f g : ℂ → ℂ} (hΦ : Continuous Φ) (hf : Continuous f)
    (hg : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun z : ℂ => f z * conj (g z) * Complex.exp (-(Φ z))) := by
  have hcg : Continuous (fun z : ℂ => conj (g z)) := Complex.continuous_conj.comp hg
  have hsg : HasCompactSupport (fun z : ℂ => conj (g z)) :=
    hs.comp_left (g := fun t : ℂ => conj t) (by simp)
  exact ((hf.mul hcg).mul (Complex.continuous_exp.comp hΦ.neg)).integrable_of_hasCompactSupport
    ((hsg.mul_left).mul_right)

/-- **The weighted inner product is conjugate symmetric** when the exponent is real. -/
theorem conj_wip {f g : ℂ → ℂ} (hreal : ∀ w, conj (Φ w) = Φ w) :
    conj (wip Φ f g) = wip Φ g f := by
  rw [wip, wip, ← integral_conj]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp only [map_mul, Complex.conj_conj, conj_exp_neg hreal z]
  ring

/-! ### The two adjoint formulas -/

/-- **The adjoint formula**, read in the weighted inner product. -/
theorem wip_dbar (hΦ : ContDiff ℝ 1 Φ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hs : HasCompactSupport v) (hreal : ∀ w, conj (Φ w) = Φ w) :
    wip Φ (dbar u) v = wip Φ u (deltaOp Φ v) :=
  integral_adjoint hΦ hu hv hs hreal

/-- **The adjoint formula, conjugated**: the weighted adjoint moves back across the inner
product as the Cauchy–Riemann operator. -/
theorem wip_deltaOp (hΦ : ContDiff ℝ 1 Φ) (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w)
    (hs : HasCompactSupport w) (hreal : ∀ t, conj (Φ t) = Φ t) :
    wip Φ w (dbar u) = wip Φ (deltaOp Φ w) u := by
  have h := congrArg conj (wip_dbar hΦ hu hw hs hreal)
  rwa [conj_wip hreal, conj_wip hreal] at h

/-! ### The identity -/

/-- **The Bochner–Kodaira identity.**  The difference of the two weighted quadratic forms is the
curvature of the weight, integrated against `|v|²`. -/
theorem bochner_kodaira (hΦ : ContDiff ℝ 2 Φ) (hv : ContDiff ℝ 2 v) (hs : HasCompactSupport v)
    (hreal : ∀ t, conj (Φ t) = Φ t) :
    wip Φ (deltaOp Φ v) (deltaOp Φ v) - wip Φ (dbar v) (dbar v)
      = ∫ z : ℂ, dbar (dz Φ) z * (v z * conj (v z)) * Complex.exp (-(Φ z)) := by
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hδ : ContDiff ℝ 1 (deltaOp Φ v) := contDiff_one_deltaOp hΦ hv
  have hdb : ContDiff ℝ 1 (dbar v) := contDiff_one_dbar hv
  -- the two adjoint formulas
  have h1 : wip Φ (dbar (deltaOp Φ v)) v = wip Φ (deltaOp Φ v) (deltaOp Φ v) :=
    wip_dbar hΦ1 hδ hv1 hs hreal
  have h2 : wip Φ (dbar v) (dbar v) = wip Φ (deltaOp Φ (dbar v)) v :=
    wip_deltaOp hΦ1 hv1 hdb (hasCompactSupport_dbar hs) hreal
  -- both integrands are integrable
  have hc1 : Continuous (dbar (deltaOp Φ v)) := continuous_dbar hδ
  have hc2 : Continuous (deltaOp Φ (dbar v)) :=
    (continuous_dz hdb).neg.add ((continuous_dz hΦ1).mul (continuous_dbar hv1))
  have hi1 := integrable_wip_integrand (f := dbar (deltaOp Φ v)) (g := v)
    hΦ1.continuous hc1 hv1.continuous hs
  have hi2 := integrable_wip_integrand (f := deltaOp Φ (dbar v)) (g := v)
    hΦ1.continuous hc2 hv1.continuous hs
  rw [← h1, h2, wip, wip, ← integral_sub hi1 hi2]
  refine integral_congr_ae (.of_forall fun z => ?_)
  linear_combination (conj (v z) * Complex.exp (-(Φ z))) * dbar_deltaOp_sub hΦ hv (z := z)

end Rigidity.RET

end
