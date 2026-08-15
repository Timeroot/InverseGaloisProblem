/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.GermLift
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Analytic.Pullback
import InverseGalois.Rigidity.RET.Analytic.RootBound

/-!
# An analytic branch of a family, as a germ satisfying the equation

A continuous branch of the roots of a monic family, read in the Kummer coordinate `T = s + uᵉ` on a
punctured disc at the origin, is a germ of the meromorphic germ field, and it satisfies there the
very equation it solves pointwise.

Two things have to be checked.  The first is analytic: the branch is holomorphic away from the
origin, because the roots it follows are simple there and a continuous root at a simple root is
holomorphic; and it is bounded near the origin, because the roots of a monic family are bounded in
terms of the parameter.  A bounded holomorphic function on a punctured disc extends across the
puncture, so the branch is the germ of a function analytic at the origin.  The second is a
translation: the ring operations of the germ field are the pointwise ones, so evaluating the family
at the germ of the branch is the germ of the pointwise evaluation, which vanishes.

## Main results

* `Rigidity.RET.Analytic.eval₂_kummerHom_eq_zero` — the germ of a branch satisfies the equation.
* `Rigidity.RET.Analytic.eval₂_kummerRatHom_eq_zero` — the same, read over the rational functions.
* `Rigidity.RET.Analytic.exists_analyticAt_of_root_kummer` — a continuous branch on a punctured
  disc is the germ of a function analytic at the origin, and that germ satisfies the equation.
-/

open Filter Topology Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

variable {P : Polynomial (Polynomial ℂ)} {s : ℂ} {e : ℕ} {g : ℂ → ℂ}

/-! ### Evaluating a family at a germ -/

theorem evalRingHom_comp_kummerAlgHom (s : ℂ) (e : ℕ) (u : ℂ) :
    (Pi.evalRingHom (fun _ : ℂ => ℂ) u).comp
        (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom
      = evalRingHom (s + u ^ e) := by
  refine ringHom_ext (fun a => ?_) ?_ <;> simp [kummerFun]

/-- Evaluating a family at a function of the Kummer coordinate is pointwise evaluation of the
specialized equations. -/
theorem eval₂_kummerHom_apply (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) (g : ℂ → ℂ)
    (u : ℂ) :
    Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom g P u
      = (spec P (s + u ^ e)).eval (g u) := by
  have h := Polynomial.hom_eval₂ P (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom
    (Pi.evalRingHom (fun _ : ℂ => ℂ) u) g
  rw [evalRingHom_comp_kummerAlgHom] at h
  rw [show Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom g P u
      = (Pi.evalRingHom (fun _ : ℂ => ℂ) u)
        (Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom g P) from rfl, h,
    spec, Polynomial.eval_map]
  rfl

/-- The value of a family at the germ of a meromorphic function is the germ of the pointwise
values. -/
theorem val_eval₂_kummerHom (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ)
    (hg : MeromorphicAt g 0) :
    (Polynomial.eval₂ (kummerHom s e) (of hg) P).1
      = ((fun u => (spec P (s + u ^ e)).eval (g u) : ℂ → ℂ) : PunctGerm (0 : ℂ)) := by
  have h1 := Polynomial.hom_eval₂ P (kummerHom s e) (meroGerms (0 : ℂ)).subtype (of hg)
  have h2 : ((meroGerms (0 : ℂ)).subtype).comp (kummerHom s e)
      = (Filter.Germ.coeRingHom (𝓝[≠] (0 : ℂ))).comp
          (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom := rfl
  rw [h2] at h1
  have h3 := Polynomial.hom_eval₂ P (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom
    (Filter.Germ.coeRingHom (𝓝[≠] (0 : ℂ))) g
  have h4 : (Polynomial.eval₂ (kummerHom s e) (of hg) P).1
      = ((Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (kummerFun s e)).toRingHom g P :
          ℂ → ℂ) : PunctGerm (0 : ℂ)) :=
    h1.trans h3.symm
  rw [h4]
  exact congrArg (fun f : ℂ → ℂ => (f : PunctGerm (0 : ℂ)))
    (funext fun u => eval₂_kummerHom_apply P s e g u)

/-- **A meromorphic branch of the roots gives a germ satisfying the equation.** -/
theorem eval₂_kummerHom_eq_zero (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec P (s + u ^ e)).eval (g u) = 0) :
    Polynomial.eval₂ (kummerHom s e) (of hg) P = 0 := by
  refine Subtype.ext ?_
  show (Polynomial.eval₂ (kummerHom s e) (of hg) P).1 = ((0 : ℂ → ℂ) : PunctGerm (0 : ℂ))
  rw [val_eval₂_kummerHom P s e hg]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [hroot] with u hu
  exact hu

/-- The same equation, read over the field of rational functions. -/
theorem eval₂_kummerRatHom_eq_zero {d : ℕ} (hd : d ≠ 0) (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec P (s + u ^ d)).eval (g u) = 0) :
    Polynomial.eval₂ (kummerRatHom s hd : RatFunc ℂ →+* MeroGerm (0 : ℂ)) (of hg)
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0 := by
  rw [Polynomial.eval₂_map]
  rw [show ((kummerRatHom s hd : RatFunc ℂ →+* MeroGerm (0 : ℂ))).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = kummerHom s d from
    RingHom.ext fun p => kummerRatHom_algebraMap s hd p]
  exact eval₂_kummerHom_eq_zero hg hroot

/-! ### From a continuous branch on a punctured disc to a germ -/

/-- A continuous branch of the roots is holomorphic on the punctured disc: the roots it follows are
simple there. -/
theorem differentiableOn_of_root_kummer {ρ : ℝ}
    (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P (s + u ^ e)).Separable)
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P (s + u ^ e)).eval (g u) = 0) :
    DifferentiableOn ℂ g (puncturedDisc (0 : ℂ) ρ) :=
  differentiableOn_of_isRoot (P := pullFam P s e) (isOpen_puncturedDisc _ _) hcont
    (fun u hu => by rw [spec_pullFam]; exact hroot u hu)
    (fun u hu => by rw [spec_pullFam]; exact hsep u hu)

/-- **A continuous branch of the roots on a punctured disc is the germ of an analytic function.**
The branch is holomorphic on the punctured disc because the roots are simple there, and bounded near
the centre because the roots of a monic family are bounded in terms of the parameter, so the
singularity at the centre is removable. -/
theorem exists_analyticAt_of_root_kummer (hP : P.Monic) (hdeg : 0 < P.natDegree) {ρ : ℝ}
    (hρ : 0 < ρ) (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P (s + u ^ e)).Separable)
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P (s + u ^ e)).eval (g u) = 0) :
    ∃ (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0), (∀ᶠ u in 𝓝[≠] (0 : ℂ), h u = g u) ∧
      Polynomial.eval₂ (kummerHom s e) (of hh.meromorphicAt) P = 0 := by
  obtain ⟨Cb, db, hCb, hbd⟩ := exists_root_bound P hP hdeg
  have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hρ
  have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) ρ \ {0}) :=
    differentiableOn_of_root_kummer hcont hsep hroot
  have hbdd : BddAbove (norm ∘ g '' (Metric.ball (0 : ℂ) ρ \ {0})) := by
    refine ⟨Cb * (1 + (‖s‖ + ρ ^ e)) ^ db, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    have hu' : ‖u‖ < ρ := by
      have := hu.1
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
    have h1 : ‖g u‖ ≤ Cb * (1 + ‖s + u ^ e‖) ^ db := hbd _ _ (hroot u hu)
    refine le_trans h1 ?_
    have h2 : ‖s + u ^ e‖ ≤ ‖s‖ + ρ ^ e := by
      refine le_trans (norm_add_le _ _) ?_
      have hpow : ‖u ^ e‖ ≤ ρ ^ e := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg u) hu'.le e
      linarith
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) db) hCb
  set h : ℂ → ℂ := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g)
  have hdiffOn : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hdiff hbdd
  have hana : AnalyticAt ℂ h 0 := hdiffOn.analyticAt hball
  have heq : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u = g u := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact Function.update_of_ne (by simpa using hu) _ _
  refine ⟨h, hana, heq, eval₂_kummerHom_eq_zero hana.meromorphicAt ?_⟩
  have hmem : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ puncturedDisc (0 : ℂ) ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with u hu hu'
    exact ⟨hu', by simpa using hu⟩
  filter_upwards [heq, hmem] with u hu hu'
  rw [hu]
  exact hroot u hu'

end Rigidity.RET.Analytic

end
