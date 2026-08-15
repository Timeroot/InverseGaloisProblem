/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.InfinityGerm
import InverseGalois.Rigidity.RET.Analytic.RootComp
import InverseGalois.Rigidity.RET.Analytic.RootBound
import InverseGalois.Rigidity.RET.Pi1.Topological.PowerDisc

/-!
# An analytic branch of a family near infinity, as a germ satisfying the equation

A continuous branch of the roots of a monic family, read in the parameter `T = u ^ (-d)` at
infinity on a punctured disc at the origin, is a germ of the meromorphic germ field, and it
satisfies there the very equation it solves pointwise.

The analytic content is a growth estimate.  The branch is holomorphic away from the origin, because
the roots it follows are simple there and a continuous root at a simple root is holomorphic.  It is
not bounded there, since the parameter itself runs off to infinity; but the roots of a monic family
grow at most polynomially in the parameter, so multiplying the branch by a large enough power of
`u` makes it bounded, and a bounded holomorphic function on a punctured disc extends across the
puncture.  Dividing that power back off exhibits the branch as a meromorphic germ.  The rest is a
translation: the ring operations of the germ field are the pointwise ones, so evaluating the family
at the germ of the branch is the germ of the pointwise evaluation, which vanishes.

## Main results

* `Rigidity.RET.Analytic.eval₂_invAlgHom_eq_zero` — the germ of a branch satisfies the equation.
* `Rigidity.RET.Analytic.eval₂_invRatHom_eq_zero` — the same, read over the rational functions.
* `Rigidity.RET.Analytic.meromorphicAt_of_root_inv` — a continuous branch on a punctured disc is
  meromorphic at the origin.
-/

open Filter Topology Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

variable {P : Polynomial (Polynomial ℂ)} {d : ℕ} {g : ℂ → ℂ}

/-! ### Evaluating a family at a germ -/

theorem evalRingHom_comp_invAeval (d : ℕ) (u : ℂ) :
    (Pi.evalRingHom (fun _ : ℂ => ℂ) u).comp
        (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom
      = evalRingHom ((u ^ d)⁻¹) := by
  refine ringHom_ext (fun a => ?_) ?_ <;> simp [invFun]

/-- Evaluating a family at a function of the parameter at infinity is pointwise evaluation of the
specialized equations. -/
theorem eval₂_invAeval_apply (P : Polynomial (Polynomial ℂ)) (d : ℕ) (g : ℂ → ℂ) (u : ℂ) :
    Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom g P u
      = (spec P ((u ^ d)⁻¹)).eval (g u) := by
  have h := Polynomial.hom_eval₂ P (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom
    (Pi.evalRingHom (fun _ : ℂ => ℂ) u) g
  rw [evalRingHom_comp_invAeval] at h
  rw [show Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom g P u
      = (Pi.evalRingHom (fun _ : ℂ => ℂ) u)
        (Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom g P) from rfl, h,
    spec, Polynomial.eval_map]
  rfl

/-- The value of a family at the germ of a meromorphic function is the germ of the pointwise
values. -/
theorem val_eval₂_invAlgHom (P : Polynomial (Polynomial ℂ)) (d : ℕ) (hg : MeromorphicAt g 0) :
    (Polynomial.eval₂ (invAlgHom d).toRingHom (of hg) P).1
      = ((fun u => (spec P ((u ^ d)⁻¹)).eval (g u) : ℂ → ℂ) : PunctGerm (0 : ℂ)) := by
  have h1 := Polynomial.hom_eval₂ P (invAlgHom d).toRingHom (meroGerms (0 : ℂ)).subtype (of hg)
  rw [subtype_comp_invAlgHom] at h1
  have h3 := Polynomial.hom_eval₂ P (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom
    (Filter.Germ.coeRingHom (𝓝[≠] (0 : ℂ))) g
  have h4 : (Polynomial.eval₂ (invAlgHom d).toRingHom (of hg) P).1
      = ((Polynomial.eval₂ (aeval (R := ℂ) (A := ℂ → ℂ) (invFun d)).toRingHom g P :
          ℂ → ℂ) : PunctGerm (0 : ℂ)) :=
    h1.trans h3.symm
  rw [h4]
  exact congrArg (fun f : ℂ → ℂ => (f : PunctGerm (0 : ℂ)))
    (funext fun u => eval₂_invAeval_apply P d g u)

/-- **A meromorphic branch of the roots near infinity gives a germ satisfying the equation.** -/
theorem eval₂_invAlgHom_eq_zero (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec P ((u ^ d)⁻¹)).eval (g u) = 0) :
    Polynomial.eval₂ (invAlgHom d).toRingHom (of hg) P = 0 := by
  refine Subtype.ext ?_
  show (Polynomial.eval₂ (invAlgHom d).toRingHom (of hg) P).1 = ((0 : ℂ → ℂ) : PunctGerm (0 : ℂ))
  rw [val_eval₂_invAlgHom P d hg]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [hroot] with u hu
  exact hu

/-- The same equation, read over the field of rational functions. -/
theorem eval₂_invRatHom_eq_zero (hd : d ≠ 0) (hg : MeromorphicAt g 0)
    (hroot : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (spec P ((u ^ d)⁻¹)).eval (g u) = 0) :
    Polynomial.eval₂ (invRatHom hd : RatFunc ℂ →+* MeroGerm (0 : ℂ)) (of hg)
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) = 0 := by
  rw [Polynomial.eval₂_map]
  rw [show ((invRatHom hd : RatFunc ℂ →+* MeroGerm (0 : ℂ))).comp
      (algebraMap (Polynomial ℂ) (RatFunc ℂ)) = (invAlgHom d).toRingHom from
    RingHom.ext fun p => invRatHom_algebraMap hd p]
  exact eval₂_invAlgHom_eq_zero hg hroot

/-! ### From a continuous branch on a punctured disc to a germ -/

/-- The growth estimate behind the extension across the puncture: multiplying a quantity bounded by
`C * (1 + a⁻¹) ^ m` by `a ^ m` clears the pole and leaves a bound in terms of `a + 1`. -/
theorem mul_pow_le_of_le_inv_pow {C a x : ℝ} (ha : 0 < a) (m : ℕ)
    (hx : x ≤ C * (1 + a⁻¹) ^ m) : a ^ m * x ≤ C * (a + 1) ^ m := by
  have h1 : a ^ m * x ≤ a ^ m * (C * (1 + a⁻¹) ^ m) :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  have h2 : a ^ m * (C * (1 + a⁻¹) ^ m) = C * (a * (1 + a⁻¹)) ^ m := by rw [mul_pow]; ring
  have h3 : a * (1 + a⁻¹) = a + 1 := by field_simp
  rwa [h2, h3] at h1

theorem differentiableOn_invFun (d : ℕ) {ρ : ℝ} :
    DifferentiableOn ℂ (invFun d) (puncturedDisc (0 : ℂ) ρ) := by
  intro u hu
  have hu0 : u ≠ 0 := by simpa using (mem_puncturedDisc.mp hu).2
  exact (((differentiable_pow d) u).inv (pow_ne_zero d hu0)).differentiableWithinAt

/-- A continuous branch of the roots near infinity is holomorphic on the punctured disc: the roots
it follows are simple there. -/
theorem differentiableOn_of_root_inv {ρ : ℝ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).Separable)
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).eval (g u) = 0) :
    DifferentiableOn ℂ g (puncturedDisc (0 : ℂ) ρ) :=
  differentiableOn_of_isRoot_comp (P := P) (isOpen_puncturedDisc _ _) (differentiableOn_invFun d)
    hcont hroot hsep

/-- **A continuous branch of the roots near infinity is meromorphic at the origin.**  The branch is
holomorphic on the punctured disc because the roots are simple there, and the roots of a monic
family grow at most polynomially in the parameter, so a large enough power of `u` times the branch
is bounded and extends across the puncture. -/
theorem meromorphicAt_of_root_inv (hP : P.Monic) (hdeg : 0 < P.natDegree) {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).Separable)
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (spec P ((u ^ d)⁻¹)).eval (g u) = 0) :
    MeromorphicAt g 0 := by
  obtain ⟨Cb, db, hCb, hbd⟩ := exists_root_bound P hP hdeg
  set N : ℕ := d * db with hN
  have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hρ
  have hgdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) ρ \ {0}) :=
    differentiableOn_of_root_inv hcont hsep hroot
  have hdiff : DifferentiableOn ℂ (fun u : ℂ => u ^ N * g u) (Metric.ball (0 : ℂ) ρ \ {0}) :=
    fun u hu => (((differentiable_pow N) u).differentiableWithinAt).mul (hgdiff u hu)
  have hbdd : BddAbove (norm ∘ (fun u : ℂ => u ^ N * g u) '' (Metric.ball (0 : ℂ) ρ \ {0})) := by
    refine ⟨Cb * (ρ ^ d + 1) ^ db, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    have hu0 : u ≠ 0 := by simpa using hu.2
    have hu' : ‖u‖ < ρ := by
      have := hu.1
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at this
    have ha0 : 0 < ‖u‖ ^ d := pow_pos (norm_pos_iff.mpr hu0) d
    have h1 : ‖g u‖ ≤ Cb * (1 + (‖u‖ ^ d)⁻¹) ^ db := by
      have h := hbd _ _ (hroot u hu)
      rwa [norm_inv, norm_pow] at h
    have hpow : ‖u ^ N‖ = (‖u‖ ^ d) ^ db := by rw [norm_pow, hN, pow_mul]
    have hkey : ‖u ^ N * g u‖ ≤ Cb * (‖u‖ ^ d + 1) ^ db := by
      rw [norm_mul, hpow]
      exact mul_pow_le_of_le_inv_pow ha0 db h1
    refine hkey.trans (mul_le_mul_of_nonneg_left ?_ hCb)
    refine pow_le_pow_left₀ (by positivity) ?_ db
    have hle : ‖u‖ ^ d ≤ ρ ^ d := pow_le_pow_left₀ (norm_nonneg u) hu'.le d
    linarith
  set H : ℂ → ℂ := Function.update (fun u : ℂ => u ^ N * g u) 0
    (limUnder (𝓝[≠] (0 : ℂ)) (fun u : ℂ => u ^ N * g u)) with hH
  have hdiffOn : DifferentiableOn ℂ H (Metric.ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hdiff hbdd
  have hana : AnalyticAt ℂ H 0 := hdiffOn.analyticAt hball
  have hprod : MeromorphicAt (fun u : ℂ => invFun N u * H u) 0 :=
    (meromorphicAt_invFun N).mul hana.meromorphicAt
  refine hprod.congr ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  have hHu : H u = u ^ N * g u := Function.update_of_ne hu0 _ _
  rw [hHu, invFun, inv_mul_cancel_left₀ (pow_ne_zero N hu0)]

end Rigidity.RET.Analytic

end
