/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.KummerSection
import InverseGalois.Rigidity.RET.Local.PuiseuxAnalytic

/-!
# Filling in the puncture of a branch of the roots

A branch of the roots of a family, read in the Kummer coordinate, is defined on a punctured disc
around the origin: the origin itself is the parameter where the family degenerates, and nothing so
far says the branch extends across it.  It does, and for the classical reason: the branch is
holomorphic on the punctured disc, because a continuous root of a family is holomorphic wherever
the fibre equation is separable, and it is bounded there, because the roots of a monic family are
bounded by a polynomial in the parameter.  A bounded holomorphic function on a punctured disc
extends holomorphically across the puncture.

The extension is smooth at the origin, so it is a germ in the sense of the Taylor homomorphism, and
its Taylor series is a formal power series solving the family in the Kummer coordinate.  This is
the analytic input to the Puiseux expansion: the algebraic side then only has to read off the
formal root.

## Main results

* `Rigidity.RET.exists_smoothAt_root` — a bounded holomorphic branch of the roots on a punctured
  disc extends to a smooth germ at the origin, still a root of the family.
* `Rigidity.RET.exists_eval₂_kummerSubstC_eq_zero` — the extension has a Taylor series that is a
  formal root of the family in the Kummer coordinate.
-/

open Polynomial Filter Topology

open scoped ContDiff

noncomputable section

namespace Rigidity.RET

variable {P : Polynomial (Polynomial ℂ)}

/-! ### Extending a branch across the puncture -/

/-- **A branch of the roots on a punctured disc extends to a smooth germ at the origin.**  The
branch is holomorphic on the punctured disc because the fibre equations there are separable, and
bounded there because the roots of a monic family grow at most polynomially in the parameter, so
the puncture is a removable singularity. -/
theorem exists_smoothAt_root (hP : P.Monic) (hdeg : 0 < P.natDegree) {s : ℂ} {ρ : ℝ} {e : ℕ}
    (hρ : 0 < ρ) (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (Analytic.spec P (s + u ^ e)).Separable)
    {g : ℂ → ℂ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (Analytic.spec P (s + u ^ e)).eval (g u) = 0) :
    ∃ G : smoothAt (0 : ℂ), (∀ u ∈ puncturedDisc (0 : ℂ) ρ, (G : ℂ → ℂ) u = g u) ∧
      ∀ᶠ u in 𝓝 (0 : ℂ), (Analytic.spec P (s + u ^ e)).eval ((G : ℂ → ℂ) u) = 0 := by
  set Q := Analytic.pullFam P s e with hQ
  have hspec : ∀ u : ℂ, Analytic.spec Q u = Analytic.spec P (s + u ^ e) :=
    Analytic.spec_pullFam P s e
  -- the branch is holomorphic on the punctured disc
  have hd : DifferentiableOn ℂ g (puncturedDisc (0 : ℂ) ρ) :=
    Analytic.differentiableOn_of_isRoot (P := Q) (isOpen_puncturedDisc 0 ρ) hcont
      (fun u hu => by rw [hspec]; exact hroot u hu) (fun u hu => by rw [hspec]; exact hsep u hu)
  -- and bounded there
  obtain ⟨Cb, d, hCb, hbd⟩ := Analytic.exists_root_bound Q (Analytic.monic_pullFam hP s e)
    (by rw [hQ, Analytic.natDegree_pullFam hP]; exact hdeg)
  have hbdd : BddAbove (norm ∘ g '' (puncturedDisc (0 : ℂ) ρ)) := by
    refine ⟨Cb * (1 + ρ) ^ d, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    refine (hbd u (g u) (by rw [hspec]; exact hroot u hu)).trans ?_
    have hlt : ‖u‖ < ρ := by
      have := (mem_puncturedDisc.mp hu).1
      rwa [sub_zero] at this
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) d) hCb
  -- so the puncture is removable
  have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hρ
  set G : ℂ → ℂ := Function.update g 0 (limUnder (𝓝[≠] (0 : ℂ)) g) with hG
  have hdG : DifferentiableOn ℂ G (Metric.ball (0 : ℂ) ρ) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hball hd hbdd
  have hGeq : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, G u = g u := fun u hu =>
    Function.update_of_ne (mem_puncturedDisc.mp hu).2 _ _
  have hsmooth : ContDiffAt ℂ ∞ G 0 := (hdG.analyticAt hball).contDiffAt
  refine ⟨⟨G, hsmooth⟩, hGeq, ?_⟩
  -- the root identity extends to the origin by continuity
  have hcontG : ContinuousAt (fun u : ℂ => Analytic.biEval Q (u, G u)) 0 :=
    (Analytic.continuous_biEval Q).continuousAt.comp
      (continuousAt_id.prodMk (hdG.differentiableAt hball).continuousAt)
  have hzero : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, Analytic.biEval Q (u, G u) = 0 := by
    intro u hu
    show (Analytic.spec Q u).eval (G u) = 0
    rw [hspec, hGeq u hu]
    exact hroot u hu
  have hmem : puncturedDisc (0 : ℂ) ρ ∈ 𝓝[≠] (0 : ℂ) := by
    have h := inter_mem_nhdsWithin ({(0 : ℂ)}ᶜ) hball
    rw [Set.inter_comm, ← Set.diff_eq] at h
    exact h
  have hlim : Tendsto (fun u : ℂ => Analytic.biEval Q (u, G u)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (Filter.eventuallyEq_of_mem hmem fun u hu => (hzero u hu).symm)
  have horigin : Analytic.biEval Q (0, G 0) = 0 :=
    tendsto_nhds_unique (hcontG.tendsto.mono_left nhdsWithin_le_nhds) hlim
  filter_upwards [hball] with u hu
  show (Analytic.spec P (s + u ^ e)).eval (G u) = 0
  rcases eq_or_ne u 0 with rfl | hune
  · rw [← hspec]; exact horigin
  · rw [← hspec]
    exact hzero u
      (mem_puncturedDisc.mpr ⟨by rw [sub_zero]; exact mem_ball_zero_iff.mp hu, hune⟩)

/-! ### The formal root -/

/-- **A branch of the roots on a punctured disc has a Taylor series that is a formal root of the
family in the Kummer coordinate.** -/
theorem exists_eval₂_kummerSubstC_eq_zero (hP : P.Monic) (hdeg : 0 < P.natDegree) {s : ℂ} {ρ : ℝ}
    {e : ℕ} (hρ : 0 < ρ) (hsep : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (Analytic.spec P (s + u ^ e)).Separable)
    {g : ℂ → ℂ} (hcont : ContinuousOn g (puncturedDisc (0 : ℂ) ρ))
    (hroot : ∀ u ∈ puncturedDisc (0 : ℂ) ρ, (Analytic.spec P (s + u ^ e)).eval (g u) = 0) :
    ∃ y : PowerSeries ℂ, Polynomial.eval₂ (kummerSubstC s e) y P = 0 ∧
      ∀ u ∈ puncturedDisc (0 : ℂ) ρ, ∃ G : smoothAt (0 : ℂ),
        y = taylorHom 0 G ∧ (G : ℂ → ℂ) u = g u := by
  obtain ⟨G, hGeq, hGroot⟩ := exists_smoothAt_root hP hdeg hρ hsep hcont hroot
  exact ⟨taylorHom 0 G, eval₂_kummerSubstC_eq_zero P s e G hGroot,
    fun u hu => ⟨G, rfl, hGeq u hu⟩⟩

end Rigidity.RET

end
