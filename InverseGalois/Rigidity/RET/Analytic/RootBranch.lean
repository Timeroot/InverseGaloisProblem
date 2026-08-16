/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A continuous branch of a root is holomorphic

A continuous function whose `n`-th power is the identity on an open set of nonzero numbers is
differentiable there, and hence analytic: the difference quotient of such a branch is the
reciprocal of a sum which converges, by continuity alone, to `n` times a nonzero number.  No
inverse function theorem and no choice of a branch of the logarithm are needed — continuity of the
branch is the whole hypothesis.

This is the local regularity of the covering `z ↦ zⁿ`: a local inverse of the power map is
continuous because it is a local homeomorphism, and this page upgrades that to holomorphy.

## Main results

* `Rigidity.RET.hasDerivAt_of_pow_eq` — a continuous branch of an `n`-th root is differentiable,
  with the expected derivative.
* `Rigidity.RET.analyticAt_of_pow_eq` — such a branch is analytic.
-/

open Filter Topology

noncomputable section

namespace Rigidity.RET

variable {n : ℕ} {g : ℂ → ℂ} {U : Set ℂ} {w₀ : ℂ}

/-- A branch of an `n`-th root of a nonzero number is nonzero. -/
theorem ne_zero_of_pow_eq (hn : 0 < n) (hpow : g w₀ ^ n = w₀) (h0 : w₀ ≠ 0) : g w₀ ≠ 0 := by
  intro h
  exact h0 (by rw [← hpow, h, zero_pow hn.ne'])

/-- Two points at which a branch of an `n`-th root takes the same value are equal. -/
theorem eq_of_pow_eq (hpow : ∀ w ∈ U, g w ^ n = w) {w w' : ℂ} (hw : w ∈ U) (hw' : w' ∈ U)
    (h : g w = g w') : w = w' := by
  rw [← hpow w hw, ← hpow w' hw', h]

/-- **A continuous branch of an `n`-th root is differentiable**, with the derivative the
reciprocal of `n` times the `(n-1)`-st power of the branch: the difference quotient is the
reciprocal of a sum whose limit continuity alone supplies. -/
theorem hasDerivAt_of_pow_eq (hn : 0 < n) (hg : ContinuousOn g U)
    (hpow : ∀ w ∈ U, g w ^ n = w) (h0 : ∀ w ∈ U, w ≠ 0) (hw₀ : U ∈ 𝓝 w₀) (hmem : w₀ ∈ U) :
    HasDerivAt g (1 / ((n : ℂ) * g w₀ ^ (n - 1))) w₀ := by
  have hg₀ : g w₀ ≠ 0 := ne_zero_of_pow_eq hn (hpow w₀ hmem) (h0 w₀ hmem)
  -- the limit of the geometric sum
  have hden : ((n : ℂ) * g w₀ ^ (n - 1)) ≠ 0 := by
    refine mul_ne_zero ?_ (pow_ne_zero _ hg₀)
    exact_mod_cast Nat.cast_ne_zero.2 hn.ne'
  have hsum : ∑ i ∈ Finset.range n, g w₀ ^ i * g w₀ ^ (n - 1 - i) = (n : ℂ) * g w₀ ^ (n - 1) := by
    have hterm : ∀ i ∈ Finset.range n, g w₀ ^ i * g w₀ ^ (n - 1 - i) = g w₀ ^ (n - 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the difference quotient
  have hcont : ContinuousAt g w₀ := hg.continuousAt hw₀
  have hlim : Tendsto (fun w => ∑ i ∈ Finset.range n, g w ^ i * g w₀ ^ (n - 1 - i)) (𝓝 w₀)
      (𝓝 ((n : ℂ) * g w₀ ^ (n - 1))) := by
    rw [← hsum]
    exact tendsto_finset_sum _ fun i _ => ((hcont.pow i).mul tendsto_const_nhds)
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : ∀ᶠ w in 𝓝[≠] w₀, slope g w₀ w
      = 1 / ∑ i ∈ Finset.range n, g w ^ i * g w₀ ^ (n - 1 - i) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hw₀] with w hw hwU
    have hne : w ≠ w₀ := hw
    have hgne : g w ≠ g w₀ := fun h => hne (eq_of_pow_eq hpow hwU hmem h)
    have hfac : (∑ i ∈ Finset.range n, g w ^ i * g w₀ ^ (n - 1 - i)) * (g w - g w₀) = w - w₀ := by
      rw [geom_sum₂_mul, hpow w hwU, hpow w₀ hmem]
    rw [slope_def_field, div_eq_div_iff (sub_ne_zero.2 hne) ?_]
    · rw [one_mul, ← hfac]
      ring
    · intro h
      rw [h, zero_mul] at hfac
      exact hne (by linear_combination -hfac)
  have hslope' : (fun w => 1 / ∑ i ∈ Finset.range n, g w ^ i * g w₀ ^ (n - 1 - i))
      =ᶠ[𝓝[≠] w₀] slope g w₀ := hslope.mono fun w hw => hw.symm
  have hgoal : Tendsto (fun w => 1 / ∑ i ∈ Finset.range n, g w ^ i * g w₀ ^ (n - 1 - i)) (𝓝 w₀)
      (𝓝 (1 / ((n : ℂ) * g w₀ ^ (n - 1)))) := tendsto_const_nhds.div hlim hden
  exact Tendsto.congr' hslope' (hgoal.mono_left nhdsWithin_le_nhds)

/-- **A continuous branch of an `n`-th root is analytic.** -/
theorem analyticAt_of_pow_eq (hn : 0 < n) (hU : IsOpen U) (hg : ContinuousOn g U)
    (hpow : ∀ w ∈ U, g w ^ n = w) (h0 : ∀ w ∈ U, w ≠ 0) (hmem : w₀ ∈ U) :
    AnalyticAt ℂ g w₀ := by
  have hdiff : DifferentiableOn ℂ g U := fun w hw =>
    (hasDerivAt_of_pow_eq hn hg hpow h0 (hU.mem_nhds hw)
      hw).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd hU w₀ hmem

end Rigidity.RET

end
