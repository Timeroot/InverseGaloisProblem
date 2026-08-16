/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.PunctureExtend

/-!
# The equation of a function of moderate growth is meromorphic at a puncture

A holomorphic function on a covering of a punctured disc need not be bounded at the puncture, but
it is enough that it grow no faster than a power of the distance to it.  Each coefficient of the
equation the function satisfies is, up to sign, an elementary symmetric function of `|H|` of its
values, so it grows at worst like the `|H|`-th power of that bound; multiplying by a fixed power of
the distance to the puncture makes it bounded, and a bounded analytic function on a punctured disc
extends across the puncture.

So the coefficients are *meromorphic* at the puncture: this is the local statement that a cover of
moderate growth is algebraic, and the reason a pole of the function turns into a pole, not an
essential singularity, of the coefficients of its equation.

## Main results

* `Rigidity.RET.exists_analyticAt_pow_mul_coeff_of_growth` — a fixed power of the distance to the
  puncture times a coefficient extends analytically across it.
* `Rigidity.RET.exists_meromorphicAt_coeff_of_growth` — the coefficients of the equation satisfied
  by a function of moderate growth are meromorphic at the puncture.
-/

open Topology

noncomputable section

namespace Rigidity.RET

section Growth

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **A power of the distance to a puncture times a coefficient of the equation extends
analytically across the puncture**, when the function grows no faster there than a power of the
distance to it. -/
theorem exists_analyticAt_pow_mul_coeff_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsurj : Metric.ball s ρ \ {s} ⊆ Set.range f)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hbdd : ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C) (k : ℕ) :
    ∃ c₀ c : ℂ → ℂ, (∀ y, AnalyticAt ℂ c₀ (f y)) ∧ (∀ y, (orbitPoly H g y).coeff k = c₀ (f y)) ∧
      AnalyticAt ℂ c s ∧
      ∀ z ∈ Metric.ball s ρ \ {s}, (z - s) ^ (N * Fintype.card H) * c₀ z = c z := by
  obtain ⟨c₀, hc₀, hac₀⟩ := exists_analytic_orbitPoly_coeff hf hover htrans hg k
  have hana : ∀ z ∈ Metric.ball s ρ \ {s}, AnalyticAt ℂ c₀ z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hsurj hz
    exact hac₀ y
  have hdiff : DifferentiableOn ℂ (fun z => (z - s) ^ (N * Fintype.card H) * c₀ z)
      (Metric.ball s ρ \ {s}) := by
    intro z hz
    refine AnalyticAt.differentiableAt ?_ |>.differentiableWithinAt
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul (hana z hz)
  have hbd : BddAbove (norm ∘ (fun z => (z - s) ^ (N * Fintype.card H) * c₀ z) ''
      (Metric.ball s ρ \ {s})) := by
    refine ⟨2 ^ Fintype.card H * max C (ρ ^ N) ^ Fintype.card H, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj hz
    have hzs : f y - s ≠ 0 := sub_ne_zero.2 (by simpa using hz.2)
    have hr : 0 < ‖f y - s‖ := norm_pos_iff.2 hzs
    have hrN : 0 < ‖f y - s‖ ^ N := pow_pos hr N
    have hzρ : ‖f y - s‖ < ρ := by rw [← dist_eq_norm]; exact hz.1
    have hM : 0 ≤ C / ‖f y - s‖ ^ N := div_nonneg hC hrN.le
    have hb : ∀ a : H, ‖g (a • y)‖ ≤ C / ‖f y - s‖ ^ N := by
      intro a
      rw [le_div_iff₀ hrN]
      have hy := hbdd (a • y) (by rw [hover a y]; exact hz)
      rwa [hover a y] at hy
    have hcoeff := norm_coeff_orbitPoly_le (H := H) (g := g) (y := y) hM hb k
    have hmax : ‖f y - s‖ ^ N * max (C / ‖f y - s‖ ^ N) 1 = max C (‖f y - s‖ ^ N) := by
      rw [mul_max_of_nonneg _ _ hrN.le, mul_one]
      congr 1
      field_simp
    have h0 : (0 : ℝ) ≤ max C (‖f y - s‖ ^ N) := le_max_of_le_left hC
    have h1 : max C (‖f y - s‖ ^ N) ≤ max C (ρ ^ N) :=
      max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hzρ.le N)
    calc ‖(f y - s) ^ (N * Fintype.card H) * c₀ (f y)‖
        = ‖f y - s‖ ^ (N * Fintype.card H) * ‖(orbitPoly H g y).coeff k‖ := by
          rw [norm_mul, norm_pow, hc₀ y]
      _ ≤ ‖f y - s‖ ^ (N * Fintype.card H) *
            (2 ^ Fintype.card H * max (C / ‖f y - s‖ ^ N) 1 ^ Fintype.card H) :=
          mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = 2 ^ Fintype.card H * (‖f y - s‖ ^ N * max (C / ‖f y - s‖ ^ N) 1) ^ Fintype.card H := by
          rw [mul_pow, pow_mul]
          ring
      _ = 2 ^ Fintype.card H * max C (‖f y - s‖ ^ N) ^ Fintype.card H := by rw [hmax]
      _ ≤ 2 ^ Fintype.card H * max C (ρ ^ N) ^ Fintype.card H :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 _) (by positivity)
  obtain ⟨c, hcA, hceq⟩ := exists_analyticAt_of_bddAbove hρ hdiff hbd
  exact ⟨c₀, c, hac₀, hc₀, hcA, fun z hz => (hceq z hz).symm⟩

/-- **The coefficients of the equation satisfied by a function of moderate growth at a puncture are
meromorphic there.** -/
theorem exists_meromorphicAt_coeff_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) {s : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsurj : Metric.ball s ρ \ {s} ⊆ Set.range f)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hbdd : ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C) (k : ℕ) :
    ∃ c : ℂ → ℂ, (∀ y, AnalyticAt ℂ c (f y)) ∧ MeromorphicAt c s ∧
      ∀ y, (orbitPoly H g y).coeff k = c (f y) := by
  obtain ⟨c₀, c, hac₀, hc₀, hcA, hceq⟩ :=
    exists_analyticAt_pow_mul_coeff_of_growth hf hover htrans hg hρ hsurj hC hbdd k
  refine ⟨c₀, hac₀, ⟨N * Fintype.card H + 1, ?_⟩, hc₀⟩
  have hagree : ∀ z ∈ Metric.ball s ρ,
      (z - s) ^ (N * Fintype.card H + 1) • c₀ z = (z - s) * c z := by
    intro z hz
    by_cases hzs : z = s
    · subst hzs
      simp
    · rw [← hceq z ⟨hz, by simpa using hzs⟩, smul_eq_mul, pow_succ]
      ring
  refine AnalyticAt.congr (f := fun z => (z - s) * c z) ?_ ?_
  · exact (analyticAt_id.sub analyticAt_const).mul hcA
  · filter_upwards [Metric.ball_mem_nhds s hρ] with z hz
    exact (hagree z hz).symm

end Growth

end Rigidity.RET

end
