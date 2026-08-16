/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.EntireGrowth
import InverseGalois.Rigidity.RET.Analytic.CoverInvariant
import InverseGalois.Rigidity.RET.Analytic.InterpRational
import InverseGalois.Rigidity.RET.Analytic.IntegralPackage

/-!
# Functions of moderate growth on a covering

The growth conditions under which a holomorphic function on a covering of a punctured plane is
algebraic over the base — no faster than a power of the distance to each puncture, no faster than
a power of `‖z‖` at infinity — are stable under the ring operations, and they hold for the
polynomials of the base coordinate.  Bundling them into a single predicate turns the long lists of
estimates carried by the growth theorems into one hypothesis, and exhibits the functions they
apply to as a subring of the functions on the total space.

The estimates behind the closure properties are the obvious ones: exponents add under
multiplication, and under addition the larger of the two exponents works once the discs are small
enough for the distance to be at most one.

## Main definitions

* `Rigidity.RET.IsModerate` — the two growth conditions, at the punctures and at infinity.

## Main results

* `Rigidity.RET.IsModerate.add`, `Rigidity.RET.IsModerate.mul`, `Rigidity.RET.IsModerate.sub` —
  moderate growth is stable under the ring operations.
* `Rigidity.RET.isModerate_polynomial` — a polynomial in the base coordinate is of moderate growth.
* `Rigidity.RET.isIntegralElem_of_moderate`, `Rigidity.RET.exists_eq_div_of_invariant_of_moderate`,
  `Rigidity.RET.exists_eq_div_of_separating_of_moderate` — the growth theorems, restated with the
  bundled hypothesis.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### Two elementary estimates -/

/-- Raising the exponent of a factor at most one only lowers the product. -/
theorem mul_pow_le_of_le {x r C : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hr1 : r ≤ 1) {N M : ℕ}
    (hNM : N ≤ M) (h : x * r ^ N ≤ C) : x * r ^ M ≤ C := by
  have hsplit : x * r ^ M = x * r ^ N * r ^ (M - N) := by
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hsplit]
  refine le_trans ?_ h
  calc x * r ^ N * r ^ (M - N) ≤ x * r ^ N * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr hr1) (by positivity)
    _ = x * r ^ N := mul_one _

/-- Raising the exponent of a factor at least one only raises the bound. -/
theorem le_mul_pow_of_le {x A z : ℝ} (hA : 0 ≤ A) (hz : 1 ≤ z) {m M : ℕ} (hmM : m ≤ M)
    (h : x ≤ A * z ^ m) : x ≤ A * z ^ M :=
  h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hmM) hA)

/-! ### Moderate growth -/

section Defs

variable {Y : Type*} {f F G : Y → ℂ} {S : Finset ℂ}

/-- **A function on the total space is of moderate growth** when at each puncture some fixed power
of the distance to it times the function is bounded, and at infinity the function grows no faster
than a power of the base coordinate. -/
structure IsModerate (f : Y → ℂ) (S : Finset ℂ) (F : Y → ℂ) : Prop where
  /-- At each puncture, a fixed power of the distance to it times the function is bounded. -/
  punct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
    ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C
  /-- At infinity, the function grows no faster than a power of the base coordinate. -/
  infty : ∃ (A R₀ : ℝ) (m : ℕ), 0 ≤ A ∧ ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A * ‖f y‖ ^ m

/-- The estimate at a puncture may always be taken on a disc of radius at most one. -/
theorem IsModerate.punct_le_one (hF : IsModerate f S F) {s : ℂ} (hs : s ∈ S) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C := by
  obtain ⟨ρ, hρ, C, hC, N, hbdd⟩ := hF.punct s hs
  refine ⟨min ρ 1, lt_min hρ one_pos, min_le_right _ _, C, hC, N, fun y hy => ?_⟩
  exact hbdd y ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩

/-- The estimate at infinity may always be taken beyond the unit circle. -/
theorem IsModerate.infty_one_le (hF : IsModerate f S F) :
    ∃ (A R₀ : ℝ) (m : ℕ), 0 ≤ A ∧ 1 ≤ R₀ ∧
      ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A * ‖f y‖ ^ m := by
  obtain ⟨A, R₀, m, hA, hbdd⟩ := hF.infty
  exact ⟨A, max R₀ 1, m, hA, le_max_right _ _,
    fun y hy => hbdd y (le_trans (le_max_left _ _) hy)⟩

/-- A constant function is of moderate growth. -/
theorem isModerate_const (f : Y → ℂ) (S : Finset ℂ) (c : ℂ) :
    IsModerate f S fun _ : Y => c where
  punct := fun s _ => ⟨1, one_pos, ‖c‖, norm_nonneg c, 0, fun y _ => by simp⟩
  infty := ⟨‖c‖, 1, 0, norm_nonneg c, fun y _ => by simp⟩

/-- A sum of two functions of moderate growth is of moderate growth. -/
theorem IsModerate.add (hF : IsModerate f S F) (hG : IsModerate f S G) :
    IsModerate f S fun y => F y + G y where
  punct := by
    intro s hs
    obtain ⟨ρ₁, hρ₁, hρ₁1, C₁, hC₁, N₁, hb₁⟩ := hF.punct_le_one hs
    obtain ⟨ρ₂, hρ₂, hρ₂1, C₂, hC₂, N₂, hb₂⟩ := hG.punct_le_one hs
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, C₁ + C₂, by positivity, max N₁ N₂, fun y hy => ?_⟩
    have hy₁ : f y ∈ Metric.ball s ρ₁ \ {s} :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    have hy₂ : f y ∈ Metric.ball s ρ₂ \ {s} :=
      ⟨Metric.ball_subset_ball (min_le_right _ _) hy.1, hy.2⟩
    have hr1 : ‖f y - s‖ ≤ 1 := by
      have h := hy.1
      rw [Metric.mem_ball, Complex.dist_eq] at h
      exact le_of_lt (lt_of_lt_of_le h (le_trans (min_le_left _ _) hρ₁1))
    have h₁ : ‖F y‖ * ‖f y - s‖ ^ max N₁ N₂ ≤ C₁ :=
      mul_pow_le_of_le (norm_nonneg _) (norm_nonneg _) hr1 (le_max_left _ _) (hb₁ y hy₁)
    have h₂ : ‖G y‖ * ‖f y - s‖ ^ max N₁ N₂ ≤ C₂ :=
      mul_pow_le_of_le (norm_nonneg _) (norm_nonneg _) hr1 (le_max_right _ _) (hb₂ y hy₂)
    calc ‖F y + G y‖ * ‖f y - s‖ ^ max N₁ N₂
        ≤ (‖F y‖ + ‖G y‖) * ‖f y - s‖ ^ max N₁ N₂ :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ = ‖F y‖ * ‖f y - s‖ ^ max N₁ N₂ + ‖G y‖ * ‖f y - s‖ ^ max N₁ N₂ := by ring
      _ ≤ C₁ + C₂ := add_le_add h₁ h₂
  infty := by
    obtain ⟨A₁, R₁, m₁, hA₁, hR₁, hb₁⟩ := hF.infty_one_le
    obtain ⟨A₂, R₂, m₂, hA₂, hR₂, hb₂⟩ := hG.infty_one_le
    refine ⟨A₁ + A₂, max R₁ R₂, max m₁ m₂, by positivity, fun y hy => ?_⟩
    have hz : (1 : ℝ) ≤ ‖f y‖ := le_trans hR₁ (le_trans (le_max_left _ _) hy)
    have h₁ : ‖F y‖ ≤ A₁ * ‖f y‖ ^ max m₁ m₂ :=
      le_mul_pow_of_le hA₁ hz (le_max_left _ _) (hb₁ y (le_trans (le_max_left _ _) hy))
    have h₂ : ‖G y‖ ≤ A₂ * ‖f y‖ ^ max m₁ m₂ :=
      le_mul_pow_of_le hA₂ hz (le_max_right _ _) (hb₂ y (le_trans (le_max_right _ _) hy))
    calc ‖F y + G y‖ ≤ ‖F y‖ + ‖G y‖ := norm_add_le _ _
      _ ≤ A₁ * ‖f y‖ ^ max m₁ m₂ + A₂ * ‖f y‖ ^ max m₁ m₂ := add_le_add h₁ h₂
      _ = (A₁ + A₂) * ‖f y‖ ^ max m₁ m₂ := by ring

/-- The negative of a function of moderate growth is of moderate growth. -/
theorem IsModerate.neg (hF : IsModerate f S F) : IsModerate f S fun y => -F y where
  punct := by
    intro s hs
    obtain ⟨ρ, hρ, C, hC, N, hb⟩ := hF.punct s hs
    exact ⟨ρ, hρ, C, hC, N, fun y hy => by simpa using hb y hy⟩
  infty := by
    obtain ⟨A, R₀, m, hA, hb⟩ := hF.infty
    exact ⟨A, R₀, m, hA, fun y hy => by simpa using hb y hy⟩

/-- A difference of two functions of moderate growth is of moderate growth. -/
theorem IsModerate.sub (hF : IsModerate f S F) (hG : IsModerate f S G) :
    IsModerate f S fun y => F y - G y := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- A product of two functions of moderate growth is of moderate growth. -/
theorem IsModerate.mul (hF : IsModerate f S F) (hG : IsModerate f S G) :
    IsModerate f S fun y => F y * G y where
  punct := by
    intro s hs
    obtain ⟨ρ₁, hρ₁, C₁, hC₁, N₁, hb₁⟩ := hF.punct s hs
    obtain ⟨ρ₂, hρ₂, C₂, hC₂, N₂, hb₂⟩ := hG.punct s hs
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, C₁ * C₂, by positivity, N₁ + N₂, fun y hy => ?_⟩
    have hy₁ : f y ∈ Metric.ball s ρ₁ \ {s} :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    have hy₂ : f y ∈ Metric.ball s ρ₂ \ {s} :=
      ⟨Metric.ball_subset_ball (min_le_right _ _) hy.1, hy.2⟩
    calc ‖F y * G y‖ * ‖f y - s‖ ^ (N₁ + N₂)
        = (‖F y‖ * ‖f y - s‖ ^ N₁) * (‖G y‖ * ‖f y - s‖ ^ N₂) := by
          rw [norm_mul, pow_add]
          ring
      _ ≤ C₁ * C₂ := mul_le_mul (hb₁ y hy₁) (hb₂ y hy₂) (by positivity) hC₁
  infty := by
    obtain ⟨A₁, R₁, m₁, hA₁, hb₁⟩ := hF.infty
    obtain ⟨A₂, R₂, m₂, hA₂, hb₂⟩ := hG.infty
    refine ⟨A₁ * A₂, max R₁ R₂, m₁ + m₂, by positivity, fun y hy => ?_⟩
    calc ‖F y * G y‖ = ‖F y‖ * ‖G y‖ := norm_mul _ _
      _ ≤ (A₁ * ‖f y‖ ^ m₁) * (A₂ * ‖f y‖ ^ m₂) :=
          mul_le_mul (hb₁ y (le_trans (le_max_left _ _) hy))
            (hb₂ y (le_trans (le_max_right _ _) hy)) (norm_nonneg _) (by positivity)
      _ = A₁ * A₂ * ‖f y‖ ^ (m₁ + m₂) := by rw [pow_add]; ring

/-- A polynomial in the base coordinate is of moderate growth: it is bounded near each puncture and
grows like a power of the base coordinate at infinity. -/
theorem isModerate_polynomial (f : Y → ℂ) (S : Finset ℂ) (p : ℂ[X]) :
    IsModerate f S fun y => p.eval (f y) where
  punct := by
    intro s hs
    obtain ⟨C, hC⟩ := (isCompact_closedBall s 1).exists_bound_of_continuousOn
      (show ContinuousOn (fun z : ℂ => p.eval z) (Metric.closedBall s 1) from
        (Polynomial.continuous p).continuousOn)
    refine ⟨1, one_pos, max C 0, le_max_right _ _, 0, fun y hy => ?_⟩
    have hmem : f y ∈ Metric.closedBall s 1 := Metric.ball_subset_closedBall hy.1
    rw [pow_zero, mul_one]
    exact le_trans (hC (f y) hmem) (le_max_left _ _)
  infty := by
    refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k‖, 1, p.natDegree,
      Finset.sum_nonneg fun k _ => norm_nonneg _, fun y hy => ?_⟩
    exact norm_eval_le_of_one_le p hy

end Defs

/-! ### The growth theorems with the bundled hypothesis -/

section Theorems

variable {Y : Type*} [TopologicalSpace Y] {f g F : Y → ℂ} {S : Finset ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **A holomorphic function of moderate growth, times the leading coefficient of its equation, is
integral over the polynomials of the base coordinate.** -/
theorem isIntegralElem_of_moderate (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (hrange : Set.range f = (↑S)ᶜ) (hmod : IsModerate f S g) :
    ∃ d : ℂ[X], d.Monic ∧ (baseEvalHom f).IsIntegralElem (fun y => d.eval (f y) * g y) := by
  obtain ⟨A, R₀, m, hA, hinf⟩ := hmod.infty
  exact isIntegralElem_of_growth (H := H) hf hover htrans hg S hrange hmod.punct hA hinf

omit [Fintype H] [ContinuousConstSMul H Y] in
/-- **An invariant holomorphic function of moderate growth is a quotient of two polynomials in the
base coordinate.** -/
theorem exists_eq_div_of_invariant_of_moderate (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hF : IsHolo f F) (hinv : ∀ (a : H) (y : Y), F (a • y) = F y)
    (hrange : Set.range f = (↑S)ᶜ) (hmod : IsModerate f S F) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ y : Y, q.eval (f y) ≠ 0) ∧
      ∀ y : Y, F y = p.eval (f y) / q.eval (f y) := by
  obtain ⟨A, R₀, m, -, hinf⟩ := hmod.infty
  exact exists_eq_div_of_invariant_of_growth (H := H) hf htrans hF hinv S hrange hmod.punct hinf

omit [Fintype H] [ContinuousConstSMul H Y] in
/-- **An invariant holomorphic function of moderate growth is a regular function on the punctured
plane**: a polynomial in the base coordinate divided by a power of the product of the distances to
the punctures. -/
theorem exists_eq_div_prod_of_invariant_of_moderate (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hF : IsHolo f F) (hinv : ∀ (a : H) (y : Y), F (a • y) = F y)
    (hrange : Set.range f = (↑S)ᶜ) (hmod : IsModerate f S F) :
    ∃ (p : ℂ[X]) (e : ℕ), ∀ y : Y, (∏ s ∈ S, (f y - s)) ^ e * F y = p.eval (f y) := by
  obtain ⟨A, R₀, m, -, hinf⟩ := hmod.infty
  exact exists_eq_div_prod_of_invariant_of_growth (H := H) hf htrans hF hinv S hrange hmod.punct
    hinf

/-- **A holomorphic function of moderate growth is a rational expression in the base coordinate and
in a function of moderate growth separating the sheets.** -/
theorem exists_eq_div_of_separating_of_moderate [DecidableEq H] (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (hF : IsHolo f F) (hrange : Set.range f = (↑S)ᶜ)
    (hsep : ∀ (y : Y) (b : H), b ≠ 1 → g (b • y) ≠ g y)
    (hmodg : IsModerate f S g) (hmodF : IsModerate f S F) :
    ∃ (t : ℕ → ℂ[X]) (q : ℂ[X]), q.Monic ∧
      (∀ y : Y, q.eval (f y) * (derivative (orbitPoly H g y)).eval (g y) ≠ 0) ∧
      ∀ y : Y, F y = (∑ k ∈ Finset.range (Fintype.card H), (t k).eval (f y) * g y ^ k)
        / (q.eval (f y) * (derivative (orbitPoly H g y)).eval (g y)) := by
  obtain ⟨A, R₀, m, hA, hinfg⟩ := hmodg.infty
  obtain ⟨A', R₀', m', hA', hinfF⟩ := hmodF.infty
  refine exists_eq_div_of_separating_of_growth hf hover htrans hg hF S hrange hsep
    hmodg.punct hmodF.punct hA hA' (R₀ := max R₀ R₀')
    (fun y hy => hinfg y (le_trans (le_max_left _ _) hy))
    (fun y hy => hinfF y (le_trans (le_max_right _ _) hy))

end Theorems

end Rigidity.RET

end
