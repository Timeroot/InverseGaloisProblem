/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.PunctureMeromorphic
import InverseGalois.Rigidity.RET.Analytic.Rational

/-!
# A function of moderate growth on a covering of a punctured plane is algebraic

A holomorphic function on a covering of the plane minus a finite set satisfies a monic equation of
degree the order of the deck group whose coefficients are analytic functions on that region.  Two
growth conditions make those coefficients rational: moderate growth at each puncture makes them
meromorphic there, and moderate growth at infinity makes them of polynomial growth, and a function
analytic off a finite set, meromorphic on it and of polynomial growth is a quotient of polynomials.

Clearing the denominators turns the monic equation with rational coefficients into an equation with
*polynomial* coefficients and a nonzero leading one: the function is algebraic over the rational
functions of the base.  This is the passage from a covering to an algebraic curve.

## Main results

* `Rigidity.RET.exists_algebraic_of_growth` — a holomorphic function of moderate growth at the
  punctures and at infinity satisfies a polynomial equation over the polynomials of the base, with
  monic leading coefficient in the base variable.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Algebraic

variable {Y : Type*} [TopologicalSpace Y] {f g : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]

/-- **The coefficients of the equation satisfied by a function of moderate growth are rational.**

Away from the punctures the coefficient is analytic, at a puncture it is meromorphic because the
function grows no faster than a power of the distance to it, and at infinity it grows no faster
than a power of `‖z‖`; so it is a quotient of two polynomials, the denominator vanishing only at
the punctures. -/
theorem exists_rational_orbitPoly_coeff_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m)
    (k : ℕ) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ z ∉ S, q.eval z ≠ 0) ∧
      ∀ y : Y, q.eval (f y) * (orbitPoly H g y).coeff k = p.eval (f y) := by
  obtain ⟨c₀, hc₀, hac₀⟩ := exists_analytic_orbitPoly_coeff hf hover htrans hg k
  -- Off the punctures the coefficient is analytic.
  have hmemrange : ∀ z : ℂ, z ∉ S → ∃ y : Y, f y = z := by
    intro z hz
    have : z ∈ Set.range f := by rw [hrange]; simpa using hz
    exact this
  have hana : ∀ z ∉ S, AnalyticAt ℂ c₀ z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hmemrange z hz
    exact hac₀ y
  -- At a puncture the coefficient is meromorphic.
  have hmero : ∀ s ∈ S, MeromorphicAt c₀ s := by
    intro s hs
    obtain ⟨ρ, hρ, C, hC, N, hbdd⟩ := hpunct s hs
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 (S.erase s).finite_toSet.isClosed.isOpen_compl s
      (by simp)
    have hρ' : 0 < min ρ ρ₀ := lt_min hρ hρ₀
    have hsub : Metric.ball s (min ρ ρ₀) \ {s} ⊆ Metric.ball s ρ \ {s} := by
      intro z hz
      exact ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
    have hnotS : ∀ z ∈ Metric.ball s (min ρ ρ₀) \ ({s} : Set ℂ), z ∉ S := by
      intro z hz hzS
      have h1 : z ∉ (S.erase s : Set ℂ) :=
        hball (Metric.ball_subset_ball (min_le_right _ _) hz.1)
      refine h1 ?_
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hzS, by simpa using hz.2⟩
    have hsurj : Metric.ball s (min ρ ρ₀) \ {s} ⊆ Set.range f := by
      intro z hz
      rw [hrange]
      exact hnotS z hz
    obtain ⟨c, hac, hmc, hcy⟩ := exists_meromorphicAt_coeff_of_growth hf hover htrans hg hρ' hsurj
      hC (fun y hy => hbdd y (hsub hy)) k
    refine hmc.congr ?_
    have hev : ∀ᶠ z in nhdsWithin s {s}ᶜ, z ∈ Metric.ball s (min ρ ρ₀) \ {s} := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds s hρ')] with z h1 h2
      exact ⟨h2, h1⟩
    filter_upwards [hev] with z hz
    obtain ⟨y, rfl⟩ := hsurj hz
    rw [← hcy y, hc₀ y]
  -- At infinity the coefficient grows no faster than a power of `‖z‖`.
  obtain ⟨B, hB⟩ := (S.image fun s : ℂ => ‖s‖).exists_le
  have hgrowth : ∀ z : ℂ, max (max R₀ 1) (B + 1) ≤ ‖z‖ →
      ‖c₀ z‖ ≤ (2 ^ Fintype.card H * max A 1 ^ Fintype.card H) * ‖z‖ ^ (m * Fintype.card H) := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_trans (le_max_right R₀ 1) (le_max_left _ _)) hz
    have hzR : R₀ ≤ ‖z‖ := le_trans (le_trans (le_max_left R₀ 1) (le_max_left _ _)) hz
    have hzS : z ∉ S := by
      intro hzS
      have h1 : ‖z‖ ≤ B := hB _ (Finset.mem_image_of_mem (fun s : ℂ => ‖s‖) hzS)
      have h2 : B + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      linarith
    obtain ⟨y, rfl⟩ := hmemrange z hzS
    have hM : 0 ≤ A * ‖f y‖ ^ m := by positivity
    have hb : ∀ a : H, ‖g (a • y)‖ ≤ A * ‖f y‖ ^ m := by
      intro a
      have := hinf (a • y) (by rw [hover a y]; exact hzR)
      rwa [hover a y] at this
    refine le_trans (le_of_eq (congrArg norm (hc₀ y).symm))
      ((norm_coeff_orbitPoly_le (H := H) hM hb k).trans ?_)
    have hzm : (1 : ℝ) ≤ ‖f y‖ ^ m := by
      simpa using pow_le_pow_left₀ zero_le_one hz1 m
    have hstep : max (A * ‖f y‖ ^ m) 1 ≤ max A 1 * ‖f y‖ ^ m := by
      refine max_le ?_ ?_
      · exact mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
      · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ max A 1 * ‖f y‖ ^ m :=
            mul_le_mul (le_max_right A 1) hzm zero_le_one (le_trans zero_le_one (le_max_right A 1))
    calc 2 ^ Fintype.card H * max (A * ‖f y‖ ^ m) 1 ^ Fintype.card H
        ≤ 2 ^ Fintype.card H * (max A 1 * ‖f y‖ ^ m) ^ Fintype.card H :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hstep _) (by positivity)
      _ = 2 ^ Fintype.card H * max A 1 ^ Fintype.card H * ‖f y‖ ^ (m * Fintype.card H) := by
          rw [mul_pow, pow_mul]
          ring
  obtain ⟨p, q, hqm, hqne, hpq⟩ :=
    exists_rational_of_meromorphic_of_growth S hana hmero hgrowth
  exact ⟨p, q, hqm, hqne, fun y => by rw [hc₀ y]; exact hpq (f y)⟩

/-- **A holomorphic function of moderate growth on a covering of a punctured plane is algebraic
over the base.**

It satisfies an equation of degree the order of the deck group whose coefficients are polynomials
in the base coordinate and whose leading coefficient is a monic polynomial in it, vanishing only at
the punctures. -/
theorem exists_algebraic_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ (a : ℕ → ℂ[X]) (d : ℂ[X]), d.Monic ∧ (∀ z ∉ S, d.eval z ≠ 0) ∧
      ∀ y : Y, d.eval (f y) * g y ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H), (a k).eval (f y) * g y ^ k = 0 := by
  choose p q hqm hqne hpq using fun k =>
    exists_rational_orbitPoly_coeff_of_growth hf hover htrans hg S hrange hpunct hA hinf k
  refine ⟨fun k => (∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j) * p k,
    ∏ k ∈ Finset.range (Fintype.card H), q k, monic_prod_of_monic _ _ fun k _ => hqm k,
    fun z hz => by
      rw [eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hqne k z hz, fun y => ?_⟩
  have hzero : g y ^ Fintype.card H
      + ∑ k ∈ Finset.range (Fintype.card H), (orbitPoly H g y).coeff k * g y ^ k = 0 := by
    have h := eval_orbitPoly_self (H := H) (g := g) y
    rw [orbitPoly_eq_add_sum y] at h
    simpa [eval_finset_sum] using h
  have hstep : ∀ k ∈ Finset.range (Fintype.card H),
      ((∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j) * p k).eval (f y)
        = (∏ k ∈ Finset.range (Fintype.card H), q k).eval (f y) * (orbitPoly H g y).coeff k := by
    intro k hk
    have hd : (∏ k ∈ Finset.range (Fintype.card H), q k)
        = q k * ∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j :=
      (Finset.mul_prod_erase _ _ hk).symm
    rw [hd, eval_mul, eval_mul, mul_assoc, ← hpq k y]
    ring
  calc (∏ k ∈ Finset.range (Fintype.card H), q k).eval (f y) * g y ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H),
            ((∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j) * p k).eval (f y) * g y ^ k
      = (∏ k ∈ Finset.range (Fintype.card H), q k).eval (f y) *
          (g y ^ Fintype.card H
            + ∑ k ∈ Finset.range (Fintype.card H), (orbitPoly H g y).coeff k * g y ^ k) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hstep k hk]
        ring
    _ = 0 := by rw [hzero, mul_zero]

/-- **A holomorphic function of moderate growth becomes integral over the base after clearing the
denominator.**

Multiplying the equation of `g` by the `(|H| - 1)`-st power of its leading coefficient turns it
into a *monic* equation for `d · g`, with coefficients polynomials in the base coordinate; the
clearing factor `d` vanishes only at the punctures. -/
theorem exists_integral_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    {A R₀ : ℝ} (hA : 0 ≤ A) {m : ℕ} (hinf : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m) :
    ∃ (b : ℕ → ℂ[X]) (d : ℂ[X]), d.Monic ∧ (∀ z ∉ S, d.eval z ≠ 0) ∧
      ∀ y : Y, (d.eval (f y) * g y) ^ Fintype.card H
        + ∑ k ∈ Finset.range (Fintype.card H),
            (b k).eval (f y) * (d.eval (f y) * g y) ^ k = 0 := by
  obtain ⟨a, d, hd, hdne, heq⟩ :=
    exists_algebraic_of_growth hf hover htrans hg S hrange hpunct hA hinf
  have hn : 1 ≤ Fintype.card H := Fintype.card_pos
  refine ⟨fun k => a k * d ^ (Fintype.card H - 1 - k), d, hd, hdne, fun y => ?_⟩
  have hpow1 : d.eval (f y) ^ (Fintype.card H - 1) * d.eval (f y)
      = d.eval (f y) ^ Fintype.card H := by
    rw [← pow_succ]
    congr 1
    omega
  have key : (d.eval (f y) * g y) ^ Fintype.card H
      + ∑ k ∈ Finset.range (Fintype.card H),
          (a k * d ^ (Fintype.card H - 1 - k)).eval (f y) * (d.eval (f y) * g y) ^ k
      = d.eval (f y) ^ (Fintype.card H - 1) *
        (d.eval (f y) * g y ^ Fintype.card H
          + ∑ k ∈ Finset.range (Fintype.card H), (a k).eval (f y) * g y ^ k) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · rw [mul_pow, ← hpow1]
      ring
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < Fintype.card H := Finset.mem_range.1 hk
      have hpow : d.eval (f y) ^ (Fintype.card H - 1 - k) * d.eval (f y) ^ k
          = d.eval (f y) ^ (Fintype.card H - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [eval_mul, eval_pow, mul_pow, ← hpow]
      ring
  rw [key, heq y, mul_zero]

end Algebraic

end Rigidity.RET

end
