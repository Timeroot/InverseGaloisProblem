/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Interpolation
import InverseGalois.Rigidity.RET.Analytic.RationalGrowth

/-!
# The interpolant of a function of moderate growth has rational coefficients

Interpolation along a fibre writes a holomorphic function `F` on a covering as a polynomial
expression in a second holomorphic function `g`, with coefficients that depend on the base point
alone.  Those coefficients are analytic on the base region, and — this is what is proved here —
they are *rational* as soon as `F` and `g` are of moderate growth at the punctures and at
infinity: each is a sum over the fibre of a value of `F` times coefficients of a monic product of
linear factors in the values of `g`, so the growth of the two functions bounds the growth of the
coefficients.

Clearing the finitely many denominators at once, the interpolation identity becomes an identity
between polynomials in `g` with coefficients polynomial in the base coordinate: the analytic form
of the primitive element theorem.  A denominator that never vanishes over the base region divides
`F`, times the derivative of the orbit polynomial of `g`, into a polynomial expression in `g` of
degree less than the order of the deck group.  Where `g` separates the sheets that derivative is
nonzero, and the identity exhibits `F` as a rational expression in the base coordinate and `g`.

## Main results

* `Rigidity.RET.norm_coeff_interpPoly_le` — the coefficients of the interpolant are bounded in
  terms of bounds on `F` and `g` along the fibre.
* `Rigidity.RET.exists_rational_interpPoly_coeff_of_growth` — each coefficient of the interpolant
  is a quotient of two polynomials in the base coordinate.
* `Rigidity.RET.exists_interp_of_growth` — the interpolation identity with polynomial
  coefficients and a denominator that does not vanish over the base region.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

section Bound

variable {Y : Type*} {g F : Y → ℂ} {H : Type*} [Group H] [Fintype H] [DecidableEq H]
  [MulAction H Y]

/-- **The coefficients of the interpolant are bounded** in terms of bounds on the two functions
along the fibre: each is a sum of `|H|` values of `F` times a coefficient of a monic product of
linear factors in the values of `g`. -/
theorem norm_coeff_interpPoly_le {y : Y} {MF Mg : ℝ} (hMg : 0 ≤ Mg)
    (hFb : ∀ a : H, ‖F (a • y)‖ ≤ MF) (hgb : ∀ a : H, ‖g (a • y)‖ ≤ Mg) (k : ℕ) :
    ‖(interpPoly H g F y).coeff k‖
      ≤ Fintype.card H * (MF * (2 ^ Fintype.card H * max Mg 1 ^ Fintype.card H)) := by
  have hMF : 0 ≤ MF := le_trans (norm_nonneg _) (hFb 1)
  have hterm : ∀ a : H,
      ‖(C (F (a • y)) * ∏ b ∈ Finset.univ.erase a, (X - C (g (b • y)))).coeff k‖
        ≤ MF * (2 ^ Fintype.card H * max Mg 1 ^ Fintype.card H) := by
    intro a
    rw [coeff_C_mul, norm_mul]
    have hcard : (Finset.univ.erase a).card ≤ Fintype.card H :=
      le_trans (Finset.card_erase_le) (le_of_eq (Finset.card_univ))
    have h1 : ‖(∏ b ∈ Finset.univ.erase a, (X - C (g (b • y)))).coeff k‖
        ≤ 2 ^ (Finset.univ.erase a).card * max Mg 1 ^ (Finset.univ.erase a).card :=
      norm_coeff_prod_X_sub_C_le _ _ hMg (fun b _ => hgb b) k
    have h2 : (2 : ℝ) ^ (Finset.univ.erase a).card * max Mg 1 ^ (Finset.univ.erase a).card
        ≤ 2 ^ Fintype.card H * max Mg 1 ^ Fintype.card H :=
      mul_le_mul (pow_le_pow_right₀ one_le_two hcard)
        (pow_le_pow_right₀ (le_max_right _ _) hcard) (by positivity) (by positivity)
    exact mul_le_mul (hFb a) (h1.trans h2) (norm_nonneg _) hMF
  rw [interpPoly, finset_sum_coeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a : H, ‖(C (F (a • y)) * ∏ b ∈ Finset.univ.erase a, (X - C (g (b • y)))).coeff k‖
      ≤ ∑ _a : H, MF * (2 ^ Fintype.card H * max Mg 1 ^ Fintype.card H) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = Fintype.card H * (MF * (2 ^ Fintype.card H * max Mg 1 ^ Fintype.card H)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Bound

section Rational

variable {Y : Type*} [TopologicalSpace Y] {f g F : Y → ℂ}
variable {H : Type*} [Group H] [Fintype H] [DecidableEq H] [MulAction H Y]
  [ContinuousConstSMul H Y]

/-- **The coefficients of the interpolant of a function of moderate growth are rational.**

Moderate growth of `F` and of `g` at a puncture bounds the coefficient by a power of the distance
to it, and polynomial growth of the two at infinity bounds it by a power of `‖z‖`; so the
coefficient is a quotient of two polynomials, whose denominator does not vanish off the
punctures. -/
theorem exists_rational_interpPoly_coeff_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (hF : IsHolo f F) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunctg : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    (hpunctF : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C)
    {A A' R₀ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') {m m' : ℕ}
    (hinfg : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m)
    (hinfF : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A' * ‖f y‖ ^ m') (k : ℕ) :
    ∃ p q : ℂ[X], q.Monic ∧ (∀ z ∉ S, q.eval z ≠ 0) ∧
      ∀ y : Y, q.eval (f y) * (interpPoly H g F y).coeff k = p.eval (f y) := by
  obtain ⟨c₀, hc₀, hac₀⟩ := exists_analytic_interpPoly_coeff hf hover htrans hg hF k
  have hmemrange : ∀ z : ℂ, z ∉ S → ∃ y : Y, f y = z := by
    intro z hz
    have : z ∈ Set.range f := by rw [hrange]; simpa using hz
    exact this
  -- Off the punctures the coefficient is analytic.
  have hana : ∀ z ∉ S, AnalyticAt ℂ c₀ z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hmemrange z hz
    exact hac₀ y
  -- At a puncture the coefficient grows no faster than a power of the distance to it.
  have hpunct : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ (B : ℝ) (N : ℕ),
      ∀ z ∈ Metric.ball s ρ \ {s}, z ∉ S → ‖c₀ z‖ * ‖z - s‖ ^ N ≤ B := by
    intro s hs
    obtain ⟨ρg, hρg, Cg, hCg, Ng, hbg⟩ := hpunctg s hs
    obtain ⟨ρF, hρF, CF, hCF, NF, hbF⟩ := hpunctF s hs
    refine ⟨min 1 (min ρg ρF), lt_min one_pos (lt_min hρg hρF),
      Fintype.card H * (CF * (2 ^ Fintype.card H * max Cg 1 ^ Fintype.card H)),
      NF + Ng * Fintype.card H, ?_⟩
    intro z hz hzS
    obtain ⟨y, rfl⟩ := hmemrange z hzS
    have hzball : ‖f y - s‖ < min 1 (min ρg ρF) := by
      have := hz.1
      rwa [Metric.mem_ball, Complex.dist_eq] at this
    have hne : f y ≠ s := by simpa using hz.2
    have hr : 0 < ‖f y - s‖ := by
      simpa [sub_eq_zero] using hne
    have hr1 : ‖f y - s‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hzball (min_le_left _ _))
    have hmemg : ∀ a : H, f (a • y) ∈ Metric.ball s ρg \ {s} := by
      intro a
      rw [hover a y]
      exact ⟨Metric.ball_subset_ball
        (le_trans (min_le_right _ _) (min_le_left _ _)) hz.1, hz.2⟩
    have hmemF : ∀ a : H, f (a • y) ∈ Metric.ball s ρF \ {s} := by
      intro a
      rw [hover a y]
      exact ⟨Metric.ball_subset_ball
        (le_trans (min_le_right _ _) (min_le_right _ _)) hz.1, hz.2⟩
    -- Bounds along the fibre, obtained by dividing by the power of the distance.
    have hgb : ∀ a : H, ‖g (a • y)‖ ≤ max Cg 1 / ‖f y - s‖ ^ Ng := by
      intro a
      refine (le_div_iff₀ (pow_pos hr Ng)).2 ?_
      have := hbg (a • y) (hmemg a)
      rw [hover a y] at this
      exact this.trans (le_max_left _ _)
    have hFb : ∀ a : H, ‖F (a • y)‖ ≤ CF / ‖f y - s‖ ^ NF := by
      intro a
      refine (le_div_iff₀ (pow_pos hr NF)).2 ?_
      have := hbF (a • y) (hmemF a)
      rwa [hover a y] at this
    have hrpow : ‖f y - s‖ ^ Ng ≤ 1 := by
      simpa using pow_le_pow_left₀ hr.le hr1 Ng
    have hMg1 : (1 : ℝ) ≤ max Cg 1 / ‖f y - s‖ ^ Ng :=
      (le_div_iff₀ (pow_pos hr Ng)).2 (by rw [one_mul]; exact hrpow.trans (le_max_right _ _))
    have hMg0 : (0 : ℝ) ≤ max Cg 1 / ‖f y - s‖ ^ Ng := le_trans zero_le_one hMg1
    have hb := norm_coeff_interpPoly_le (H := H) (F := F) hMg0 hFb hgb k
    rw [max_eq_left hMg1] at hb
    rw [← hc₀ y]
    refine (mul_le_mul_of_nonneg_right hb (pow_nonneg hr.le _)).trans (le_of_eq ?_)
    have hsplit : ‖f y - s‖ ^ (NF + Ng * Fintype.card H)
        = ‖f y - s‖ ^ NF * (‖f y - s‖ ^ Ng) ^ Fintype.card H := by
      rw [pow_add, pow_mul]
    have hu : ‖f y - s‖ ^ NF ≠ 0 := ne_of_gt (pow_pos hr NF)
    have hv : (‖f y - s‖ ^ Ng) ^ Fintype.card H ≠ 0 := ne_of_gt (pow_pos (pow_pos hr Ng) _)
    rw [hsplit, div_pow]
    field_simp
  -- At infinity the coefficient grows no faster than a power of `‖z‖`.
  have hinf : ∀ z : ℂ, max R₀ 1 ≤ ‖z‖ → z ∉ S →
      ‖c₀ z‖ ≤ (Fintype.card H * A' * 2 ^ Fintype.card H * max A 1 ^ Fintype.card H)
        * ‖z‖ ^ (m' + m * Fintype.card H) := by
    intro z hz hzS
    obtain ⟨y, rfl⟩ := hmemrange z hzS
    have hz1 : (1 : ℝ) ≤ ‖f y‖ := le_trans (le_max_right _ _) hz
    have hzR : R₀ ≤ ‖f y‖ := le_trans (le_max_left _ _) hz
    have hgb : ∀ a : H, ‖g (a • y)‖ ≤ A * ‖f y‖ ^ m := by
      intro a
      have := hinfg (a • y) (by rw [hover a y]; exact hzR)
      rwa [hover a y] at this
    have hFb : ∀ a : H, ‖F (a • y)‖ ≤ A' * ‖f y‖ ^ m' := by
      intro a
      have := hinfF (a • y) (by rw [hover a y]; exact hzR)
      rwa [hover a y] at this
    have hMg0 : (0 : ℝ) ≤ A * ‖f y‖ ^ m := by positivity
    have hb := norm_coeff_interpPoly_le (H := H) (F := F) hMg0 hFb hgb k
    have hzm : (1 : ℝ) ≤ ‖f y‖ ^ m := by
      simpa using pow_le_pow_left₀ zero_le_one hz1 m
    have hstep : max (A * ‖f y‖ ^ m) 1 ≤ max A 1 * ‖f y‖ ^ m := by
      refine max_le ?_ ?_
      · exact mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
      · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ max A 1 * ‖f y‖ ^ m :=
            mul_le_mul (le_max_right A 1) hzm zero_le_one (le_trans zero_le_one (le_max_right A 1))
    rw [← hc₀ y]
    refine hb.trans ?_
    have hpowle : max (A * ‖f y‖ ^ m) 1 ^ Fintype.card H
        ≤ (max A 1 * ‖f y‖ ^ m) ^ Fintype.card H :=
      pow_le_pow_left₀ (le_max_of_le_right zero_le_one) hstep _
    calc (Fintype.card H : ℝ) *
          (A' * ‖f y‖ ^ m' * (2 ^ Fintype.card H * max (A * ‖f y‖ ^ m) 1 ^ Fintype.card H))
        ≤ (Fintype.card H : ℝ) *
          (A' * ‖f y‖ ^ m' * (2 ^ Fintype.card H * (max A 1 * ‖f y‖ ^ m) ^ Fintype.card H)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpowle (by positivity)) (by positivity)) (by positivity)
      _ = (Fintype.card H * A' * 2 ^ Fintype.card H * max A 1 ^ Fintype.card H)
            * ‖f y‖ ^ (m' + m * Fintype.card H) := by
          rw [mul_pow, pow_add, pow_mul]
          ring
  obtain ⟨p, q, hqm, hqne, hpq⟩ := exists_rational_of_growth S hana hpunct hinf
  exact ⟨p, q, hqm, hqne, fun y => by rw [hc₀ y]; exact hpq (f y)⟩

/-- **The interpolation identity with polynomial coefficients.**

Clearing the denominators of the finitely many coefficients at once, the value of `F` times the
derivative of the orbit polynomial of `g` becomes, after multiplication by a fixed polynomial in
the base coordinate that does not vanish over the base region, a polynomial expression in `g` of
degree less than the order of the deck group with coefficients polynomial in the base
coordinate. -/
theorem exists_interp_of_growth (hf : IsLocalHomeomorph f)
    (hover : ∀ (a : H) (y : Y), f (a • y) = f y)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ b : H, y' = b • y)
    (hg : IsHolo f g) (hF : IsHolo f F) (S : Finset ℂ) (hrange : Set.range f = (↑S)ᶜ)
    (hpunctg : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖g y‖ * ‖f y - s‖ ^ N ≤ C)
    (hpunctF : ∀ s ∈ S, ∃ ρ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ N : ℕ,
      ∀ y : Y, f y ∈ Metric.ball s ρ \ {s} → ‖F y‖ * ‖f y - s‖ ^ N ≤ C)
    {A A' R₀ : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') {m m' : ℕ}
    (hinfg : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖g y‖ ≤ A * ‖f y‖ ^ m)
    (hinfF : ∀ y : Y, R₀ ≤ ‖f y‖ → ‖F y‖ ≤ A' * ‖f y‖ ^ m') :
    ∃ (t : ℕ → ℂ[X]) (q : ℂ[X]), q.Monic ∧ (∀ y : Y, q.eval (f y) ≠ 0) ∧
      ∀ y : Y, q.eval (f y) * (F y * (derivative (orbitPoly H g y)).eval (g y))
        = ∑ k ∈ Finset.range (Fintype.card H), (t k).eval (f y) * g y ^ k := by
  choose p q hqm hqne hpq using fun k =>
    exists_rational_interpPoly_coeff_of_growth hf hover htrans hg hF S hrange hpunctg hpunctF
      hA hA' hinfg hinfF k
  have hnotS : ∀ y : Y, f y ∉ S := by
    intro y
    have hmem : f y ∈ (↑S : Set ℂ)ᶜ := hrange ▸ Set.mem_range_self y
    simpa using hmem
  refine ⟨fun k => (∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j) * p k,
    ∏ k ∈ Finset.range (Fintype.card H), q k,
    monic_prod_of_monic _ _ fun k _ => hqm k, fun y => ?_, fun y => ?_⟩
  · rw [eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hqne k (f y) (hnotS y)
  · have hexp : F y * (derivative (orbitPoly H g y)).eval (g y)
        = ∑ k ∈ Finset.range (Fintype.card H), (interpPoly H g F y).coeff k * g y ^ k := by
      rw [← eval_interpPoly_eq_mul, eval_eq_sum_range' (natDegree_interpPoly_lt y)]
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (∏ j ∈ Finset.range (Fintype.card H), q j)
        = q k * ∏ j ∈ (Finset.range (Fintype.card H)).erase k, q j :=
      (Finset.mul_prod_erase _ _ hk).symm
    rw [hd, eval_mul, eval_mul, ← hpq k y]
    ring

end Rational

end Rigidity.RET

end
