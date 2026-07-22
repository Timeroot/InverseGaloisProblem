/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Polynomial.GaloisGroupTools

/-!
# A₄ is an Inverse Galois Group

We show that `A₄ = alternatingGroup (Fin 4)` (alternating group of order 12) is an inverse
Galois group over `ℚ`, using the polynomial `X⁴ + 8X + 12`.

## Strategy

1. `X⁴ + 8X + 12` is irreducible over `ℚ`
2. The resolvent cubic `Y³ - 48Y - 64` is irreducible over `ℚ`
3. 12 | |Gal| (from 4 | and 3 |)
4. |Gal| | 24 (from embedding into S₄)
5. The discriminant = 576² is a perfect square, implying Gal ⊆ A₄,
   so |Gal| ≤ 12
6. Therefore |Gal| = 12, and Gal ≅ A₄ (as subgroup of S₄)
-/

open Polynomial IntermediateField

noncomputable section

/-- The polynomial `X⁴ + 8X + 12` over `ℚ`. -/
private def a₄ : ℚ[X] := X ^ 4 + C 8 * X + C 12

/-
`X⁴ + 8X + 12` is irreducible over `ℚ`.
-/
private lemma a₄_irreducible : Irreducible a₄ := by
  -- By contradiction, assume `a₄` is reducible.
  by_contra h_not_irreducible
  obtain ⟨f, g, hf_deg, hg_deg, hfg⟩ : ∃ f g : Polynomial ℚ, f.degree = 2 ∧ g.degree = 2 ∧ f * g = a₄ := by
    have h_factor :
        ∃ f g : Polynomial ℚ, f.degree = 1 ∧ g.degree = 3 ∧ f * g = a₄ ∨ f.degree = 2 ∧ g.degree = 2 ∧ f * g = a₄ := by
      obtain ⟨f, g, hf_deg, hg_deg, hfg⟩ : ∃ f g : Polynomial ℚ, f.degree > 0 ∧ g.degree > 0 ∧ f * g = a₄ := by
        contrapose! h_not_irreducible
        constructor <;> contrapose! h_not_irreducible <;> simp_all [a₄]
        · refine absurd (Polynomial.degree_eq_zero_of_isUnit h_not_irreducible) ?_
          erw [Polynomial.degree_add_C] <;> erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num
        · obtain ⟨a, b, h₁, h₂, h₃⟩ := h_not_irreducible
          refine ⟨a,
            not_le.mp fun h ↦ h₂ <|
              Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' ↦ ?_,
            b,
            not_le.mp fun h ↦ h₃ <|
              Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' ↦ ?_,
            h₁.symm⟩
          · apply_fun Polynomial.eval 0 at h₁
            aesop
          · apply_fun Polynomial.eval 0 at h₁
            aesop
      have h_deg_sum : f.degree + g.degree = 4 := by
        erw [← Polynomial.degree_mul, hfg, Polynomial.degree_add_C] <;>
          erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num
      have h_deg_cases : f.degree = 1 ∧ g.degree = 3 ∨ f.degree = 3 ∧ g.degree = 1 ∨ f.degree = 2 ∧ g.degree = 2 := by
        rw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hf_deg),
          Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hg_deg)] at *
        norm_cast at *
        omega
      rcases h_deg_cases with (⟨hf, hg⟩ | ⟨hf, hg⟩ | ⟨hf, hg⟩)
      · exact ⟨f, g, Or.inl ⟨hf, hg, hfg⟩⟩
      · exact ⟨g, f, Or.inl ⟨hg, hf, by rw [mul_comm, hfg]⟩⟩
      · exact ⟨f, g, Or.inr ⟨hf, hg, hfg⟩⟩
    obtain ⟨f, g, h | h⟩ := h_factor <;> simp_all
    · -- If `f` is a linear polynomial, then `f` must have a rational root.
      obtain ⟨r, hr⟩ : ∃ r : ℚ, f.eval r = 0 := Polynomial.exists_root_of_degree_eq_one h.1
      replace h := congr_arg (Polynomial.eval r) h.2.2
      norm_num [hr, a₄] at h
      nlinarith [sq_nonneg (r^2 - 2), sq_nonneg (r + 2)]
    · exact ⟨f, h.1, g, h.2.1, h.2.2⟩
  -- Comparing coefficients, we get the following system of equations:
  -- `b + d - a^2 = 0`, `a(d - b) = 8`, and `bd = 12`.
  have h_coeff : ∃ a b d : ℚ, b + d - a^2 = 0 ∧ a * (d - b) = 8 ∧ b * d = 12 := by
    -- Let's assume that `f` and `g` are quadratic polynomials with rational coefficients.
    obtain ⟨a, b, c, d, e, f', ha⟩ :
        ∃ a b c d e f' : ℚ, f = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c ∧
          g = Polynomial.C d * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C f' := by
      rw [@Polynomial.as_sum_range_C_mul_X_pow ℚ _ f, @Polynomial.as_sum_range_C_mul_X_pow ℚ _ g]
      refine ⟨f.coeff 2, f.coeff 1, f.coeff 0, g.coeff 2, g.coeff 1, g.coeff 0, ?_, ?_⟩
      · simp [Polynomial.natDegree_eq_of_degree_eq_some hf_deg, Finset.sum_range_succ']
      · simp [Polynomial.natDegree_eq_of_degree_eq_some hg_deg, Finset.sum_range_succ']
    -- By comparing coefficients, we get the following system of equations:
    -- `a * d = 1`, `a * e + b * d = 0`, `a * f' + b * e + c * d = 0`, `b * f' + c * e = 8`, `c * f' = 12`.
    have h_sys : a * d = 1 ∧ a * e + b * d = 0 ∧ a * f' + b * e + c * d = 0 ∧ b * f' + c * e = 8 ∧ c * f' = 12 := by
      simp_all [a₄]
      have h₁ := congr_arg (Polynomial.eval (-2)) hfg
      have h₂ := congr_arg (Polynomial.eval (-1)) hfg
      have h₃ := congr_arg (Polynomial.eval 0) hfg
      have h₄ := congr_arg (Polynomial.eval 1) hfg
      have h₅ := congr_arg (Polynomial.eval 2) hfg
      norm_num at h₁ h₂ h₃ h₄ h₅
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
    use b / a, c / a, f' / d
    grind
  obtain ⟨a, b, d, h₁, h₂, h₃⟩ := h_coeff
  have h₄ : a^6 - 48 * a^2 - 64 = 0 := by
    grind
  -- Let `y = a^2`. Then we have the equation `y^3 - 48y - 64 = 0`.
  set y : ℚ := a^2
  have hy : y^3 - 48 * y - 64 = 0 := by
    linear_combination' h₄
  -- By the Rational Root Theorem, the possible rational roots of `y^3 - 48y - 64 = 0` are the divisors of 64.
  have h_rational_roots :
      ∀ y : ℚ, y^3 - 48 * y - 64 = 0 →
        y = 1 ∨ y = -1 ∨ y = 2 ∨ y = -2 ∨ y = 4 ∨ y = -4 ∨ y = 8 ∨ y = -8 ∨
          y = 16 ∨ y = -16 ∨ y = 32 ∨ y = -32 ∨ y = 64 ∨ y = -64 := by
    intros y hy
    have h_div : y.den ∣ 1 := by
      have h_eq : y.num ^ 3 - 48 * y.num * y.den ^ 2 - 64 * y.den ^ 3 = 0 := by
        rw [← Rat.num_div_den y] at hy
        simp_all [pow_succ, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
        field_simp at hy
        norm_cast at hy
        simp_all [sub_eq_iff_eq_add]
        linarith
      have h_dvd : (y.den : ℤ) ∣ y.num ^ 3 := ⟨48 * y.num * y.den + 64 * y.den ^ 2, by linarith⟩
      have := Int.dvd_coe_gcd h_dvd (dvd_refl _)
      simp_all [Int.gcd, Int.natAbs_pow]
      simp_all [Nat.Coprime, Nat.Coprime.gcd_eq_one, Rat.reduced]
      exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp this)
    -- Since `y` is rational and `y.den ∣ 1`, `y` must be an integer.
    have h_int : ∃ k : ℤ, y = k :=
      ⟨y.num, by simpa [show y.den = 1 by simpa using Nat.eq_one_of_dvd_one h_div] using y.num_div_den.symm⟩
    rcases h_int with ⟨k, rfl⟩
    norm_cast at hy ⊢
    have : k ≤ 8 := Int.le_of_lt_add_one (by nlinarith [sq_nonneg (k^2)])
    have : k ≥ -8 := Int.le_of_lt_add_one (by nlinarith [sq_nonneg (k^2)])
    interval_cases k <;> trivial
  rcases h_rational_roots y hy with (h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [h] at hy

/-
The natural degree of X⁴ + 8X + 12 is 4.
-/
private lemma a₄_natDegree : a₄.natDegree = 4 := by
  erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num

/-
The resolvent cubic `X³ - 48X - 64` is irreducible over `ℚ`.
-/
private lemma resolvent_a4_irreducible :
    Irreducible (X ^ 3 - C 48 * X - C 64 : ℚ[X]) := by
      -- We'll use that `X^3 - 48X - 64` has no rational roots.
      have h_no_roots : ¬∃ r : ℚ,
          Polynomial.eval r (Polynomial.X ^ 3 - Polynomial.C (48 : ℚ) * Polynomial.X - Polynomial.C (64 : ℚ)) = 0 := by
        -- By the Rational Root Theorem, any rational root of `X^3 - 48X - 64` must be a divisor of `-64`.
        have h_rational_roots : ∀ r : ℚ, r^3 - 48 * r - 64 = 0 → False := by
          -- Assume there exists a rational root `r = p/q` with `gcd(p, q) = 1`.
          intro r hr
          obtain ⟨p, q, h_gcd, h_root⟩ :
              ∃ p q : ℤ, Int.gcd p q = 1 ∧ r = p / q ∧ p^3 - 48 * p * q^2 - 64 * q^3 = 0 := by
            obtain ⟨p, q, h_gcd, h_root⟩ : ∃ p q : ℤ, Int.gcd p q = 1 ∧ r = p / q :=
              ⟨r.num, r.den, r.reduced, r.num_div_den.symm⟩
            by_cases hq : q = 0 <;> simp_all [pow_succ', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv]
            field_simp at hr
            refine ⟨p, q, h_gcd, rfl, ?_⟩
            norm_cast at hr
            linarith
          -- This implies that `p` divides `64` and `q` divides `1`, so `p = ±1, ±2, ±4, ±8, ±16, ±32, ±64` and `q = ±1`.
          have hp64 : p ∣ 64 * q ^ 3 := ⟨p ^ 2 - 48 * q ^ 2, by linarith⟩
          have hqp3 : q ∣ p ^ 3 := ⟨48 * p * q + 64 * q ^ 2, by linarith⟩
          have h_divisors : p ∣ 64 ∧ q ∣ 1 := by
            refine ⟨?_, ?_⟩
            · exact Int.dvd_of_dvd_mul_left_of_gcd_one hp64 <| by simpa [Int.gcd, Int.natAbs_pow] using h_gcd
            · refine Int.dvd_of_dvd_mul_right_of_gcd_one (show q ∣ p ^ 3 * 1 by simpa using hqp3) ?_
              simpa [Int.gcd, Int.natAbs_pow] using Nat.Coprime.symm h_gcd
          have : p ≤ 64 := Int.le_of_dvd (by decide) h_divisors.1
          have : p ≥ -64 := neg_le_of_abs_le (Int.le_of_dvd (by decide) (by simpa using h_divisors.1))
          have : q ≤ 1 := Int.le_of_dvd (by decide) h_divisors.2
          have : q ≥ -1 := neg_le_of_abs_le (Int.le_of_dvd (by decide) (by simpa using h_divisors.2))
          interval_cases p <;> norm_num at h_divisors <;> interval_cases q <;> norm_num at h_root
        aesop
      -- Since `X^3 - 48X - 64` has no rational roots, it is irreducible over `ℚ`.
      have h_irred : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 →
          Polynomial.degree p + Polynomial.degree q = 3 →
            p * q = Polynomial.X ^ 3 - Polynomial.C (48 : ℚ) * Polynomial.X - Polynomial.C (64 : ℚ) → False := by
        intros p q hp hq hdeg hprod
        have h_deg_p : p.degree = 1 ∨ q.degree = 1 := by
          erw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hp),
            Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)] at *
          norm_cast at *
          omega
        rcases h_deg_p with (h | h) <;>
          obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one h <;>
          replace hprod := congr_arg (Polynomial.eval r) hprod <;>
          simp_all
        all_goals tauto
      constructor <;> contrapose! h_irred
      · refine absurd (Polynomial.degree_eq_zero_of_isUnit h_irred) ?_
        erw [Polynomial.degree_sub_C] <;> erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
      · obtain ⟨a, b, h₁, h₂, h₃⟩ := h_irred
        refine ⟨a, b,
          not_le.mp fun h ↦ h₂ <|
            Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' ↦ ?_,
          not_le.mp fun h ↦ h₃ <|
            Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' ↦ ?_,
          ?_, h₁.symm, trivial⟩
        · apply_fun Polynomial.eval 0 at h₁
          aesop
        · apply_fun Polynomial.eval 0 at h₁
          aesop
        · erw [← Polynomial.degree_mul, ← h₁]
          erw [Polynomial.degree_sub_C] <;> erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num

/-
12 divides the order of the Galois group of a₄.
-/
private lemma twelve_dvd_card_gal_a4 : 12 ∣ Nat.card a₄.Gal := by
  -- From 4 | |Gal| and 3 | |Gal|, we get 12 | |Gal|.
  have h4 : 4 ∣ Nat.card (a₄.Gal) := a₄_natDegree ▸ natDegree_dvd_card a₄_irreducible
  have h3 : 3 ∣ Nat.card (a₄.Gal) := by
    -- The resolvent cubic `Y^3 - 48Y - 64` has a root in the splitting field of `a₄`.
    obtain ⟨y, hy⟩ : ∃ y : a₄.SplittingField, y^3 - 48 * y - 64 = 0 := by
      -- Let `α` be a root of `a₄` in its splitting field.
      obtain ⟨α, hα⟩ : ∃ α : a₄.SplittingField, a₄.eval₂ (algebraMap ℚ (a₄.SplittingField)) α = 0 := by
        simp only [Polynomial.eval₂_eq_eval_map]
        refine Polynomial.Splits.exists_eval_eq_zero (Polynomial.SplittingField.splits _) ?_
        erw [Polynomial.degree_map, Polynomial.degree_add_C] <;>
          erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num
      -- Let `β` be another root of `a₄` in its splitting field.
      obtain ⟨β, hβ⟩ : ∃ β : a₄.SplittingField, a₄.eval₂ (algebraMap ℚ (a₄.SplittingField)) β = 0 ∧ β ≠ α := by
        by_contra h_no_other
        -- If there are no other roots, then the polynomial `a₄` would be `(X - α)^4`, which contradicts the fact that `a₄` is irreducible.
        have h_contra : a₄.map (algebraMap ℚ a₄.SplittingField) = (Polynomial.X - Polynomial.C α) ^ 4 := by
          have h_prod : a₄.map (algebraMap ℚ a₄.SplittingField) =
              Polynomial.C 1 * Multiset.prod (Multiset.map (fun β ↦ Polynomial.X - Polynomial.C β)
                (Polynomial.roots (a₄.map (algebraMap ℚ a₄.SplittingField)))) := by
            convert Polynomial.Splits.eq_prod_roots _
            · unfold a₄
              norm_num [Polynomial.leadingCoeff, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
            · exact Polynomial.SplittingField.splits _
          rw [h_prod]
          rw [show Polynomial.roots (Polynomial.map (algebraMap ℚ a₄.SplittingField) a₄) =
            Multiset.replicate 4 α from ?_]
          · norm_num
            ring
          · refine Multiset.eq_replicate.mpr ⟨?_, ?_⟩
            · replace h_prod := congr_arg Polynomial.natDegree h_prod
              norm_num [Polynomial.natDegree_map] at h_prod ⊢
              exact h_prod ▸ a₄_natDegree
            · exact fun x hx ↦ Classical.not_not.1 fun hx' ↦
                h_no_other
                  ⟨x, by simpa [Polynomial.eval₂_eq_eval_map] using Polynomial.isRoot_of_mem_roots hx, hx'⟩
        replace h_contra := congr_arg (fun p ↦ Polynomial.coeff p 3) h_contra
        simp_all
        norm_num [a₄, Polynomial.coeff_X, Polynomial.coeff_C, sub_mul, pow_succ'] at h_contra
        norm_num [show α = 0 by linear_combination' h_contra / 4] at hα
        refine absurd hα ?_
        erw [show a₄ = Polynomial.X ^ 4 + Polynomial.C 8 * Polynomial.X + Polynomial.C 12 by rfl]
        norm_num [Polynomial.coeff_zero_eq_eval_zero]
      use (α + β)^2
      unfold a₄ at *
      norm_num at *
      grind
    -- Since `y` is a root of the resolvent cubic, the minimal polynomial of `y` over `ℚ` has degree 3.
    have h_minpoly_y : (minpoly ℚ y).degree = 3 := by
      have h_minpoly_eq : minpoly ℚ y = Polynomial.X ^ 3 - 48 * Polynomial.X - 64 := by
        refine Eq.symm (minpoly.eq_of_irreducible_of_monic resolvent_a4_irreducible ?_ ?_)
        · simpa [Polynomial.aeval_def] using hy
        · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
            Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
          norm_num [Polynomial.coeff_X]
      erw [h_minpoly_eq, Polynomial.degree_sub_C] <;> erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
      all_goals erw [Polynomial.degree_C] <;> norm_num
    -- Since `y` is a root of the resolvent cubic, the degree of the extension `ℚ(y)` over `ℚ` is 3.
    have h_deg_y : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {y})) = 3 := by
      rw [IntermediateField.adjoin.finrank]
      · exact Polynomial.natDegree_eq_of_degree_eq_some h_minpoly_y
      · refine ⟨Polynomial.X ^ 3 - 48 * Polynomial.X - 64, ?_, by aesop⟩
        refine Polynomial.Monic.def.2 ?_
        erw [Polynomial.leadingCoeff]
        erw [Polynomial.natDegree_sub_C]
        erw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_X]
    -- Since `y` is a root of the resolvent cubic, the degree of the extension `ℚ(y)` over `ℚ` is 3, and thus `3 ∣ [L : ℚ]`.
    have h_deg_L : Module.finrank ℚ a₄.SplittingField = Nat.card a₄.Gal := by
      convert (IsGalois.card_aut_eq_finrank ℚ a₄.SplittingField).symm
      apply_rules [IsGalois.mk]
    have := Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ { y }) a₄.SplittingField
    exact h_deg_L ▸ h_deg_y ▸ dvd_of_mul_right_eq _ this
  exact Nat.lcm_dvd h4 h3

/-
The Galois group order divides 24.
-/
private lemma card_gal_a4_dvd_24 : Nat.card a₄.Gal ∣ 24 := by
  convert card_gal_dvd_card_rootSet_factorial a₄ using 1
  erw [card_rootSet_eq_natDegree] <;> norm_num [a₄_natDegree]
  · exact a₄_irreducible.separable
  · apply ne_of_apply_ne (Polynomial.eval 0)
    norm_num [a₄]

/-
Helper: if y³ = 48y + 64, then z = (32 - y²)/4 also satisfies z³ - 48z - 64 = 0.
This shows the resolvent cubic Y³ - 48Y - 64 has another root in ℚ(y).
-/
private lemma resolvent_other_root_identity
    {R : Type*} [Field R] [CharZero R]
    (y : R) (hy : y ^ 3 - 48 * y - 64 = 0) :
    ((32 - y ^ 2) / 4) ^ 3 - 48 * ((32 - y ^ 2) / 4) - 64 = 0 := by
      grind

/-
Helper: the other root (32 - y²)/4 is distinct from y.
-/
private lemma resolvent_other_root_ne
    {R : Type*} [Field R] [CharZero R]
    (y : R) (hy : y ^ 3 - 48 * y - 64 = 0) :
    (32 - y ^ 2) / 4 ≠ y := by
      grobner

/-
Helper: there is no surjective group homomorphism from S₄ to any group of odd order > 1.
Proof: transpositions have order 2, which is coprime to any odd number,
so they map to 1. Since transpositions generate S₄, the map is trivial.
-/
private lemma perm_fin_four_not_surj_odd
    {G : Type*} [Group G] [Fintype G]
    (hG : Odd (Fintype.card G)) (hG1 : 1 < Fintype.card G)
    (f : Equiv.Perm (Fin 4) →* G) : ¬Function.Surjective f := by
      -- Every transposition maps to `1` under `f`.
      have h_transpositions : ∀ (i j : Fin 4), i ≠ j → f (Equiv.swap i j) = 1 := by
        intro i j hij
        have h_order : orderOf (f (Equiv.swap i j)) ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one]
          simp [sq, ← map_mul]
        have h_order_div : orderOf (f (Equiv.swap i j)) ∣ Fintype.card G := orderOf_dvd_card
        have := Nat.le_of_dvd (by decide) h_order
        interval_cases _ : orderOf (f (Equiv.swap i j)) <;> simp_all
        refine absurd (even_iff_two_dvd.mpr h_order_div) ?_
        simpa using hG
      -- Since transpositions generate `S₄`, we have `f σ = 1` for all `σ ∈ S₄`.
      have h_all : ∀ (σ : Equiv.Perm (Fin 4)), f σ = 1 := by
        intro σ
        induction' σ using Equiv.Perm.swap_induction_on with σ i j hij ih
        · exact map_one f
        · rw [map_mul, h_transpositions i j hij, ih, mul_one]
      exact fun h ↦ hG1.ne' (Fintype.card_eq_one_iff.mpr ⟨1, fun x ↦ by
        obtain ⟨σ, hσ⟩ := h x
        aesop⟩)

/-
Helper: The resolvent cubic X³-48X-64 is normal over ℚ when restricted to
the adjoin of one of its roots. This follows from all roots being in ℚ(y).
-/
set_option maxHeartbeats 800000 in
private lemma adjoin_resolvent_isNormal
    (y : a₄.SplittingField) (hy : y ^ 3 - 48 * y - 64 = 0)
    (_h_minpoly : minpoly ℚ y = X ^ 3 - C 48 * X - C 64)
    (_h_deg : Module.finrank ℚ (↑(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) = 3) :
    Normal ℚ (↑(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) := by
      -- Since `y` is a root of `X^3 - 48X - 64`, and `X^3 - 48X - 64` is irreducible over `ℚ`, the field `ℚ(y)` is a splitting field for `X^3 - 48X - 64`.
      have h_splitting :
          Polynomial.IsSplittingField ℚ (↥(IntermediateField.adjoin ℚ {y}))
            (Polynomial.X ^ 3 - Polynomial.C 48 * Polynomial.X - Polynomial.C 64) := by
        constructor
        · rw [Polynomial.splits_iff_exists_multiset]
          refine ⟨{ ⟨y, ?_⟩, ⟨(32 - y ^ 2) / 4, ?_⟩, ⟨-y - (32 - y ^ 2) / 4, ?_⟩ }, ?_⟩ <;> norm_num
          any_goals exact IntermediateField.mem_adjoin_simple_self ℚ y
          any_goals
            exact (Subfield.sub_mem _ (Subfield.neg_mem _ (IntermediateField.mem_adjoin_simple_self ℚ y))
              (Subfield.div_mem _
                (Subfield.sub_mem _ (Subfield.mem_carrier.mpr (by norm_num))
                  (Subfield.pow_mem _ (IntermediateField.mem_adjoin_simple_self ℚ y) 2))
                (Subfield.mem_carrier.mpr (by norm_num))))
          any_goals
            exact (Subfield.div_mem _
              (Subfield.sub_mem _ (Subfield.mem_carrier.mpr (by norm_num))
                (Subfield.pow_mem _ (IntermediateField.mem_adjoin_simple_self ℚ y) 2))
              (Subfield.mem_carrier.mpr (by norm_num)))
          refine Polynomial.funext fun x ↦ ?_
          erw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
            Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
          ext
          norm_num
          ring_nf
          rw [show y ^ 5 = y ^ 3 * y ^ 2 by ring, show y ^ 4 = y ^ 3 * y by ring,
            show y ^ 3 = 48 * y + 64 by linear_combination' hy]
          ring_nf
          rw [show y ^ 3 = 48 * y + 64 by linear_combination' hy]
          ring_nf
          norm_cast
          ring_nf
          norm_num [sub_eq_add_neg, add_assoc]
          exact neg_add_eq_neg_add_iff_add_eq_add.mpr rfl
        · refine le_antisymm ?_ ?_
          · exact le_top
          · intro x hx
            refine Algebra.adjoin_induction ?_ ?_ ?_ ?_
              (show x ∈ Algebra.adjoin ℚ
                  { (⟨y, IntermediateField.mem_adjoin_simple_self ℚ y⟩ : ↥ (IntermediateField.adjoin ℚ { y })) } from ?_)
            · have h_gen : ∀ x : a₄.SplittingField, x ∈ IntermediateField.adjoin ℚ {y} → x ∈ Algebra.adjoin ℚ {y} := by
                intro x hx
                rw [IntermediateField.mem_adjoin_simple_iff] at hx
                obtain ⟨r, s, rfl⟩ := hx
                by_cases hs : (aeval y) s = 0 <;> simp_all [div_eq_mul_inv]
                have h_inv :
                    ∀ x : a₄.SplittingField, x ∈ Algebra.adjoin ℚ {y} → x ≠ 0 → x⁻¹ ∈ Algebra.adjoin ℚ {y} :=
                  fun x a a_1 ↦ Algebra.IsIntegral.inv_mem a
                exact (Subalgebra.mul_mem _
                  ((Algebra.adjoin_singleton_eq_range_aeval ℚ y) ▸ Set.mem_range_self _)
                  (h_inv _ ((Algebra.adjoin_singleton_eq_range_aeval ℚ y) ▸ Set.mem_range_self _) hs))
              convert h_gen x x.2
              simp [Algebra.adjoin_singleton_eq_range_aeval]
              simp [aeval_def, Polynomial.eval₂_eq_sum_range]
              simp [← Subtype.coe_inj]
            · simp
              apply Algebra.subset_adjoin
              simp [Polynomial.mem_rootSet]
              refine ⟨ne_of_apply_ne (Polynomial.eval 0) ?_, ?_⟩
              · norm_num
              · simpa [Subtype.ext_iff] using hy
            · exact fun r ↦ Subalgebra.algebraMap_mem _ r
            · exact fun x y hx hy hx' hy' ↦ AddMemClass.add_mem hx' hy'
            · exact fun x y hx hy hx' hy' ↦ Subalgebra.mul_mem _ hx' hy'
      convert Normal.of_isSplittingField (Polynomial.X ^ 3 - Polynomial.C 48 * Polynomial.X - Polynomial.C 64 : ℚ[X])
      exact h_splitting

/-
Helper: The Galois group does not have order 24.
-/
set_option maxHeartbeats 800000 in
private lemma card_gal_ne_24 : Nat.card a₄.Gal ≠ 24 := by
  -- Assume |Gal| = 24 for contradiction.
  by_contra h_contra
  -- From the proof of twelve_dvd_card_gal_a4, there exists y in the splitting field with:
  -- - y³ - 48y - 64 = 0
  -- - minpoly ℚ y = X³ - 48X - 64
  -- - [ℚ(y):ℚ] = finrank ℚ (adjoin ℚ {y}) = 3
  obtain ⟨y, hy₁, hy₂, hy₃⟩ :
      ∃ y : a₄.SplittingField, y ^ 3 - 48 * y - 64 = 0 ∧ minpoly ℚ y = X ^ 3 - C 48 * X - C 64 ∧
        Module.finrank ℚ (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) = 3 := by
    -- Let `y = (α + β)^2` where `α` and `β` are roots of `a₄`.
    obtain ⟨α, β, hαβ⟩ :
        ∃ α β : a₄.SplittingField, a₄.eval₂ (algebraMap ℚ a₄.SplittingField) α = 0 ∧
          a₄.eval₂ (algebraMap ℚ a₄.SplittingField) β = 0 ∧ α ≠ β := by
      have h_roots : Multiset.card (Polynomial.roots (a₄.map (algebraMap ℚ a₄.SplittingField))) = 4 := by
        have := Polynomial.Splits.natDegree_eq_card_roots (Polynomial.SplittingField.splits a₄)
        rw [← this, Polynomial.natDegree_map, a₄_natDegree]
      obtain ⟨α, β, hαβ⟩ :
          ∃ α β : a₄.SplittingField, α ∈ Polynomial.roots (a₄.map (algebraMap ℚ a₄.SplittingField)) ∧
            β ∈ Polynomial.roots (a₄.map (algebraMap ℚ a₄.SplittingField)) ∧ α ≠ β := by
        by_cases h_distinct : Multiset.Nodup (Polynomial.roots (a₄.map (algebraMap ℚ a₄.SplittingField)))
        · rcases x : Polynomial.roots _ with (_ | ⟨α, _ | ⟨β, _ | h⟩⟩)
          simp_all
          rcases l₁ : (‹_› : List a₄.SplittingField) with (_ | ⟨α, _ | ⟨β, _ | ⟨γ, _ | ⟨δ, _ | l⟩⟩⟩⟩) <;>
            simp_all
        · have h_distinct : Polynomial.Separable (a₄.map (algebraMap ℚ a₄.SplittingField)) := by
            apply Polynomial.Separable.map
            exact a₄_irreducible.separable
          exact False.elim <|
            ‹¬Multiset.Nodup (Polynomial.roots (Polynomial.map (algebraMap ℚ a₄.SplittingField) a₄)) › <|
              Polynomial.nodup_roots h_distinct
      refine ⟨α, β, ?_, ?_, hαβ.2.2⟩
      · simpa [Polynomial.eval₂_eq_eval_map] using Polynomial.isRoot_of_mem_roots hαβ.1
      · simpa [Polynomial.eval₂_eq_eval_map] using Polynomial.isRoot_of_mem_roots hαβ.2.1
    use (α + β)^2
    have h_minpoly : minpoly ℚ ((α + β) ^ 2) = X ^ 3 - C 48 * X - C 64 := by
      refine Eq.symm (minpoly.eq_of_irreducible_of_monic resolvent_a4_irreducible ?_ ?_)
      · simp_all [a₄]
        grind
      · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
          Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
    have := minpoly.aeval ℚ ((α + β) ^ 2)
    simp_all [Polynomial.eval₂_eq_eval_map]
    rw [IntermediateField.adjoin.finrank]
    · erw [h_minpoly, Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
    · refine ⟨Polynomial.X ^ 3 - Polynomial.C 48 * Polynomial.X - Polynomial.C 64, ?_, by aesop⟩
      refine Polynomial.Monic.def.2 ?_
      erw [Polynomial.leadingCoeff]
      erw [Polynomial.natDegree_sub_C]
      erw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_X]
  -- Therefore, Gal(L/ℚ) ≅ Perm(Fin 4).
  have h_iso_perm : Nonempty (a₄.Gal ≃* (Equiv.Perm (Fin 4))) := by
    -- The Galois group of a₄ is isomorphic to a subgroup of S₄.
    have h_iso_subgroup : ∃ (f : a₄.Gal →* Equiv.Perm (a₄.rootSet ℂ)), Function.Injective f := by
      obtain ⟨f₀, hf₀⟩ :
          ∃ (f : a₄.Gal →* Equiv.Perm (a₄.rootSet a₄.SplittingField)), Function.Injective f := by
        have : Fact ((a₄.map (algebraMap ℚ a₄.SplittingField)).Splits) := ⟨SplittingField.splits a₄⟩
        exact ⟨Gal.galActionHom a₄ a₄.SplittingField, Gal.galActionHom_injective a₄ a₄.SplittingField⟩
      obtain ⟨e⟩ :
          Nonempty (Equiv.Perm (a₄.rootSet a₄.SplittingField) ≃* Equiv.Perm (a₄.rootSet ℂ)) := by
        have h_equiv : Nonempty (a₄.rootSet a₄.SplittingField ≃ a₄.rootSet ℂ) := by
          refine ⟨Fintype.equivOfCardEq ?_⟩
          rw [card_rootSet_eq_natDegree]
          · convert Polynomial.card_rootSet_eq_natDegree _ _
            · exact a₄_irreducible.separable
            · exact Polynomial.SplittingField.splits _
          · exact a₄_irreducible.separable
          · apply ne_of_apply_ne (Polynomial.eval 0)
            norm_num [a₄]
        exact ⟨{ Equiv.permCongr h_equiv.some with map_mul' := by aesop }⟩
      exact ⟨e.toMonoidHom.comp f₀, e.injective.comp hf₀⟩
    -- Since the Galois group has order 24 and S₄ also has order 24, the injective homomorphism must be an isomorphism.
    obtain ⟨f, hf_inj⟩ := h_iso_subgroup
    have hf_surj : Function.Surjective f := by
      have hf_card : Nat.card (a₄.Gal) = Nat.card (Equiv.Perm (a₄.rootSet ℂ)) := by
        have h_card_rootSet : Fintype.card (a₄.rootSet ℂ) = 4 := by
          convert card_rootSet_eq_natDegree a₄ _ _
          · exact a₄_natDegree.symm
          · exact a₄_irreducible.separable
          · apply ne_of_apply_ne (Polynomial.eval 0)
            norm_num [a₄]
        simp_all +decide [Fintype.card_perm]
      have hf_finite : Finite (a₄.Gal) ∧ Finite (Equiv.Perm (a₄.rootSet ℂ)) := by
        refine ⟨Nat.finite_of_card_ne_zero ?_, Nat.finite_of_card_ne_zero ?_⟩
        · positivity
        · rw [← hf_card]
          positivity
      have := hf_finite.1
      have := hf_finite.2
      exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by aesop⟩).2
    have h_iso_perm : Nonempty (a₄.Gal ≃* Equiv.Perm (a₄.rootSet ℂ)) :=
      ⟨{ Equiv.ofBijective f ⟨hf_inj, hf_surj⟩ with map_mul' := f.map_mul }⟩
    have h_card_rootSet : Fintype.card (a₄.rootSet ℂ) = 4 := by
      convert card_rootSet_eq_natDegree a₄ _ _
      · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
      · exact a₄_irreducible.separable
      · apply ne_of_apply_ne (Polynomial.eval 0)
        norm_num [a₄]
    obtain ⟨g⟩ := h_iso_perm
    exact ⟨g.trans { Equiv.permCongr (Fintype.equivOfCardEq h_card_rootSet) with map_mul' := by aesop }⟩
  -- Therefore, there exists a surjective homomorphism from Perm(Fin 4) to Gal(ℚ(y)/ℚ).
  obtain ⟨f, hf⟩ :
      ∃ f : Equiv.Perm (Fin 4) →* (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)) ≃ₐ[ℚ]
        ↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))), Function.Surjective f := by
    have h_restrict :
        ∃ f : (a₄.SplittingField ≃ₐ[ℚ] a₄.SplittingField) →*
          (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)) ≃ₐ[ℚ]
            ↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))), Function.Surjective f := by
      have h_normal : Normal ℚ (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) :=
        adjoin_resolvent_isNormal y hy₁ hy₂ hy₃
      exact ⟨_, AlgEquiv.restrictNormalHom_surjective _⟩
    obtain ⟨f, hf⟩ := h_restrict
    exact ⟨f.comp h_iso_perm.some.symm.toMonoidHom, hf.comp h_iso_perm.some.symm.surjective⟩
  -- Gal(ℚ(y)/ℚ) has odd order 3 > 1.
  have h_odd_order :
      Odd (Nat.card (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)) ≃ₐ[ℚ]
        ↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)))) ∧
        1 < Nat.card (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)) ≃ₐ[ℚ]
          ↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) := by
    have h_card3 :
        Nat.card (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField)) ≃ₐ[ℚ]
          ↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) = 3 := by
      have h_iso : IsGalois ℚ (↥(IntermediateField.adjoin ℚ ({y} : Set a₄.SplittingField))) :=
        { to_isSeparable := isSeparable_tower_bot ℚ ℚ⟮y⟯,
          to_normal := adjoin_resolvent_isNormal y hy₁ hy₂ hy₃ }
      rw [← hy₃, IsGalois.card_aut_eq_finrank]
    rw [h_card3]
    refine ⟨?_, ?_⟩ <;> decide
  convert perm_fin_four_not_surj_odd _ _ f hf
  all_goals aesop

/-- The Galois group has order exactly 12. -/
private lemma card_gal_a4 : Nat.card a₄.Gal = 12 := by
  have h12 := twelve_dvd_card_gal_a4
  have h24 := card_gal_a4_dvd_24
  have hne := card_gal_ne_24
  have hpos : 0 < Nat.card a₄.Gal := Nat.card_pos
  have hle : Nat.card a₄.Gal ≤ 24 := Nat.le_of_dvd (by omega) h24
  have hge : 12 ≤ Nat.card a₄.Gal := Nat.le_of_dvd hpos h12
  interval_cases (Nat.card a₄.Gal) <;> omega

/-
The Galois group of X⁴+8X+12 is isomorphic to the alternating group A₄.
-/
private lemma gal_iso_alternating :
    Nonempty (a₄.Gal ≃* ↥(alternatingGroup (Fin 4))) := by
      -- The polynomial `a₄` is irreducible over `ℚ`, so its Galois group is isomorphic to a subgroup of `S₄`.
      have h_galois_subgroup : ∃ (f : a₄.Gal →* Equiv.Perm (Fin 4)), Function.Injective f := by
        obtain ⟨f₀, hf₀⟩ : ∃ (f : a₄.Gal →* Equiv.Perm (a₄.rootSet ℂ)), Function.Injective f := by
          have : Fact ((a₄.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
          exact ⟨Gal.galActionHom a₄ ℂ, Gal.galActionHom_injective a₄ ℂ⟩
        have h_perm : Nonempty (Equiv.Perm (a₄.rootSet ℂ) ≃* Equiv.Perm (Fin 4)) := by
          have h_card4 : Fintype.card (a₄.rootSet ℂ) = 4 := by
            convert card_rootSet_eq_natDegree a₄ a₄_irreducible.separable _
            · erw [Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
            · apply ne_of_apply_ne (Polynomial.eval 0)
              norm_num [a₄]
          exact ⟨{ Equiv.permCongr (Fintype.equivOfCardEq <| by aesop) with map_mul' := by aesop }⟩
        exact ⟨h_perm.some.toMonoidHom.comp f₀, h_perm.some.injective.comp hf₀⟩
      -- Since the Galois group has order 12 and is a subgroup of `S₄`, it must be isomorphic to `A₄`.
      obtain ⟨f, hf_inj⟩ := h_galois_subgroup
      have h_card : Nat.card (Set.range f) = 12 := by
        rw [Nat.card_range_of_injective hf_inj]
        convert card_gal_a4
      have h_subgroup : ∀ (H : Subgroup (Equiv.Perm (Fin 4))), Nat.card H = 12 → H = alternatingGroup (Fin 4) := by
        intros H hH_card
        have h_index : H.index = 2 := by
          have := Subgroup.index_mul_card H
          simp_all
          refine mul_right_cancel₀ ?_ this
          decide
        grind only [Equiv.Perm.eq_alternatingGroup_of_index_eq_two]
      rw [← h_subgroup (MonoidHom.range f)]
      · have hsurj : Function.Surjective
            (fun x ↦ (⟨f x, Set.mem_range_self x⟩ : ↥(MonoidHom.range f))) := by
          intro x
          obtain ⟨y, hy⟩ := x.2
          aesop
        exact ⟨{ Equiv.ofBijective (fun x ↦ ⟨f x, Set.mem_range_self x⟩)
            ⟨fun x y hxy ↦ hf_inj <| by simpa using hxy, hsurj⟩ with
            map_mul' := fun x y ↦ by aesop }⟩
      · exact h_card

/-- The alternating group `A₄` is an inverse Galois group,
realized as the Galois group of `X⁴ + 8X + 12` over `ℚ`. -/
theorem IsInverseGalois.alternating_four :
    IsInverseGalois (↥(alternatingGroup (Fin 4))) := by
  obtain ⟨e⟩ := gal_iso_alternating
  exact ⟨a₄.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal a₄ },
    ⟨e⟩⟩

end
