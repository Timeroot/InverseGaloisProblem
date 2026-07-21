/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic
import InverseGalois.Polynomial.GaloisGroupTools

/-!
# S₄ is an Inverse Galois Group

We show that `S₄ = Equiv.Perm (Fin 4)` is an inverse Galois group over `ℚ`,
by exhibiting the polynomial `X⁴ - X - 1` whose Galois group is `S₄`.

## Strategy

1. `X⁴ - X - 1` is irreducible over `ℚ` (no rational roots + no quadratic factorization)
2. It has exactly 2 real roots and 2 complex conjugate roots
3. Complex conjugation gives a transposition in the Galois group
4. The resolvent cubic `X³ + 4X - 1` is irreducible over `ℚ`
5. By the classification of transitive subgroups of `S₄`:
   - irreducible resolvent cubic → Gal ∈ {A₄, S₄}
   - discriminant = -283 is not a square → Gal ⊄ A₄
   - Therefore Gal ≅ S₄
-/

open Polynomial IntermediateField

noncomputable section

/-- The polynomial `X⁴ - X - 1` over `ℚ`. -/
private def q₄ : ℚ[X] := X ^ 4 - X - C 1

/-
`X⁴ - X - 1` is irreducible over `ℚ`.
-/
private lemma q₄_irreducible : Irreducible q₄ := by
  -- We'll use that `X^4 - X - 1` is irreducible over `ℤ`.
  have h_irred_Z : Irreducible (X ^ 4 - X - 1 : Polynomial ℤ) := by
    -- To prove irreducibility, we can use the fact that if a polynomial is irreducible over the integers, then it is also irreducible over the rationals. Hence, we need to show that `X^4 - X - 1` is irreducible over the integers.
    have h_irred_int : ∀ p q : Polynomial ℤ, p.degree > 0 → q.degree > 0 →
        p * q = Polynomial.X ^ 4 - Polynomial.X - 1 → False := by
      intro p q hp hq h_eq
      have h_deg : p.degree + q.degree = 4 := by
        rw [← Polynomial.degree_mul, h_eq, Polynomial.degree_sub_eq_left_of_degree_lt] <;>
          rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
      have h_deg_cases : p.degree = 1 ∧ q.degree = 3 ∨ p.degree = 3 ∧ q.degree = 1 ∨ p.degree = 2 ∧ q.degree = 2 := by
        rw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hp),
          Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)] at *
        norm_cast at *
        omega
      rcases h_deg_cases with (⟨hp_deg, hq_deg⟩ | ⟨hp_deg, hq_deg⟩ | ⟨hp_deg, hq_deg⟩) <;> simp_all +decide only []
      · -- If `p` is a linear polynomial, then `p` must have a root in `ℤ`.
        obtain ⟨a, ha⟩ : ∃ a : ℤ, p.eval a = 0 := by
          rw [Polynomial.eq_X_add_C_of_degree_eq_one hp_deg]
          -- Since `p` is a linear polynomial with integer coefficients, its leading coefficient must be `± 1`.
          have h_leading_coeff : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := by
            have h_leading_coeff : p.leadingCoeff * q.leadingCoeff = 1 := by
              rw [← Polynomial.leadingCoeff_mul, h_eq, Polynomial.leadingCoeff,
                Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
            exact Int.eq_one_or_neg_one_of_mul_eq_one h_leading_coeff
          exact h_leading_coeff.elim (fun h ↦ ⟨-p.coeff 0, by norm_num [h]⟩) fun h ↦ ⟨p.coeff 0, by norm_num [h]⟩
        replace h_eq := congr_arg (Polynomial.eval a) h_eq
        simp_all +decide [Polynomial.eval_mul]
        have := (show a ≤ 1 by nlinarith [sq_nonneg (a^2 - 1)])
        have := (show a ≥ -1 by nlinarith [sq_nonneg (a^2 - 1)])
        interval_cases a <;> trivial
      · -- Let `r` be a root of `q`. Then `q(r) = 0`, which implies `r` is a root of `X^4 - X - 1`.
        obtain ⟨r, hr⟩ : ∃ r : ℤ, q.eval r = 0 := by
          rw [Polynomial.eq_X_add_C_of_degree_eq_one hq_deg]
          have h_leading_coeff : q.leadingCoeff ∣ 1 := by
            have h_leading_coeff : q.leadingCoeff * p.leadingCoeff = 1 := by
              rw [mul_comm, ← Polynomial.leadingCoeff_mul, h_eq, Polynomial.leadingCoeff,
                Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
            exact dvd_of_mul_right_eq _ h_leading_coeff
          obtain h | h := Int.isUnit_iff.mp (isUnit_of_dvd_one h_leading_coeff) <;>
            use -q.coeff 0 / q.leadingCoeff <;> simp_all +decide
        replace h_eq := congr_arg (Polynomial.eval r) h_eq
        simp_all +decide
        have := (show r ≤ 1 by nlinarith [sq_nonneg (r^2 - 1)])
        have := (show r ≥ -1 by nlinarith [sq_nonneg (r^2 - 1)])
        interval_cases r <;> trivial
      · -- Let `p(x) = ax^2 + bx + c` and `q(x) = dx^2 + ex + f`.
        obtain ⟨a, b, c, d, e, f, hp, hq⟩ : ∃ a b c d e f : ℤ,
            p = Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c ∧
            q = Polynomial.C d * Polynomial.X ^ 2 + Polynomial.C e * Polynomial.X + Polynomial.C f := by
          rw [@Polynomial.as_sum_range_C_mul_X_pow ℤ _ p, @Polynomial.as_sum_range_C_mul_X_pow ℤ _ q]
          exact ⟨p.coeff 2, p.coeff 1, p.coeff 0, q.coeff 2, q.coeff 1, q.coeff 0,
            by simp +arith +decide [Polynomial.natDegree_eq_of_degree_eq_some hp_deg, Finset.sum_range_succ'],
            by simp +arith +decide [Polynomial.natDegree_eq_of_degree_eq_some hq_deg, Finset.sum_range_succ']⟩
        -- By comparing coefficients, we get the following system of equations:
        -- `a * d = 1`
        -- `a * e + b * d = 0`
        -- `a * f + b * e + c * d = 0`
        -- `b * f + c * e = -1`
        -- `c * f = -1`
        have h_coeff : a * d = 1 ∧ a * e + b * d = 0 ∧ a * f + b * e + c * d = 0 ∧ b * f + c * e = -1 ∧ c * f = -1 := by
          subst_vars
          have h₁ := congr_arg (Polynomial.eval (-2)) h_eq
          have h₂ := congr_arg (Polynomial.eval (-1)) h_eq
          have h₃ := congr_arg (Polynomial.eval 0) h_eq
          have h₄ := congr_arg (Polynomial.eval 1) h_eq
          have h₅ := congr_arg (Polynomial.eval 2) h_eq
          norm_num at h₁ h₂ h₃ h₄ h₅
          exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
        rcases Int.eq_one_or_neg_one_of_mul_eq_one h_coeff.1 with (rfl | rfl) <;>
          rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h_coeff.2.2.2.2 with (rfl | rfl) <;>
          norm_num at h_coeff ⊢ <;> nlinarith [show b = 0 by nlinarith]
    constructor <;> contrapose! h_irred_int
    · exact absurd (Polynomial.degree_eq_zero_of_isUnit h_irred_int) (by
        erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
          erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num)
    · obtain ⟨a, b, h₁, h₂, h₃⟩ := h_irred_int
      use a, b
      simp_all +decide [Polynomial.isUnit_iff]
      constructor <;> refine lt_of_not_ge fun h ↦ ?_
      · rw [Polynomial.eq_C_of_degree_le_zero h] at h₁ h₂
        replace h₁ := congr_arg (fun p ↦ Polynomial.coeff p 4) h₁
        norm_num [Polynomial.coeff_one, Polynomial.coeff_X, pow_succ'] at h₁
        exact h₂ (a.coeff 0) (isUnit_of_dvd_one <| h₁.symm ▸ dvd_mul_right _ _) (by aesop)
      · rw [Polynomial.eq_C_of_degree_le_zero h] at h₃ h₁
        replace h₁ := congr_arg (fun p ↦ p.coeff 4) h₁
        norm_num [Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_C] at h₁
        exact h₃ (b.coeff 0) (isUnit_of_dvd_one <| h₁.symm ▸ dvd_mul_left _ _) rfl
  have h_gauss : Irreducible (Polynomial.map (Int.castRingHom ℚ) (X ^ 4 - X - 1 : Polynomial ℤ)) := by
    have h_primitive : Polynomial.IsPrimitive (X ^ 4 - X - 1 : Polynomial ℤ) := by
      exact Polynomial.Monic.isPrimitive (by
        erw [Polynomial.Monic, Polynomial.leadingCoeff]
        erw [Polynomial.natDegree_sub_C]
        erw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X])
    grind only [IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  aesop

private lemma q₄_natDegree : q₄.natDegree = 4 := by
  erw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num

/-
`X⁴ - X - 1` has exactly 2 real roots and 2 complex conjugate roots.
More precisely, `card(rootSet ℂ) = 4` and `card(rootSet ℝ) = 2`.
-/
private lemma q₄_real_roots : Fintype.card (q₄.rootSet ℝ) = 2 := by
  -- By the Intermediate Value Theorem, since `q₄(-1) = 1 > 0 > -1 = q₄(0)`, there is at least one root in the interval `(-1, 0)`.
  have h_root_interval : ∃ x ∈ Set.Ioo (-1 : ℝ) 0, x ^ 4 - x - 1 = 0 := by
    apply intermediate_value_Ioo' <;> norm_num
    exact Continuous.continuousOn (by continuity)
  -- By the Intermediate Value Theorem, since `q₄(1) = -1 < 0 < 13 = q₄(2)`, there is at least one root in the interval `(1, 2)`.
  have h_root_interval2 : ∃ x ∈ Set.Ioo (1 : ℝ) 2, x ^ 4 - x - 1 = 0 := by
    apply intermediate_value_Ioo <;> norm_num
    exact Continuous.continuousOn (by continuity)
  obtain ⟨x₁, hx₁⟩ := h_root_interval
  obtain ⟨x₂, hx₂⟩ := h_root_interval2
  have h_card : (q₄.map (algebraMap ℚ ℝ)).roots.toFinset = {x₁, x₂} := by
    ext
    simp
    constructor <;> intro h <;> simp_all +decide [q₄]
    · by_cases h_cases : ‹ℝ› < 0
      · by_contra h_contra
        exact h_contra <| Or.inl <| by
          nlinarith [mul_pos (sub_pos.mpr h_cases) (sub_pos.mpr hx₁.1.1),
            mul_pos (sub_pos.mpr h_cases) (sub_pos.mpr hx₁.1.2),
            mul_pos (sub_pos.mpr hx₁.1.1) (sub_pos.mpr hx₁.1.2),
            pow_two_nonneg ((‹ℝ› : ℝ) ^ 2 - x₁ ^ 2), pow_two_nonneg ((‹ℝ› : ℝ) - x₁)]
      · exact Or.inr <| by
          nlinarith [sq_nonneg ((‹_› : ℝ) ^ 2 - x₂ ^ 2),
            mul_le_mul_of_nonneg_left (le_of_not_gt h_cases) <| sq_nonneg <| (‹_› : ℝ) - x₂]
    · exact ⟨by exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num), by rcases h with (rfl | rfl) <;> linarith⟩
  convert congr_arg Finset.card h_card using 1
  · norm_num [Polynomial.rootSet_def]
  · rw [Finset.card_pair (by linarith [hx₁.1.2, hx₂.1.1])]

/-
The resolvent cubic `X³ + 4X - 1` of `X⁴ - X - 1` is irreducible over `ℚ`.
-/
private lemma resolvent_irreducible :
    Irreducible (X ^ 3 + C 4 * X - C 1 : ℚ[X]) := by
      -- By the rational root theorem, the only possible rational roots of `X^3 + 4X - 1` are `± 1`.
      have h_no_rational_roots :
          ¬∃ r : ℚ, Polynomial.eval r (Polynomial.X ^ 3 + Polynomial.C 4 * Polynomial.X - Polynomial.C 1) = 0 := by
        -- By the rational root theorem, the only possible rational roots are ±1.
        by_contra h_contra
        obtain ⟨r, hr⟩ := h_contra
        have h_div : r.den ∣ 1 := by
          have h_rational_root : r.num ^ 3 + 4 * r.num * r.den ^ 2 - r.den ^ 3 = 0 := by
            simp_all +decide [← @Int.cast_inj ℚ]
            rw [← Rat.num_div_den r] at hr
            grind
          have h_div : (r.den : ℤ) ∣ r.num ^ 3 := by
            exact ⟨-4 * r.num * r.den + r.den ^ 2, by linarith⟩
          have := Int.dvd_coe_gcd h_div (dvd_refl _)
          simp_all +decide [Int.gcd, Int.natAbs_pow]
          simp_all +decide [Nat.Coprime, Nat.Coprime.gcd_eq_one, Rat.reduced]
          exact Nat.eq_one_of_dvd_one (Int.natCast_dvd_natCast.mp this)
        norm_num +zetaDelta at *
        rw [← @Rat.num_div_den r] at hr
        norm_num [h_div] at hr
        norm_cast at hr
        have := (show r.num ≤ 1 by nlinarith [sq_nonneg (r.num^2)])
        have := (show r.num ≥ -1 by nlinarith [sq_nonneg (r.num^2)])
        interval_cases r.num <;> trivial
      -- Since `X^3 + 4X - 1` is a cubic polynomial with no rational roots, it is irreducible over `ℚ`.
      have h_irred : ∀ p q : Polynomial ℚ, p.degree > 0 → q.degree > 0 →
          Polynomial.X ^ 3 + Polynomial.C 4 * Polynomial.X - Polynomial.C 1 = p * q → False := by
        intros p q hp hq h_factor
        have h_deg : p.degree + q.degree = 3 := by
          rw [← Polynomial.degree_mul, ← h_factor, Polynomial.degree_sub_C] <;>
            erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num
        -- Since `p` and `q` are non-constant polynomials with degrees adding up to 3, one of them must have degree 1.
        obtain (h_deg_p | h_deg_q) : p.degree = 1 ∨ q.degree = 1 := by
          erw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hp),
            Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)] at *
          norm_cast at *
          omega
        · exact h_no_rational_roots <| by
            obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one h_deg_p
            exact ⟨r, by aesop⟩
        · exact h_no_rational_roots <| by
            obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one h_deg_q
            exact ⟨r, by aesop⟩
      constructor
      · exact fun h ↦ absurd (Polynomial.degree_eq_zero_of_isUnit h) (by
          erw [Polynomial.degree_sub_C] <;>
            erw [Polynomial.degree_add_eq_left_of_degree_lt] <;> norm_num)
      · contrapose! h_irred
        obtain ⟨a, b, h₁, h₂, h₃⟩ := h_irred
        refine ⟨a, b, not_le.mp fun h ↦ h₂ <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
          le_antisymm h <| le_of_not_gt fun h' ↦ ?_, not_le.mp fun h ↦ h₃ <|
          Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <| le_of_not_gt fun h' ↦ ?_,
          h₁, trivial⟩
        · apply_fun Polynomial.eval 0 at h₁
          aesop
        · apply_fun Polynomial.eval 0 at h₁
          aesop

/-
The discriminant of `X⁴ - X - 1` equals -283, which is not a perfect square.
This implies the Galois group is not contained in `A₄`.
-/
private lemma q₄_disc_not_sq :
    ¬ IsSquare ((-283 : ℤ)) := by
      decide

/-
The Galois group of `X⁴ - X - 1` acts faithfully on its 4 roots, giving an embedding
into `S₄ = Equiv.Perm (Fin 4)`. The image is all of `S₄` because:
- The resolvent cubic is irreducible (rules out `D₄`, `V₄`, `ℤ/4ℤ`)
- The discriminant is not a square (rules out `A₄`)
- The only remaining possibility is `S₄`.

Together with the irreducibility (which gives transitivity), this shows `|Gal| = 24 = |S₄|`.
-/

/-- Key algebraic identity: from the Vieta relations of the quartic X⁴-X-1,
the resolvent root satisfies t⁶ + 4t² - 1 = 0. -/
private lemma resolvent_identity {K : Type*} [Field K] (t w v : K)
    (h1 : t ^ 2 = w + v) (h2 : w * v = -1) (h3 : t * (v - w) = 1) :
    t ^ 6 + 4 * t ^ 2 - 1 = 0 := by
  have step1 : t ^ 2 * (v - w) ^ 2 = 1 := by
    calc t ^ 2 * (v - w) ^ 2 = (t * (v - w)) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h3]
      _ = 1 := by ring
  have step2 : (v - w) ^ 2 = t ^ 4 + 4 := by
    have : (v - w) ^ 2 = (w + v) ^ 2 - 4 * (w * v) := by ring
    rw [← h1, h2] at this
    linear_combination this
  rw [step2] at step1
  linear_combination step1

/-- If α is a root of q₄ and γ is a root of the cubic factor, then (α+γ)² is a root
of the resolvent cubic Y³+4Y-1. This follows from the resolvent_identity and
direct algebraic computation. -/
private lemma resolvent_root_from_cubic_root (α γ : q₄.SplittingField)
    (hα : α ^ 4 = α + 1)
    (hγ : γ ^ 3 + α * γ ^ 2 + α ^ 2 * γ + (α ^ 3 - 1) = 0) :
    ((α + γ) ^ 2) ^ 3 + 4 * (α + γ) ^ 2 - 1 = 0 := by
  set t := α + γ with ht_def
  set w := α * γ with hw_def
  set v := α ^ 2 + α * γ + γ ^ 2 with hv_def
  have h1 : t ^ 2 = w + v := by
    simp only [ht_def, hw_def, hv_def]
    ring
  have h2 : w * v = -1 := by
    simp only [hw_def, hv_def]
    linear_combination α * hγ - hα
  have h3 : t * (v - w) = 1 := by
    simp only [ht_def, hv_def, hw_def]
    linear_combination hγ
  have key := resolvent_identity t w v h1 h2 h3
  linear_combination key

/-
The cubic factor g(X) = X³+αX²+α²X+α³-1 of q₄ over ℚ(α) is irreducible.
This follows from the resolvent cubic Y³+4Y-1 being irreducible over ℚ.
If g had a root γ in ℚ(α), then y = (α+γ)² would be a root of Y³+4Y-1 in ℚ(α),
but [ℚ(α):ℚ] = 4 and the resolvent generates a degree 3 extension, contradicting 3 ∤ 4.
-/
private lemma cubic_factor_irreducible :
    ∀ (α : q₄.SplittingField),
    Polynomial.aeval α q₄ = 0 →
    ¬ ∃ (γ : IntermediateField.adjoin ℚ {α}),
      γ.val ^ 3 + α * γ.val ^ 2 + α ^ 2 * γ.val + (α ^ 3 - 1) = 0 := by
        intro α hα
        by_contra h_contra
        obtain ⟨γ, hγ⟩ := h_contra
        have h_resolvent : ((α + γ.val) ^ 2) ^ 3 + 4 * (α + γ.val) ^ 2 - 1 = 0 := by
          convert resolvent_root_from_cubic_root α γ.val _ _ using 1
          · unfold q₄ at hα
            norm_num at hα
            linear_combination' hα
          · exact hγ
        -- Since `y = (α + γ)^2` is in `ℚ(α)`, we have `ℚ(y) ⊆ ℚ(α)`.
        have h_sub : IntermediateField.adjoin ℚ {((α + γ.val) ^ 2)} ≤ IntermediateField.adjoin ℚ {α} := by
          simp +zetaDelta at *
          exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (IntermediateField.mem_adjoin_simple_self ℚ α) γ.2) _
        -- Since `y = (α + γ)^2` is a root of the resolvent cubic `X^3 + 4X - 1`, we have `[ℚ(y):ℚ] = 3`.
        have h_deg_y : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {((α + γ.val) ^ 2)})) = 3 := by
          rw [IntermediateField.adjoin.finrank]
          · have h_minpoly : minpoly ℚ ((α + γ.val) ^ 2) =
                Polynomial.X ^ 3 + Polynomial.C 4 * Polynomial.X - Polynomial.C 1 := by
              refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
              · exact resolvent_irreducible
              · aesop
              · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
                  Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
                norm_num [Polynomial.coeff_one]
            erw [h_minpoly, Polynomial.natDegree_sub_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
          · refine ⟨Polynomial.X ^ 3 + Polynomial.C 4 * Polynomial.X - Polynomial.C 1, ?_, ?_⟩ <;> norm_num [h_resolvent]
            erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
              Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
            norm_num [Polynomial.coeff_one]
        -- Since `α` is a root of `q₄`, we have `[ℚ(α):ℚ] = 4`.
        have h_deg_α : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) = 4 := by
          have h_deg_α : IsIntegral ℚ α := by
            exact Algebra.IsIntegral.isIntegral α
          have h_deg_α : minpoly ℚ α = q₄ := by
            refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_) <;> norm_num [q₄] at *
            · exact q₄_irreducible
            · exact hα
            · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
                Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
          have h_deg_α : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) = Polynomial.natDegree (minpoly ℚ α) := by
            rw [IntermediateField.adjoin.finrank]
            aesop
          rw [h_deg_α, h_deg_α] at *
          simp_all +decide [q₄_natDegree]
        have h_div : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {((α + γ.val) ^ 2)})) ∣
            Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) := by
          exact finrank_dvd_of_le_right h_sub
        simp_all +decide only []

/-
3 divides the order of the Galois group of q₄.
-/
set_option maxHeartbeats 800000 in
private lemma three_dvd_card_gal : 3 ∣ Nat.card q₄.Gal := by
  -- Let α be a root of q₄ in the splitting field. Then [ℚ(α):ℚ] = 4 since q₄ is irreducible of degree 4.
  obtain ⟨α, hα⟩ : ∃ α : q₄.SplittingField, Polynomial.aeval α q₄ = 0 := by
    convert Polynomial.Splits.exists_eval_eq_zero
      (f := Polynomial.map (algebraMap ℚ q₄.SplittingField) q₄) _ _
    · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    · exact Polynomial.SplittingField.splits _
    · erw [Polynomial.degree_map, Polynomial.degree_sub_C] <;>
        erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
  have h_deg : 4 ∣ (Module.finrank ℚ (IntermediateField.adjoin ℚ {α})) := by
    have h_deg : minpoly ℚ α = Polynomial.C (1 / 1) * q₄ := by
      refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_) <;> norm_num [hα]
      · exact q₄_irreducible
      · unfold q₄
        erw [Polynomial.Monic, Polynomial.leadingCoeff]
        erw [Polynomial.natDegree_sub_C]
        erw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
    have h_deg : Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = Polynomial.natDegree (minpoly ℚ α) := by
      convert (IntermediateField.adjoin.finrank <| show IsIntegral ℚ α from ?_)
      exact Algebra.IsIntegral.isIntegral α
    simp_all +decide [q₄_natDegree]
  -- Since g is irreducible over ℚ(α) of degree 3, adjoining β gives [ℚ(α,β):ℚ(α)] = 3, so 3 | [K:ℚ] = Nat.card q₄.Gal (by tower law).
  have h_deg_beta : 3 ∣ (Module.finrank (IntermediateField.adjoin ℚ {α}) q₄.SplittingField) := by
    -- Let β be a root of g in the splitting field.
    obtain ⟨β, hβ⟩ : ∃ β : q₄.SplittingField, β ^ 3 + α * β ^ 2 + α ^ 2 * β + (α ^ 3 - 1) = 0 := by
      obtain ⟨β, hβ⟩ : ∃ β : q₄.SplittingField, β ≠ α ∧ Polynomial.aeval β q₄ = 0 := by
        by_contra! h_contra
        -- If `q₄` has only one root in its splitting field, then `q₄` would be linear, contradicting its degree being 4.
        have h_linear : q₄.map (algebraMap ℚ q₄.SplittingField) = (Polynomial.X - Polynomial.C α) ^ 4 := by
          have h_linear : q₄.map (algebraMap ℚ q₄.SplittingField) =
              Polynomial.C (1 : q₄.SplittingField) * Multiset.prod (Multiset.map
                (fun β ↦ Polynomial.X - Polynomial.C β)
                (Polynomial.roots (q₄.map (algebraMap ℚ q₄.SplittingField)))) := by
            convert Polynomial.Splits.eq_prod_roots _
            · unfold q₄
              erw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero] <;> norm_num
              · erw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
                  Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
                  norm_num [Polynomial.coeff_one, Polynomial.coeff_X]
              · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num)
            · exact Polynomial.SplittingField.splits _
          rw [h_linear]
          rw [show Polynomial.roots (Polynomial.map (algebraMap ℚ q₄.SplittingField) q₄) =
            Multiset.replicate 4 α from ?_]
          · norm_num [← pow_mul]
            ring
          · refine Multiset.eq_replicate.mpr ⟨?_, ?_⟩
            · replace h_linear := congr_arg Polynomial.natDegree h_linear
              norm_num [Polynomial.natDegree_map] at h_linear ⊢
              exact h_linear ▸ q₄_natDegree
            · exact fun x hx ↦ Classical.not_not.1 fun hx' ↦ h_contra x hx' <|
                by simpa [Polynomial.eval_map] using Polynomial.isRoot_of_mem_roots hx
        simp_all +decide [q₄]
        have := congr_arg (Polynomial.derivative) h_linear
        norm_num at this
        replace this := congr_arg (Polynomial.eval 0) this
        norm_num [Polynomial.derivative_pow] at this
        grind
      use β
      unfold q₄ at *
      norm_num at *
      exact mul_left_cancel₀ (sub_ne_zero_of_ne hβ.1) <| by linear_combination hβ.2 - hα
    -- Since `g` is irreducible over `ℚ(α)`, the minimal polynomial of `β` over `ℚ(α)` has degree 3.
    have h_min_poly_deg : Polynomial.natDegree (minpoly (IntermediateField.adjoin ℚ {α}) β) = 3 := by
      have h_deg2 : minpoly (IntermediateField.adjoin ℚ {α}) β =
          Polynomial.X ^ 3 +
            Polynomial.C (⟨α, IntermediateField.subset_adjoin ℚ {α} (Set.mem_singleton α)⟩ :
              IntermediateField.adjoin ℚ {α}) * Polynomial.X ^ 2 +
            Polynomial.C (⟨α ^ 2, Subalgebra.pow_mem _ (IntermediateField.mem_adjoin_simple_self ℚ α) 2⟩ :
              IntermediateField.adjoin ℚ {α}) * Polynomial.X +
            Polynomial.C (⟨α ^ 3 - 1, Subalgebra.sub_mem _
              (Subalgebra.pow_mem _ (IntermediateField.mem_adjoin_simple_self ℚ α) _)
              (Subalgebra.one_mem _)⟩ : IntermediateField.adjoin ℚ {α}) := by
        refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
        · have h_irred : ∀ (p : Polynomial (IntermediateField.adjoin ℚ {α})), p.degree = 3 →
            (∀ (γ : IntermediateField.adjoin ℚ {α}), p.eval γ ≠ 0) → Irreducible p := by
            intros p hp_deg hp_no_roots
            have h_irred : ∀ (f g : Polynomial (IntermediateField.adjoin ℚ {α})), f.degree > 0 →
                g.degree > 0 → p = f * g → False := by
              intros f g hf hg hp_eq
              have h_deg_f : f.degree = 1 ∨ g.degree = 1 := by
                have := congr_arg Polynomial.degree hp_eq
                norm_num [hp_deg] at this
                rw [Polynomial.degree_eq_natDegree (by aesop_cat), Polynomial.degree_eq_natDegree (by aesop_cat)] at *
                norm_cast at *
                omega
              rcases h_deg_f with (h | h) <;>
                obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one h <;> simp_all +decide
            constructor <;> contrapose! h_irred
            · exact absurd (Polynomial.degree_eq_zero_of_isUnit h_irred) (by aesop)
            · obtain ⟨a, b, rfl, ha, hb⟩ := h_irred
              exact ⟨a, b, not_le.mp fun ha' ↦ ha <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
                le_antisymm ha' <| le_of_not_gt fun ha'' ↦ by aesop, not_le.mp fun hb' ↦ hb <|
                Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm hb' <| le_of_not_gt fun hb'' ↦ by aesop,
                rfl, trivial⟩
          apply h_irred
          · refine Polynomial.degree_eq_of_le_of_coeff_ne_zero ?_ ?_
            · rw [Polynomial.degree_le_iff_coeff_zero]
              rintro (_ | _ | _ | _ | m) <;> simp +decide [Polynomial.coeff_eq_zero_of_natDegree_lt]
            · norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]
          · intro γ hγ
            have h_contra : γ.val ^ 3 + α * γ.val ^ 2 + α ^ 2 * γ.val + (α ^ 3 - 1) = 0 := by
              convert congr_arg Subtype.val hγ using 1
              norm_num
            exact cubic_factor_irreducible α hα ⟨γ, h_contra⟩
        · convert hβ using 1
          simp +decide [Polynomial.aeval_def]
        · erw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C,
            Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
            erw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
            by_cases h : α = 0 <;> simp +decide [h]
          all_goals simp_all +decide [Subtype.ext_iff]
          all_goals
            unfold q₄ at hα
            norm_num at hα
      rw [h_deg2, Polynomial.natDegree_add_C, Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;>
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
      · by_cases h : (C ⟨α, IntermediateField.subset_adjoin ℚ { α } (Set.mem_singleton α)⟩ :
          Polynomial (IntermediateField.adjoin ℚ { α })) = 0 <;> simp +decide [h]
      · exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) (by norm_num)
      · by_cases h : (C ⟨α, IntermediateField.subset_adjoin ℚ { α } (Set.mem_singleton α)⟩ :
          Polynomial (IntermediateField.adjoin ℚ { α })) = 0 <;> simp +decide [h]
    have := Module.finrank_mul_finrank (IntermediateField.adjoin ℚ { α })
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ { α }) { β }) q₄.SplittingField
    have h_min_poly_deg : Module.finrank (IntermediateField.adjoin ℚ {α})
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ {α}) {β}) = 3 := by
      rw [← h_min_poly_deg, IntermediateField.adjoin.finrank]
      exact Algebra.IsIntegral.isIntegral β
    exact h_min_poly_deg ▸ this ▸ dvd_mul_right _ _
  have h_deg_beta : 3 ∣ (Module.finrank ℚ q₄.SplittingField) := by
    exact dvd_trans h_deg_beta (by
      simpa using Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ { α }) q₄.SplittingField ▸ dvd_mul_left _ _)
  convert h_deg_beta using 1
  exact Gal.card_of_separable (q₄_irreducible.separable)

/-- Nat.card q₄.Gal divides 24. -/
private lemma card_gal_dvd_24 : Nat.card q₄.Gal ∣ 24 := by
  have h := card_gal_dvd_card_rootSet_factorial q₄
  have hcard : Fintype.card (q₄.rootSet ℂ) = 4 :=
    card_rootSet_eq_natDegree q₄ q₄_irreducible.separable (Irreducible.ne_zero q₄_irreducible)
      |>.trans q₄_natDegree
  rw [hcard] at h
  norm_num at h
  rwa [Nat.card_eq_fintype_card]

/-- 12 divides Nat.card q₄.Gal. -/
private lemma twelve_dvd_card_gal : 12 ∣ Nat.card q₄.Gal := by
  have h4 : 4 ∣ Nat.card q₄.Gal := by
    have := natDegree_dvd_card q₄_irreducible
    rw [q₄_natDegree] at this
    exact this
  have h3 := three_dvd_card_gal
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4

/-- A₄ (on Fin 4) has no subgroup of order 6. -/
private lemma no_order_six_subgroup_A4 :
    ∀ S : Finset (Equiv.Perm (Fin 4)),
    S.card = 6 →
    (∀ x ∈ S, Equiv.Perm.sign x = 1) →
    (1 ∈ S) →
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
    False := by native_decide

private instance : Fact ((q₄.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩

/-- Complex conjugation acts on the roots of q₄ as a permutation with support of size 2. -/
private lemma conj_support_card_eq_two :
    (Gal.galActionHom q₄ ℂ
      (Gal.restrict q₄ ℂ (Complex.conjAe.restrictScalars ℚ))).support.card = 2 := by
  have key := Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv q₄
  have hℂ : (q₄.rootSet ℂ).toFinset.card = 4 := by
    rw [Set.toFinset_card]
    exact (card_rootSet_eq_natDegree q₄ q₄_irreducible.separable
      (Irreducible.ne_zero q₄_irreducible)).trans q₄_natDegree
  have hℝ : (q₄.rootSet ℝ).toFinset.card = 2 := by
    rw [Set.toFinset_card]
    exact q₄_real_roots
  omega

/-
The Galois group order is not 12 (because complex conjugation gives an odd permutation
in the Galois group, but any subgroup of S₄ of order 12 is A₄ which has only even
permutations; this latter fact is equivalent to A₄ having no subgroup of order 6).
-/
set_option maxHeartbeats 800000 in
private lemma card_gal_ne_12 : Nat.card q₄.Gal ≠ 12 := by
  intro h_card
  have h_ker : (Nat.card (MonoidHom.ker (Equiv.Perm.sign.comp (Gal.galActionHom q₄ ℂ))) = 6) := by
    have h_ker : (Nat.card (MonoidHom.range (Equiv.Perm.sign.comp (Gal.galActionHom q₄ ℂ))) = 2) := by
      rw [Nat.card_eq_two_iff]
      simp +decide [Set.ext_iff]
      refine ⟨1, Gal.restrict q₄ ℂ (Complex.conjAe.restrictScalars ℚ), ?_, ?_⟩ <;> norm_num
      · have := conj_support_card_eq_two
        rw [Equiv.Perm.card_support_eq_two] at this
        obtain ⟨x, y, hxy, h⟩ := this
        simp +decide [h, hxy]
      · intro a
        cases' Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom q₄ ℂ a)) with h h <;>
          cases' Int.units_eq_one_or (Equiv.Perm.sign (Gal.galActionHom q₄ ℂ
            (Gal.restrict q₄ ℂ (Complex.conjAe.restrictScalars ℚ)))) with h' h' <;>
          simp +decide only [h, h']
        have := conj_support_card_eq_two
        simp_all +decide [Equiv.Perm.card_support_eq_two]
        obtain ⟨x, y, hxy, h⟩ := this
        simp_all +decide
    have := Subgroup.card_mul_index (MonoidHom.ker (Equiv.Perm.sign.comp (Gal.galActionHom q₄ ℂ)))
    simp_all +decide [Nat.mul_comm]
    rw [Subgroup.index_ker] at this
    simp_all +decide [Fintype.card_subtype]
    linarith
  obtain ⟨S, hS⟩ : ∃ S : Finset (Equiv.Perm (q₄.rootSet ℂ)),
      S.card = 6 ∧ (∀ x ∈ S, Equiv.Perm.sign x = 1) ∧ (1 ∈ S) ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) := by
    refine ⟨Finset.image (fun x : ↥ (MonoidHom.ker (Equiv.Perm.sign.comp (Gal.galActionHom q₄ ℂ))) ↦
      (Gal.galActionHom q₄ ℂ) x) (Finset.univ), ?_, ?_, ?_, ?_⟩ <;> simp_all +decide
    · rw [Finset.card_image_of_injective _ fun x y hxy ↦ by simpa using Gal.galActionHom_injective q₄ ℂ hxy,
        Finset.card_univ]
      aesop
    · exact ⟨1, by simp +decide⟩
    · exact fun a ha b hb ↦ ⟨a * b, by simp +decide [ha, hb], by simp +decide⟩
  obtain ⟨e, he⟩ : ∃ e : q₄.rootSet ℂ ≃ Fin 4, True := by
    have h_card : Fintype.card (q₄.rootSet ℂ) = 4 := by
      convert card_rootSet_eq_natDegree q₄ _ _
      · erw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
      · exact q₄_irreducible.separable
      · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num [q₄])
    exact ⟨Fintype.equivOfCardEq <| by simp +decide [h_card], trivial⟩
  refine no_order_six_subgroup_A4 (Finset.image (fun x : Equiv.Perm (q₄.rootSet ℂ) ↦ Equiv.permCongr e x) S)
    ?_ ?_ ?_ ?_ <;> simp_all +decide [Finset.card_image_of_injective, Function.Injective]
  · exact ⟨1, hS.2.2.1, by aesop⟩
  · exact fun a ha b hb ↦ ⟨a * b, hS.2.2.2 a ha b hb, by simp +decide⟩

private lemma card_gal_eq_24 : Nat.card q₄.Gal = 24 := by
  have h12 := twelve_dvd_card_gal
  have h24 := card_gal_dvd_24
  have hne := card_gal_ne_12
  have h_pos : 0 < Nat.card q₄.Gal := Nat.pos_of_dvd_of_pos h24 (by norm_num)
  have h_le : Nat.card q₄.Gal ≤ 24 := Nat.le_of_dvd (by norm_num) h24
  -- card ∈ {12, 24} since 12 | card and card | 24 and card ≤ 24
  interval_cases (Nat.card q₄.Gal) <;> simp_all

theorem IsInverseGalois.perm_fin_four : IsInverseGalois (Equiv.Perm (Fin 4)) := by
  refine ⟨q₄.SplittingField, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try infer_instance
  · apply IsGalois.mk
  · have h_galois : Nat.card q₄.Gal = 24 := card_gal_eq_24
    refine ⟨?_⟩
    -- The Galois group of the splitting field of `q₄` is isomorphic to a subgroup of `S₄`.
    have h_subgroup : ∃ (f : Gal(q₄.SplittingField/ℚ) →* Equiv.Perm (q₄.rootSet ℂ)), Function.Injective f :=
      ⟨_, Gal.galActionHom_injective q₄ ℂ⟩
    have h_card : Fintype.card (q₄.rootSet ℂ) = 4 := by
      convert card_rootSet_eq_natDegree q₄ _ _
      · erw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
      · exact q₄_irreducible.separable
      · exact ne_of_apply_ne (Polynomial.eval 0) (by norm_num [q₄])
    have h_iso : ∃ (f : Gal(q₄.SplittingField/ℚ) →* Equiv.Perm (Fin 4)), Function.Injective f := by
      have h_iso : Nonempty (Equiv.Perm (q₄.rootSet ℂ) ≃* Equiv.Perm (Fin 4)) := by
        exact ⟨by exact { Equiv.permCongr (Fintype.equivOfCardEq h_card) with map_mul' := fun _ _ ↦ by aesop }⟩
      exact ⟨h_iso.some.toMonoidHom.comp h_subgroup.choose, h_iso.some.injective.comp h_subgroup.choose_spec⟩
    have h_iso : Function.Bijective (h_iso.choose : Gal(q₄.SplittingField/ℚ) → Equiv.Perm (Fin 4)) := by
      have h_iso : Fintype.card (Gal(q₄.SplittingField/ℚ)) = Fintype.card (Equiv.Perm (Fin 4)) := by
        simp_all +decide [Fintype.card_perm]
        exact h_galois
      have hcs := (‹∃ f : Gal(q₄.SplittingField/ℚ) →* Equiv.Perm (Fin 4), Function.Injective f›).choose_spec
      exact ⟨hcs, Fintype.bijective_iff_injective_and_card _ |>.2 ⟨hcs, h_iso⟩ |>.2⟩
    exact MulEquiv.ofBijective _ h_iso

end
