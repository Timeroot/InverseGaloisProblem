/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Artin-Schreier Irreducibility

This file proves that the Artin-Schreier polynomial `X^p - X - a` is irreducible
over `𝔽_p` for any `a ∈ 𝔽_p*` (nonzero `a`).

## Main results

- `artinSchreier_irreducible`: `X^p - X - a` is irreducible over `𝔽_p` for `a ≠ 0`
- `artinSchreier_no_roots`: `X^p - X - a` has no roots in `𝔽_p` for `a ≠ 0`

## References

- Lang, S. "Algebra", Chapter VI, §6 (Artin-Schreier theory)
- Lidl, R. and Niederreiter, H. "Finite Fields", §3.4
-/

open Polynomial

noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The Artin-Schreier polynomial `X^p - X - C a` has no roots in `𝔽_p`
when `a ≠ 0`. This is because `x^p - x = 0` for all `x ∈ 𝔽_p`. -/
theorem artinSchreier_no_roots (a : ZMod p) (ha : a ≠ 0) :
    ∀ x : ZMod p, Polynomial.eval x (X ^ p - X - C a) ≠ 0 := by
  simp +contextual [ha]

/-- `X^p - X - C a` is separable over `𝔽_p`. -/
lemma artinSchreier_separable (a : ZMod p) :
    Polynomial.Separable (X ^ p - X - C a : Polynomial (ZMod p)) := by
  apply IsCoprime.symm
  norm_num [Polynomial.derivative_pow]
  exact isCoprime_one_left.neg_left

/-- If `α` is a root of `X^p - X - a`, then `α + 1` is also a root. -/
lemma artinSchreier_root_shift {K : Type*} [Field K] [Algebra (ZMod p) K]
    (a : ZMod p) (α : K)
    (hα : Polynomial.aeval α (X ^ p - X - C a : Polynomial (ZMod p)) = 0) :
    Polynomial.aeval (α + 1) (X ^ p - X - C a : Polynomial (ZMod p)) = 0 := by
  simp_all [map_sub, map_pow, sub_eq_zero]
  have h_frobenius : ∀ (x y : K), (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    have h_char : ringChar K = p := by
      have h_char : ringChar (ZMod p) = p := by
        rw [ZMod.ringChar_zmod_n]
      convert h_char using 1
      exact Eq.symm (Algebra.ringChar_eq (ZMod p) K)
    have := ringChar.of_eq h_char
    simp [add_pow_char]
  simp_all

/-
The Frobenius endomorphism maps roots of a polynomial over 𝔽_p to roots.
If g ∈ 𝔽_p[X] and g(β) = 0 in an extension K, then g(β^p) = 0.
This is because g(β^p) = g(β)^p = 0^p = 0 in characteristic p.
-/
lemma frobenius_preserves_roots_of_zmod_poly
    {K : Type*} [Field K] [Algebra (ZMod p) K]
    (g : Polynomial (ZMod p)) (β : K)
    (hβ : Polynomial.aeval β (g.map (algebraMap (ZMod p) K)) = 0) :
    Polynomial.aeval (β ^ p) (g.map (algebraMap (ZMod p) K)) = 0 := by
      -- `g (β ^ p) = g β ^ p` via the Frobenius endomorphism.
      have h_eval : (Polynomial.eval (β ^ p) (Polynomial.map (algebraMap (ZMod p) K) g)) =
          (Polynomial.eval β (Polynomial.map (algebraMap (ZMod p) K) g)) ^ p := by
        have h_frobenius : ∀ x y : K, (x + y) ^ p = x ^ p + y ^ p := by
          have h_char : ringChar K = p := by
            have h_char : ringChar K = ringChar (ZMod p) := by
              grind only [Algebra.ringChar_eq]
            rw [h_char, ZMod.ringChar_zmod_n]
          have := ringChar.of_eq h_char
          simp [add_pow_char]
        simp [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        induction' g.support using Finset.induction
        · simp_all [mul_comm]
          rw [zero_pow hp.1.ne_zero]
        · simp_all [mul_comm]
          simp [mul_pow, ← pow_mul]
          simp [mul_comm, ← map_pow]
      simp_all [Polynomial.aeval_def]
      exact hp.1.ne_zero

/-
The degree of X^p - X - C a is p for p prime.
-/
lemma artinSchreier_natDegree (a : ZMod p) :
    (X ^ p - X - C a : Polynomial (ZMod p)).natDegree = p := by
      rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [hp.1.one_lt]

/-
X^p - X - C a is monic.
-/
lemma artinSchreier_monic (a : ZMod p) :
    (X ^ p - X - C a : Polynomial (ZMod p)).Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff_sub_of_degree_lt]
      · rw [Polynomial.leadingCoeff_sub_of_degree_lt] <;> norm_num [hp.1.one_lt]
      · rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num [hp.1.one_lt]
        exact lt_of_le_of_lt Polynomial.degree_C_le (WithBot.coe_lt_coe.mpr hp.1.pos)

/-
If a polynomial over an integral domain has n distinct roots, its degree is at least n.
-/
lemma natDegree_ge_of_distinct_roots {R : Type*} [CommRing R] [IsDomain R]
    (g : Polynomial R) (hg : g ≠ 0) (S : Finset R)
    (hS : ∀ x ∈ S, Polynomial.IsRoot g x) :
    S.card ≤ g.natDegree := by
      simp_all [Polynomial.eval_eq_sum_range]
      contrapose! hS
      by_contra! h
      -- Let `f` be the polynomial `∑ i ∈ range (g.natDegree + 1), C (g.coeff i) * X ^ i`.
      set f : Polynomial R := ∑ i ∈ Finset.range (g.natDegree + 1), Polynomial.C (g.coeff i) * Polynomial.X ^ i
      -- `f` has degree at most `g.natDegree`, and `S` has more than `g.natDegree` elements, so `f` must be zero.
      have h_f_zero : f = 0 := by
        refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq S ?_ ?_
        · rw [sub_zero, Polynomial.degree_lt_iff_coeff_zero]
          simp +zetaDelta at *
          intro m hm1 hm2
          omega
        · simp +zetaDelta at *
          simpa [Polynomial.eval_finset_sum] using h
      replace h_f_zero := congr_arg (fun q ↦ Polynomial.coeff q g.natDegree) h_f_zero
      simp_all only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_range, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte,
        coeff_natDegree, coeff_zero, leadingCoeff_eq_zero, f]

/-
In ZMod p, if a ≠ 0, then the map k ↦ k • a is injective on {0, ..., p-1}.
-/
lemma zmod_smul_injective (a : ZMod p) (ha : a ≠ 0) :
    Function.Injective (fun k : ZMod p => k * a) := by
      exact fun x y hxy ↦ mul_right_cancel₀ ha hxy

/-
Key lemma: if g divides X^p - X - C a (with a ≠ 0) and g is monic irreducible,
then g has degree p.

Proof: Let β be a root of g in an extension. Since g | f and f(β) = 0,
we have β^p = β + a. The Frobenius σ(β) = β^p = β + a is also a root of g
(since σ preserves roots of polynomials with F_p coefficients).
Iterating: β, β+a, β+2a, ..., β+(p-1)a are all roots of g.
Since a ≠ 0 in F_p (a field of prime order), {ka : k ∈ F_p} = F_p.
So g has p distinct roots, hence deg g ≥ p. Since g | f and deg f = p,
we get deg g = p.
-/
lemma artinSchreier_factor_degree (a : ZMod p) (ha : a ≠ 0)
    (g : Polynomial (ZMod p)) (hg_irr : Irreducible g)
    (hg_dvd : g ∣ (X ^ p - X - C a : Polynomial (ZMod p))) :
    g.natDegree = p := by
      -- `g` divides `X ^ (p ^ d) - X` where `d = g.natDegree`.
      have h_div : g ∣ (X ^ (p ^ (g.natDegree)) - X : Polynomial (ZMod p)) := by
        -- Let `K` be the field extension of `𝔽_p` generated by a root of `g`.
        set K := AdjoinRoot g
        -- Since `g` is irreducible, `K` is a finite field with `p ^ g.natDegree` elements.
        have hK_card : Fintype K := by
          have hK_card : FiniteDimensional (ZMod p) K := by
            exact Module.Basis.finiteDimensional_of_finite (PowerBasis.basis (AdjoinRoot.powerBasis hg_irr.ne_zero))
          convert (Fintype.ofEquiv (Fin (Module.finrank (ZMod p) K) → ZMod p) ?_)
          exact ((Module.finBasis (ZMod p) K).equivFun).toEquiv.symm
        have hK_card_eq : Fintype.card K = p ^ g.natDegree := by
          have hK_card_eq : Fintype.card K = Fintype.card (Fin (g.natDegree) → ZMod p) := by
            apply Fintype.card_congr
            have hK_card_eq : K ≃ₗ[ZMod p] (Fin (g.natDegree) → ZMod p) := by
              exact (AdjoinRoot.powerBasis hg_irr.ne_zero).basis.equivFun
            exact hK_card_eq.toEquiv
          simp_all
        -- Every element `x` of `K` satisfies `x ^ (p ^ g.natDegree) = x`.
        have hK_poly : ∀ x : K, x ^ (p ^ g.natDegree) = x := by
          simp [← hK_card_eq]
          have := Fact.mk hg_irr
          exact FiniteField.pow_card
        rw [← AdjoinRoot.mk_eq_zero]
        simp_all
      -- Since `g` divides `X ^ p - X - C a`, it also divides `X ^ (p ^ k) - X - C (k * a)` for every `k`.
      have h_div_shift : g ∣ (X ^ (p ^ (g.natDegree)) - X - C (g.natDegree * a) : Polynomial (ZMod p)) := by
        suffices h : ∀ k : ℕ, g ∣ (X ^ (p ^ k) - X - C (k * a) : Polynomial (ZMod p)) from h _
        intro k
        induction' k with k ih
        · simp_all
        simp_all
        have h_div_shift : g ∣ ((X ^ (p ^ k)) ^ p - X ^ p - C (k * a) : Polynomial (ZMod p)) := by
          convert ih.trans (show X ^ p ^ k - X - ↑k * C a ∣ (X ^ p ^ k) ^ p - X ^ p - C (↑k * a) from ?_) using 1
          have h_div_shift : (X ^ (p ^ k) - X - C (k * a) : Polynomial (ZMod p)) ∣
              ((X ^ (p ^ k)) ^ p - X ^ p - C (k * a) ^ p : Polynomial (ZMod p)) := by
            convert sub_dvd_pow_sub_pow (X ^ p ^ k) (X + C (k * a)) p using 1
            · ring
            · simp [add_pow_char, sub_sub]
          convert h_div_shift using 1
          · norm_num [← Polynomial.C_pow, ← Polynomial.C_mul]
          · rw [← map_pow, ZMod.pow_card]
        convert dvd_add h_div_shift hg_dvd using 1
        ring_nf
        norm_num [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      have := dvd_sub h_div h_div_shift
      simp_all
      -- `g` divides the constant `C (g.natDegree * a)`; since `g` is not a unit, `p ∣ g.natDegree`.
      have h_natDegree_mul_p : p ∣ g.natDegree := by
        contrapose! this
        -- `C (g.natDegree : ZMod p)` is a unit, since `g.natDegree ≠ 0` in `ZMod p`.
        have h_unit : IsUnit (Polynomial.C (g.natDegree : ZMod p)) := by
          exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr <| by rwa [Ne.eq_def, ZMod.natCast_eq_zero_iff])
        exact fun h ↦ hg_irr.not_isUnit <| isUnit_of_dvd_unit h <| by simpa using h_unit
      have := Polynomial.natDegree_le_of_dvd hg_dvd
      simp_all
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] at this <;>
        simp_all [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, hp.1.one_lt]
      refine le_antisymm (this ?_) (Nat.le_of_dvd ?_ h_natDegree_mul_p)
      · apply ne_of_apply_ne Polynomial.natDegree
        erw [Polynomial.natDegree_sub_C]
        erw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num <;> linarith [hp.1.one_lt]
      · exact Polynomial.natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg_irr

/-
The minimal polynomial of a root of X^p - X - C a over F_p has degree p.
Since the extension degree divides p (prime), it's either 1 or p.
Since there are no roots in F_p, it's p.

The Frobenius iteration: if α^p = α + a, then α^{p^k} = α + k·a.
This follows by induction using add_pow_char.
-/
lemma frobenius_iterate {K : Type*} [Field K] [Algebra (ZMod p) K]
    (a : ZMod p) (α : K)
    (hα : α ^ p = α + algebraMap (ZMod p) K a) :
    ∀ k : ℕ, α ^ (p ^ k) = α + algebraMap (ZMod p) K (k * a) := by
      intro k
      induction' k with k ih
      · simp_all
      have h_frobenius : ∀ x y : K, (x + y) ^ p = x ^ p + y ^ p := by
        intro x y
        have h_char : ringChar K = p := by
          grind only [ringChar.spec, Algebra.ringChar_eq, ringChar.eq]
        have := ringChar.of_eq h_char
        simp [add_pow_char]
      simp_all [pow_succ, pow_mul]
      rw [mul_pow, add_mul, one_mul, add_assoc]
      simp [← map_pow]
      rw [add_comm, ← map_natCast (algebraMap (ZMod p) K)]
      rw [← map_pow, ZMod.pow_card]

lemma artinSchreier_minpoly_degree (a : ZMod p) (ha : a ≠ 0)
    (α : AlgebraicClosure (ZMod p))
    (hα : Polynomial.aeval α (X ^ p - X - C a : Polynomial (ZMod p)) = 0) :
    (minpoly (ZMod p) α).natDegree = p := by
      -- Since `α` is a root of `X ^ p - X - C a`, its minimal polynomial divides `X ^ p - X - C a`.
      have h_div : (minpoly (ZMod p) α) ∣ (Polynomial.X ^ p - Polynomial.X - Polynomial.C a) :=
        minpoly.dvd (ZMod p) α hα
      refine artinSchreier_factor_degree a ha (minpoly (ZMod p) α) ?_ h_div
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral α)

/-
The Artin-Schreier polynomial `X^p - X - C a` is irreducible over `𝔽_p`
for any nonzero `a ∈ 𝔽_p`.

**Proof**: Let α be a root of f = X^p - X - C a in the algebraic closure.
The minimal polynomial of α over F_p divides f. Its degree divides [F_p(α):F_p],
which divides deg(f) = p. Since p is prime, deg(minpoly) = 1 or p.
Since there are no roots in F_p (by artinSchreier_no_roots), deg(minpoly) ≠ 1.
So deg(minpoly) = p = deg(f). Since both are monic and minpoly | f, we get
minpoly = f. Since the minimal polynomial is irreducible, f is irreducible.
-/
theorem artinSchreier_irreducible (a : ZMod p) (ha : a ≠ 0) :
    Irreducible (X ^ p - X - C a : Polynomial (ZMod p)) := by
      -- Let `f = X ^ p - X - C a`.
      set f : Polynomial (ZMod p) := X ^ p - X - C a
      -- The minimal polynomial of any root `α` of `f` equals `f`.
      have h_min_div : ∀ α : AlgebraicClosure (ZMod p), Polynomial.aeval α f = 0 → minpoly (ZMod p) α = f := by
        intro α hα
        have h_deg : (minpoly (ZMod p) α).natDegree = p :=
          artinSchreier_minpoly_degree a ha α hα
        have h_monic : (minpoly (ZMod p) α).Monic :=
          minpoly.monic (Algebra.IsIntegral.isIntegral α)
        have h_div : minpoly (ZMod p) α ∣ f :=
          minpoly.dvd (ZMod p) α hα
        have h_eq : minpoly (ZMod p) α = f := by
          obtain ⟨g, hg⟩ := h_div
          have h_deg_f : f.natDegree = p := by
            rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [hp.1.one_lt]
          have h_deg_g : g.natDegree = 0 := by
            by_cases hg_zero : g = 0 <;> simp_all [Polynomial.natDegree_mul']
          have h_g_monic : g.Monic := by
            apply_fun Polynomial.leadingCoeff at hg
            simp_all [Polynomial.leadingCoeff_mul]
            rw [Polynomial.Monic, ← hg, Polynomial.leadingCoeff, h_deg_f]
            simp +zetaDelta at *
            rw [Polynomial.coeff_X, Polynomial.coeff_C, if_neg (by linarith [hp.1.one_lt]),
              if_neg (by linarith [hp.1.one_lt])]
            norm_num
          have h_g_one : g = 1 :=
            eq_one_of_monic_natDegree_zero h_g_monic h_deg_g
          subst h_g_one
          simp_all
        exact h_eq
      -- Let α be a root of f in the algebraic closure.
      obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure (ZMod p), Polynomial.aeval α f = 0 := by
        have h_root : ∃ α : AlgebraicClosure (ZMod p),
            Polynomial.eval α (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0 := by
          apply IsAlgClosed.exists_root
          rw [Polynomial.degree_map, Polynomial.degree_sub_C] <;>
            rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num [hp.1.one_lt]
          · exact hp.1.ne_zero
          · exact hp.1.pos
        simpa [Polynomial.eval_map] using h_root
      have := minpoly.irreducible (show IsIntegral (ZMod p) α from ?_)
      · simp_all
      · exact Algebra.IsIntegral.isIntegral α

/-- As a corollary, `X^p - X - 1` is irreducible over `𝔽_p` for any prime `p`. -/
theorem artinSchreier_one_irreducible :
    Irreducible (X ^ p - X - 1 : Polynomial (ZMod p)) := by
  exact artinSchreier_irreducible 1 one_ne_zero

end