/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.HilbertIrreducibility
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# The explicit `Aₙ`-family (Serre §4.5) — algebraic half

The `sorry` in `Hilbert/Alternating.lean` (`exists_alternating_resolvent_family`) needs a
*regular `Aₙ`-extension of `ℚ(T)`*.  Rather than Mestre's genus-`0` construction, we use the
**classical explicit family** described in Serre, *Topics in Galois Theory*, §4.5 (attributed
there to Hilbert):

> Take `f(X, T) = Xⁿ − X^{n-1} − T` (`anBaseFamily n`).  Its ramification type is
> `(n, n−1, 2)`: an `n`-cycle at `X = ∞`, an `(n−1)`-cycle at `X = 0`, and a single
> transposition at the finite critical value `α = f(1 − 1/n)` — hence Galois group `Sₙ`.
> The discriminant (in `X`) is, up to square factors, `∼ nT(T − 1)` (`n` odd) or
> `∼ (n−1)(T − 1)` (`n` even), so the curve `D² = Δ` has genus `0`.  Substituting `T` by the
> rational parametrisation of that conic yields a family whose discriminant is *identically a
> square* in `ℚ[T]`, and whose Galois group therefore descends to `Aₙ` (the "double-group
> trick", Lemma 4.5.1).

This file develops the **algebraic half** of the decomposition: the family, its degree/monic
bookkeeping, cofinite separability of the specialisations, and (as documented `sorry`s) the
square-discriminant certificate that supplies the per-`t` `discSq` conjunct.  The **analytic
half** (irreducibility and absolute irreducibility of the descended resolvent, i.e. the
monodromy computation) lives in `Hilbert/AlternatingFamilyAnalytic.lean`.

The `Aₙ`-orbit resolvent and its descent to `ℚ[e₁,…,eₙ][δ]` are already handled by
`Resolvent/AlternatingInvariants.lean` and `Resolvent/AlternatingResolventDescent.lean`.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

/-- **The base ramification family** `f(X, T) = Xⁿ − X^{n-1} − T`, as an element of `ℚ[T][X]`
(outer variable `X`; the coefficient variable is `T = C X`).  This is Serre's `(n, n−1, 2)`
family whose Galois group over `ℚ(T)` is `Sₙ`; the `Aₙ`-family is obtained from it by the
square-discriminant substitution. -/
def anBaseFamily (n : ℕ) : Polynomial (Polynomial ℚ) := X ^ n - X ^ (n - 1) - C X

/-- **[algebraic leaf]** `f = Xⁿ − X^{n-1} − T` is monic for `n ≥ 2`. -/
theorem anBaseFamily_monic (n : ℕ) (hn : 2 ≤ n) : (anBaseFamily n).Monic := by
  have h : anBaseFamily n = X ^ n - (X ^ (n - 1) + C X) := by unfold anBaseFamily; ring
  rw [h]
  apply monic_X_pow_sub
  have hle : (X ^ (n - 1) + C X : Polynomial (Polynomial ℚ)).degree ≤ (↑(n - 1)) := by
    refine le_trans (degree_add_le _ _) ?_
    rw [degree_X_pow]
    exact max_le le_rfl (le_trans degree_C_le (by exact_mod_cast Nat.zero_le (n - 1)))
  refine lt_of_le_of_lt hle ?_
  exact_mod_cast (by omega : n - 1 < n)

/-- **[algebraic leaf]** `f = Xⁿ − X^{n-1} − T` has `X`-degree `n` for `n ≥ 2`. -/
theorem anBaseFamily_natDegree (n : ℕ) (hn : 2 ≤ n) : (anBaseFamily n).natDegree = n := by
  simp [anBaseFamily]
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simp
    omega

/-- **[algebraic leaf]** The `X`-derivative of the base family is
`f′ = n·X^{n-1} − (n−1)·X^{n-2}`.  Its critical points (`X = 0` of multiplicity `n − 2` and
`X = (n−1)/n`) drive the `(n, n−1, 2)` ramification type. -/
theorem anBaseFamily_derivative (n : ℕ) (hn : 2 ≤ n) :
    derivative (anBaseFamily n) = C (n : Polynomial ℚ) * X ^ (n - 1)
      - C ((n : Polynomial ℚ) - 1) * X ^ (n - 2) := by
  simp [anBaseFamily, derivative_pow]
  simp (config := { decide := true }) only [show n - 1 - 1 = n - 2 by omega]
  congr 1
  simp [Nat.cast_sub (by omega : 1 ≤ n)]

/-- **[algebraic leaf]** `f(t, X) = Xⁿ − X^{n-1} − t` is separable for all but finitely many
`t ∈ ℤ` (the exceptions are the finitely many roots of the discriminant, a nonzero polynomial
in `t`). -/
theorem anBaseFamily_separable_cofinite (n : ℕ) (hn : 2 ≤ n) :
    {t : ℤ | ¬ (specialize (anBaseFamily n) t).Separable}.Finite := by
  -- The roots of the derivative `f' = n·X^{n-1} − (n−1)·X^{n-2}` are finite.
  have hDisc_roots_finite : Set.Finite (SetLike.coe (Polynomial.roots
      (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1)
        - Polynomial.C ((n : ℚ) - 1) * Polynomial.X ^ (n - 2) : Polynomial ℚ)).toFinset) :=
    Set.toFinite _
  have hD_roots_finite : Set.Finite {t : ℚ | ∃ r : AlgebraicClosure ℚ,
      Polynomial.eval r (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1)
          - Polynomial.C ((n : ℚ) - 1) * Polynomial.X ^ (n - 2))) = 0 ∧
      Polynomial.eval r (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (Polynomial.X ^ n - Polynomial.X ^ (n - 1) - Polynomial.C (t : ℚ))) = 0} := by
    refine Set.Finite.subset (hDisc_roots_finite.image (fun r : ℚ ↦ r ^ n - r ^ (n - 1))) ?_
    intro t ht
    obtain ⟨r, hr₁, hr₂⟩ := ht
    -- `r` is a root of `f'`, hence `r = 0` or `r = (n-1)/n`; both are rational.
    have h_rational : ∃ q : ℚ, r = algebraMap ℚ (AlgebraicClosure ℚ) q ∧
        Polynomial.eval q (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1)
          - Polynomial.C ((n : ℚ) - 1) * Polynomial.X ^ (n - 2)) = 0 := by
      -- Simplify the root condition `f'(r) = 0`.
      have hr : (n : AlgebraicClosure ℚ) * r ^ (n - 1)
          - ((n : AlgebraicClosure ℚ) - 1) * r ^ (n - 2) = 0 := by
        have h := hr₁
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at h
        rw [map_natCast, map_sub, map_natCast, map_one] at h
        exact h
      -- Factor `r^{n-2}·(n·r − (n−1)) = 0`.
      have hm : n - 1 = (n - 2) + 1 := by omega
      have hfact : r ^ (n - 2)
          * ((n : AlgebraicClosure ℚ) * r - ((n : AlgebraicClosure ℚ) - 1)) = 0 := by
        rw [hm, pow_succ] at hr
        linear_combination hr
      rcases mul_eq_zero.mp hfact with h0 | h0
      · -- `r^{n-2} = 0`: forces `r = 0` (and `n ≥ 3`).
        rcases eq_or_ne (n - 2) 0 with he | he
        · rw [he, pow_zero] at h0; exact absurd h0 one_ne_zero
        · have hr0 : r = 0 := (pow_eq_zero_iff he).mp h0
          refine ⟨0, by rw [hr0]; simp, ?_⟩
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          rw [zero_pow (by omega : n - 1 ≠ 0), zero_pow he]
          ring
      · -- `n·r − (n−1) = 0`: forces `r = (n−1)/n`.
        have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
        have hrval : r = ((n : AlgebraicClosure ℚ) - 1) / (n : AlgebraicClosure ℚ) := by
          field_simp
          linear_combination h0
        refine ⟨((n : ℚ) - 1) / (n : ℚ), ?_, ?_⟩
        · rw [hrval, map_div₀, map_sub, map_natCast, map_one]
        · have hn0q : (n : ℚ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
          simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_X, Polynomial.eval_C]
          rw [hm, pow_succ]
          field_simp
          ring
    obtain ⟨q, rfl, hq⟩ := h_rational
    have hpoly_ne : (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1)
        - Polynomial.C ((n : ℚ) - 1) * Polynomial.X ^ (n - 2) : Polynomial ℚ) ≠ 0 := by
      intro h
      have hc := congr_arg (fun p ↦ Polynomial.coeff p (n - 1)) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_zero] at hc
      rw [if_neg (by omega : ¬ (n - 1 = n - 2))] at hc
      simp only [if_true, mul_one, mul_zero, sub_zero] at hc
      exact absurd (Nat.cast_eq_zero.mp hc) (by omega)
    refine ⟨q, ?_, ?_⟩
    · rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hpoly_ne, hq⟩
    · -- t = q^n - q^(n-1)
      have h := hr₂
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
      have hinj := (algebraMap ℚ (AlgebraicClosure ℚ)).injective
      apply hinj
      simp only [map_sub, map_pow]
      linear_combination h
  refine Set.Finite.subset (hD_roots_finite.preimage (f := fun t : ℤ ↦ (t : ℚ)) ?_) ?_
  · intro x hx y hy hxy
    simpa using hxy
  · intro t ht
    simp only [Set.mem_setOf_eq] at ht
    rw [Set.mem_preimage, Set.mem_setOf_eq]
    contrapose! ht
    have h_separable : ∀ x : AlgebraicClosure ℚ,
        Polynomial.eval x (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
          (specialize (anBaseFamily n) t)) = 0 →
        Polynomial.eval x (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
          (derivative (specialize (anBaseFamily n) t))) ≠ 0 := by
      intro x hx hx'
      apply ht x
      · -- f'(x) = 0
        have hd : derivative (specialize (anBaseFamily n) t)
            = Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1)
              - Polynomial.C ((n : ℚ) - 1) * Polynomial.X ^ (n - 2) := by
          rw [specialize, Polynomial.derivative_map, anBaseFamily_derivative n hn]
          simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
        rw [hd] at hx'
        exact hx'
      · -- f(t)(x) = 0
        have hf : specialize (anBaseFamily n) t
            = Polynomial.X ^ n - Polynomial.X ^ (n - 1) - Polynomial.C (t : ℚ) := by
          simp [specialize, anBaseFamily]
        rw [hf] at hx
        exact hx
    rw [Polynomial.Separable]
    apply isCoprime_of_irreducible_dvd
    · unfold specialize anBaseFamily
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      intro h
      obtain ⟨h1, _⟩ := h
      replace h1 := congr_arg (fun p ↦ Polynomial.coeff p n) h1
      rcases n with (_ | _ | n) <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · intro z hz hz' hz''
      contrapose! h_separable
      simp_all [Polynomial.eval_map]
      have hdeg : (z.map (algebraMap ℚ (AlgebraicClosure ℚ))).degree ≠ 0 := by
        rw [Polynomial.degree_map]
        exact hz.degree_pos.ne'
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
      use x
      simp_all [Polynomial.eval₂_eq_eval_map]
      refine ⟨?_, ?_⟩
      · simpa [hx] using
          Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap ℚ (AlgebraicClosure ℚ)) x hz' hx
      · simpa [hx] using
          Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap ℚ (AlgebraicClosure ℚ)) x hz'' hx

/-!
The `Aₙ`-forcing square-discriminant certificate has moved to `Hilbert/AlternatingFamilyDisc.lean`,
where it is developed around the **concrete** substituted family `serreAnFamily` (rather than a
decoupled existential `∃ F`), so that it composes with the resolvent side into
`exists_alternating_resolvent_family`.  See `serreAnFamily_disc_isSquare_of_separable`.
-/

end AlternatingFamily

end
