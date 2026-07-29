/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamily
import InverseGalois.Hilbert.AlternatingFamilyDisc
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# Serre's explicit `Aₙ`-family (Serre §4.5) — the **odd-`n`** conic-parametrised family

The sibling file `AlternatingFamilyDisc.lean` develops the **even-`n`** family `serreAnFamily`
whose `X`-discriminant is `nⁿ t² qⁿ⁻²` — a rational square exactly when `n` is even.  For **odd**
`n` the base family `(n−1)Xⁿ − nX^{n-1} + T` has `X`-discriminant `∼ (−1)^{(n−1)/2}·n·T(T−1)` (a
genuine conic), so `T` must be rationally parametrised `T = c/(c−U²)`.  Multiplying through by
`(k−U²)ⁿ` and rescaling the variable clears denominators and lands back in `ℚ[U][Y]`, giving the
**monic-in-`Y`** family

  `serreAnFamilyOdd n = Yⁿ − (n/(n−1))·(k−U²)·Y^{n-1} + (k/(n−1))·(k−U²)^{n-1}`,

where `k = (−1)^{(n−1)/2}·n`.  Its `X`-discriminant is *identically a square in `ℚ[U]`* for odd
`n`; every integer specialization therefore has square discriminant and Galois group `⊆ Aₙ`.

This file mirrors `AlternatingFamilyDisc.lean` line-for-line, with the substitution `1 ↦ (k−U²)`
for the second critical point and `Even n ↦ Odd n`.  It is out-of-graph (not in the default
`lake build`), exactly like its even sibling.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

/-- **Serre's explicit odd-`n` `Aₙ`-family**
`Yⁿ − (n/(n−1))·(k−U²)·Y^{n-1} + (k/(n−1))·(k−U²)^{n-1}` with `k = (−1)^{(n−1)/2}·n`, monic in
`Y`, as an element of `ℚ[U][Y]` (outer variable `Y`, inner variable `U = C X`). -/
def serreAnFamilyOdd (n : ℕ) : Polynomial (Polynomial ℚ) :=
  X ^ n
    - C (C ((n : ℚ) / ((n : ℚ) - 1)) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2)) * X ^ (n - 1)
    + C (C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
          * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1))

/-- Rewriting of `serreAnFamilyOdd` as `Yⁿ − (…)`. -/
theorem serreAnFamilyOdd_eq (n : ℕ) :
    serreAnFamilyOdd n = X ^ n
      - (C (C ((n : ℚ) / ((n : ℚ) - 1)) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2)) * X ^ (n - 1)
        - C (C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
              * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1))) := by
  unfold serreAnFamilyOdd
  ring

/-- **[algebraic leaf]** `serreAnFamilyOdd n` is monic (in `Y`) for `n ≥ 2`. -/
theorem serreAnFamilyOdd_monic (n : ℕ) (hn : 2 ≤ n) : (serreAnFamilyOdd n).Monic := by
  rw [serreAnFamilyOdd_eq]
  apply monic_X_pow_sub
  have hle : (C (C ((n : ℚ) / ((n : ℚ) - 1)) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2))
        * X ^ (n - 1)
      - C (C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1))
            * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ (n - 1))
        : Polynomial (Polynomial ℚ)).degree ≤ (↑(n - 1)) := by
    apply le_trans (degree_sub_le _ _)
    apply max_le
    · exact degree_C_mul_X_pow_le _ _
    · exact le_trans degree_C_le (by exact_mod_cast Nat.zero_le (n - 1))
  apply lt_of_le_of_lt hle
  exact_mod_cast (by omega : n - 1 < n)

/-- **[algebraic leaf]** `serreAnFamilyOdd n` has `Y`-degree `n` for `n ≥ 2`. -/
theorem serreAnFamilyOdd_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamilyOdd n).natDegree = n := by
  rw [serreAnFamilyOdd_eq]
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · rw [natDegree_X_pow]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
      rw [natDegree_X_pow]
      omega
    · rw [natDegree_C]
      omega

/-- **[algebraic leaf]** The `Y`-derivative of `serreAnFamilyOdd` is
`n·Y^{n-1} − n·(k−U²)·Y^{n-2}`.  Its critical points are `Y = 0` and `Y = (k−U²)`. -/
theorem serreAnFamilyOdd_derivative (n : ℕ) (hn : 2 ≤ n) :
    derivative (serreAnFamilyOdd n) = C ((n : Polynomial ℚ)) * X ^ (n - 1)
      - C ((n : Polynomial ℚ) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2)) * X ^ (n - 2) := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have e1 : (↑(n - 1) : Polynomial ℚ) = C (↑(n - 1) : ℚ) := (map_natCast C (n - 1)).symm
  have e2 : ((n : Polynomial ℚ)) = C (n : ℚ) := (map_natCast C n).symm
  have hscal : (C ((n : ℚ) / ((n : ℚ) - 1)) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2))
        * (↑(n - 1) : Polynomial ℚ)
      = (n : Polynomial ℚ) * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) := by
    rw [e1, e2, mul_right_comm, ← C_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
      div_mul_cancel₀ _ hne]
  unfold serreAnFamilyOdd
  simp only [derivative_add, derivative_sub, derivative_C_mul, derivative_C,
    derivative_X_pow, add_zero]
  rw [show n - 1 - 1 = n - 2 by omega]
  congr 1
  rw [← mul_assoc, ← C_mul, hscal]

/-- **[algebraic leaf]** The explicit integer specialization of `serreAnFamilyOdd n`
(evaluating `U ↦ t`, sending `k−U² ↦ k−t²`). -/
theorem specialize_serreAnFamilyOdd (n : ℕ) (t : ℤ) :
    specialize (serreAnFamilyOdd n) t
      = X ^ n
        - C ((n : ℚ) / ((n : ℚ) - 1) * ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2)) * X ^ (n - 1)
        + C (((-1 : ℚ) ^ ((n - 1) / 2) * n) / ((n : ℚ) - 1)
              * ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2) ^ (n - 1)) := by
  unfold specialize serreAnFamilyOdd
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, coe_evalRingHom,
    eval_sub, eval_mul, eval_pow, eval_C,
    eval_X]

/-- **[algebraic leaf]** Every integer specialization of `serreAnFamilyOdd n` is monic. -/
theorem specialize_serreAnFamilyOdd_monic (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    (specialize (serreAnFamilyOdd n) t).Monic :=
  specialize_monic _ (serreAnFamilyOdd_monic n hn) t

/-- **[algebraic leaf]** Every integer specialization of `serreAnFamilyOdd n` has degree `n`. -/
theorem specialize_serreAnFamilyOdd_natDegree (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    (specialize (serreAnFamilyOdd n) t).natDegree = n := by
  unfold specialize
  rw [(serreAnFamilyOdd_monic n hn).natDegree_map, serreAnFamilyOdd_natDegree n hn]

/-- **[algebraic leaf]** The `Y`-derivative of every integer specialization is
`n·Y^{n-1} − n·(k−t²)·Y^{n-2}`. -/
theorem specialize_serreAnFamilyOdd_derivative (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    derivative (specialize (serreAnFamilyOdd n) t)
      = C (n : ℚ) * X ^ (n - 1)
        - C ((n : ℚ) * ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2)) * X ^ (n - 2) := by
  rw [specialize, derivative_map, serreAnFamilyOdd_derivative n hn]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_natCast]

/-- **[algebraic leaf — separability]** `serreAnFamilyOdd n |_t` is separable for all but finitely
many `t ∈ ℤ`.  The exceptions lie in `{t | t² = k} ∪ {t | t = 0}` (the collision loci `k−t² = 0`
and `t = 0`), both finite. -/
theorem serreAnFamilyOdd_separable_cofinite (n : ℕ) (hn : 2 ≤ n) :
    {t : ℤ | ¬ (specialize (serreAnFamilyOdd n) t).Separable}.Finite := by
  set φ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hφinj : Function.Injective φ := φ.injective
  set kq : ℚ := (-1 : ℚ) ^ ((n - 1) / 2) * n with hkq
  have hkne : kq ≠ 0 := by
    rw [hkq]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (by omega : n ≠ 0))
  have hne1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  -- `{t | t² = kq}` is finite (roots of `X² − C kq`).
  have hfin_quad : {t : ℤ | (t : ℚ) ^ 2 = kq}.Finite := by
    have hpoly_ne : (X ^ 2 - C kq : Polynomial ℚ) ≠ 0 := fun h ↦ by
      simpa using congr_arg (fun p ↦ coeff p 2) h
    have hqfin : {q : ℚ | q ^ 2 = kq}.Finite := by
      apply Set.Finite.subset (X ^ 2 - C kq : Polynomial ℚ).roots.toFinset.finite_toSet
      intro q hq
      simp only [Set.mem_setOf_eq] at hq
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hpoly_ne]
      simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C]
      linarith [hq]
    exact Set.Finite.subset (hqfin.preimage (f := fun t : ℤ ↦ (t : ℚ))
      (fun x _ y _ h ↦ by simpa using h)) (fun t ht ↦ ht)
  have hfin_zero : {t : ℤ | (t : ℚ) = 0}.Finite := by
    apply Set.Finite.subset (Set.finite_singleton (0 : ℤ))
    intro t ht
    exact_mod_cast ht
  apply Set.Finite.subset (hfin_quad.union hfin_zero)
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  have hcrit : (kq - (t : ℚ) ^ 2) ^ (n - 1) = 0 → (t : ℚ) ^ 2 = kq := fun hp ↦ by
    linarith [pow_eq_zero_iff (show n - 1 ≠ 0 by omega) |>.mp hp]
  have hne_ft : specialize (serreAnFamilyOdd n) t ≠ 0 :=
    (specialize_serreAnFamilyOdd_monic n hn t).ne_zero
  have hcommon : ∃ r : AlgebraicClosure ℚ,
      eval r (map φ (specialize (serreAnFamilyOdd n) t)) = 0 ∧
      eval r (map φ (derivative (specialize (serreAnFamilyOdd n) t))) = 0 := by
    by_contra hc
    push_neg at hc
    apply ht
    rw [Separable]
    apply isCoprime_of_irreducible_dvd
    · exact fun h ↦ hne_ft h.1
    · intro z hz hz' hz''
      have hdeg : (z.map φ).degree ≠ 0 := by
        rw [degree_map]
        exact hz.degree_pos.ne'
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
      have hxz : eval₂ φ x z = 0 := by simpa [eval_map] using hx
      have hxf : eval x (map φ (specialize (serreAnFamilyOdd n) t)) = 0 := by
        simpa [eval_map] using eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ x hz' hxz
      have hxf' : eval x (map φ (derivative (specialize (serreAnFamilyOdd n) t))) = 0 := by
        simpa [eval_map] using eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ x hz'' hxz
      exact hc x hxf hxf'
  obtain ⟨r, hrf, hrf'⟩ := hcommon
  rw [specialize_serreAnFamilyOdd_derivative n hn t] at hrf'
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  -- the common root of `f_t'` must be `0` or `φ (k − t²)`
  have hr0κ : r = 0 ∨ r = φ (kq - (t : ℚ) ^ 2) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_natCast, eval_sub, eval_mul, eval_pow, eval_X, eval_C,
      eval_natCast, map_natCast, ← hkq] at hrf'
    have hfact : (n : AlgebraicClosure ℚ) * r ^ (n - 2) * (r - φ (kq - (t : ℚ) ^ 2)) = 0 := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, map_mul, map_natCast] at hrf'
      linear_combination hrf'
    rcases mul_eq_zero.mp hfact with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hn0
      · rcases eq_or_ne (n - 2) 0 with he | he
        · rw [he, pow_zero] at h'
          exact absurd h' one_ne_zero
        · exact Or.inl ((pow_eq_zero_iff he).mp h')
    · exact Or.inr (by linear_combination h)
  simp only [Set.mem_union, Set.mem_setOf_eq]
  -- The ℚ-level values of `f_t` at its two critical points.
  have hF0 : eval 0 (specialize (serreAnFamilyOdd n) t) = kq / ((n : ℚ) - 1) * (kq - (t : ℚ) ^ 2) ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq]
    simp [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
  have hFκ : eval (kq - (t : ℚ) ^ 2) (specialize (serreAnFamilyOdd n) t)
      = (t : ℚ) ^ 2 / ((n : ℚ) - 1) * (kq - (t : ℚ) ^ 2) ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    have hpow : (kq - (t : ℚ) ^ 2) ^ n = (kq - (t : ℚ) ^ 2) * (kq - (t : ℚ) ^ 2) ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    have hkey : (kq - (t : ℚ) ^ 2) - (n : ℚ) / ((n : ℚ) - 1) * (kq - (t : ℚ) ^ 2)
        + kq / ((n : ℚ) - 1) = (t : ℚ) ^ 2 / ((n : ℚ) - 1) := by
      rw [hkq]
      field_simp
      ring
    linear_combination ((kq - (t : ℚ) ^ 2) ^ (n - 1)) * hkey
  -- In either case `f_t(r) = 0` forces `k − t² = 0` (i.e. `t² = k`) or `t = 0`.
  rcases hr0κ with h0 | hκ
  · -- r = 0
    subst h0
    have hz : eval 0 (specialize (serreAnFamilyOdd n) t) = 0 := by
      apply hφinj
      rw [map_zero, ← hrf, eval_map, eval₂_at_zero,
        coeff_zero_eq_eval_zero]
    rw [hF0] at hz
    rcases mul_eq_zero.mp hz with hb | hp
    · exact absurd hb (div_ne_zero hkne hne1)
    · exact Or.inl (hcrit hp)
  · -- r = φ (k − t²)
    subst hκ
    have hz : eval (kq - (t : ℚ) ^ 2) (specialize (serreAnFamilyOdd n) t) = 0 := by
      apply hφinj
      rw [map_zero, ← hrf, eval_map, eval₂_at_apply]
    rw [hFκ] at hz
    rcases mul_eq_zero.mp hz with hb | hp
    · right
      have h2 : (t : ℚ) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp hb with h | h
        · exact h
        · exact absurd h hne1
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
    · exact Or.inl (hcrit hp)

/-- **[algebraic leaf]** For a separable specialization the `n` roots are distinct. -/
theorem serreAnFamilyOdd_card_rootSet (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable) :
    Fintype.card ((specialize (serreAnFamilyOdd n) t).rootSet
      (specialize (serreAnFamilyOdd n) t).SplittingField) = n := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits _),
    specialize_serreAnFamilyOdd_natDegree n hn t]

/-- **[algebraic leaf]** Hence a root-enumeration `Fin n ≃ rootSet` exists for separable `t`. -/
theorem serreAnFamilyOdd_rootEnum_nonempty (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable) :
    Nonempty (Fin n ≃ (specialize (serreAnFamilyOdd n) t).rootSet
      (specialize (serreAnFamilyOdd n) t).SplittingField) :=
  ⟨(Fintype.equivFinOfCardEq (serreAnFamilyOdd_card_rootSet n hn t hsep)).symm⟩

/-- **The closed-form `X`-discriminant** of `serreAnFamilyOdd n` at the integer specialization `t`.
The Vieta computation gives, after sign collapse for odd `n`, the clean square

  `disc = n^{2n-2} · t² · (k−t²)^{(n-1)²} / (n−1)^{n-1}`,  with `k = (−1)^{(n−1)/2}·n`. -/
def serreAnDiscValOdd (n : ℕ) (t : ℤ) : ℚ :=
  (n : ℚ) ^ (2 * n - 2) * (t : ℚ) ^ 2
    * ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2) ^ ((n - 1) ^ 2) / ((n : ℚ) - 1) ^ (n - 1)

/-- **The explicit rational square-root** of the `X`-discriminant of `serreAnFamilyOdd n` at `t`,
for **odd** `n`:  `δ = n^{n-1}·t·(k−t²)^{(n-1)²/2} / (n−1)^{(n-1)/2}`. -/
def serreAnDeltaOdd (n : ℕ) (t : ℤ) : ℚ :=
  (n : ℚ) ^ (n - 1) * (t : ℚ)
    * ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2) ^ ((n - 1) ^ 2 / 2) / ((n : ℚ) - 1) ^ ((n - 1) / 2)

/-- **[algebraic leaf — odd parity square]** For **odd** `n ≥ 2`, `serreAnDiscValOdd n t` is the
square of `serreAnDeltaOdd n t`. -/
theorem serreAnDeltaOdd_sq_eq (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ) :
    (serreAnDeltaOdd n t) ^ 2 = serreAnDiscValOdd n t := by
  obtain ⟨m, rfl⟩ := hodd
  unfold serreAnDeltaOdd serreAnDiscValOdd
  rw [div_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  rw [show (2 * m + 1 - 1) * 2 = 2 * (2 * m + 1) - 2 by omega,
      show ((2 * m + 1 - 1) ^ 2 / 2) * 2 = (2 * m + 1 - 1) ^ 2 by
        rw [show 2 * m + 1 - 1 = 2 * m by omega]
        ring_nf
        omega,
      show ((2 * m + 1 - 1) / 2) * 2 = 2 * m + 1 - 1 by omega]

open Finset in
/-- **[algebraic core — Vieta value]** For a separable specialization the signed off-diagonal
product of the root differences equals `algebraMap ℚ _ (serreAnDiscValOdd n t)`. -/
theorem serreAnFamilyOdd_signed_prod_erase_val (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamilyOdd n) t).rootSet
        (specialize (serreAnFamilyOdd n) t).SplittingField) :
    (-1 : (specialize (serreAnFamilyOdd n) t).SplittingField) ^ (n * (n - 1) / 2) *
        ∏ i, ∏ j ∈ Finset.univ.erase i,
          ((v i : (specialize (serreAnFamilyOdd n) t).SplittingField) - (v j : _)) =
      algebraMap ℚ (specialize (serreAnFamilyOdd n) t).SplittingField (serreAnDiscValOdd n t) := by
  classical
  set K := (specialize (serreAnFamilyOdd n) t).SplittingField
  set φ : ℚ →+* K := algebraMap ℚ K
  set w : Fin n → K := fun i ↦ (v i : K)
  set kq : ℚ := (-1 : ℚ) ^ ((n - 1) / 2) * n with hkq
  set κtq : ℚ := kq - (t : ℚ) ^ 2 with hκtq
  have hne1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hmonic : (specialize (serreAnFamilyOdd n) t).Monic := specialize_serreAnFamilyOdd_monic n hn t
  have hwinj : Function.Injective w := fun i j h ↦ v.injective (Subtype.ext h)
  -- Root bridge
  have hbridge : ((specialize (serreAnFamilyOdd n) t).map φ).roots = Multiset.map w Finset.univ.val := by
    have hnd : ((specialize (serreAnFamilyOdd n) t).map φ).roots.Nodup := nodup_roots (hsep.map)
    have hmap : ((specialize (serreAnFamilyOdd n) t).rootSet K).toFinset = Finset.map (Function.Embedding.subtype _)
        (Finset.univ : Finset ((specialize (serreAnFamilyOdd n) t).rootSet K)) := by
      ext x
      simp
    have hsub : Multiset.map (Subtype.val) (Finset.univ : Finset ((specialize (serreAnFamilyOdd n) t).rootSet K)).val
        = ((specialize (serreAnFamilyOdd n) t).rootSet K).toFinset.val := by
      rw [hmap, Finset.map_val]
      rfl
    have hrs : ((specialize (serreAnFamilyOdd n) t).rootSet K).toFinset.val
        = ((specialize (serreAnFamilyOdd n) t).map φ).roots := by
      refine (Multiset.Nodup.ext ((specialize (serreAnFamilyOdd n) t).rootSet K).toFinset.nodup hnd).mpr (fun a ↦ ?_)
      rw [← Finset.mem_def, Set.mem_toFinset]
      simp only [mem_rootSet', mem_roots', IsRoot.def,
        aeval_def, eval_map]
      exact Iff.rfl
    rw [← hrs, ← hsub, ← Multiset.map_univ_val_equiv v, Multiset.map_map]
    rfl
  have hsplitK : ((specialize (serreAnFamilyOdd n) t).map φ).Splits :=
    SplittingField.splits (specialize (serreAnFamilyOdd n) t)
  have hwmem : ∀ i, w i ∈ ((specialize (serreAnFamilyOdd n) t).map φ).roots := fun i ↦ by
    rw [hbridge]
    exact Multiset.mem_map_of_mem w (Finset.mem_univ i)
  have hpe : ∀ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
      = eval (w i) (derivative ((specialize (serreAnFamilyOdd n) t).map φ)) := by
    intro i
    rw [hsplitK.eval_root_derivative (hmonic.map φ) (hwmem i), hbridge,
      ← Multiset.map_erase w hwinj, ← Finset.erase_val, Multiset.map_map]
    rfl
  have hde : derivative ((specialize (serreAnFamilyOdd n) t).map φ)
      = (n : Polynomial K) * X ^ (n - 1) - C ((n : K) * φ κtq) * X ^ (n - 2) := by
    rw [derivative_map, specialize_serreAnFamilyOdd_derivative n hn t]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_natCast, map_mul, map_natCast]
    rw [← hkq, ← hκtq]
  have hev : ∀ i, eval (w i) (derivative ((specialize (serreAnFamilyOdd n) t).map φ))
      = (n : K) * w i ^ (n - 2) * (w i - φ κtq) := by
    intro i
    rw [hde]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_natCast]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hK0 : ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
      = (n : K) ^ n * (∏ i, w i) ^ (n - 2) * ∏ i, (w i - φ κtq) := by
    have hterm : ∀ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
        = (n : K) * w i ^ (n - 2) * (w i - φ κtq) := fun i ↦ (hpe i).trans (hev i)
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
      Finset.card_univ, Fintype.card_fin]
  have hmdeg : ((specialize (serreAnFamilyOdd n) t).map φ).natDegree = n := by
    rw [hmonic.natDegree_map, specialize_serreAnFamilyOdd_natDegree n hn t]
  have hcard : Multiset.card ((specialize (serreAnFamilyOdd n) t).map φ).roots
      = ((specialize (serreAnFamilyOdd n) t).map φ).natDegree := by
    rw [hbridge, Multiset.card_map, hmdeg]
    simp
  have hfact : (specialize (serreAnFamilyOdd n) t).map φ = ∏ i, (X - C (w i)) := by
    have hh := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hmonic.map φ) hcard
    rw [hbridge, Multiset.map_map] at hh
    rw [← hh]
    rfl
  have heval0 : eval 0 ((specialize (serreAnFamilyOdd n) t).map φ)
      = φ (eval 0 (specialize (serreAnFamilyOdd n) t)) := by
    rw [eval_map, eval₂_at_zero, coeff_zero_eq_eval_zero]
  have hevalκ : eval (φ κtq) ((specialize (serreAnFamilyOdd n) t).map φ)
      = φ (eval κtq (specialize (serreAnFamilyOdd n) t)) := by
    rw [eval_map, eval₂_at_apply]
  -- constant and (k−t²)-values of `f_t`
  have hF0 : eval 0 (specialize (serreAnFamilyOdd n) t) = kq / ((n : ℚ) - 1) * κtq ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq, ← hκtq]
    simp [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
  have hFκ : eval κtq (specialize (serreAnFamilyOdd n) t) = (t : ℚ) ^ 2 / ((n : ℚ) - 1) * κtq ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq, ← hκtq]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    have hpow : κtq ^ n = κtq * κtq ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    have hkey : κtq - (n : ℚ) / ((n : ℚ) - 1) * κtq + kq / ((n : ℚ) - 1)
        = (t : ℚ) ^ 2 / ((n : ℚ) - 1) := by
      rw [hκtq]
      field_simp
      ring
    linear_combination (κtq ^ (n - 1)) * hkey
  -- Vieta: ∏ w = (−1)ⁿ φ(F0), ∏ (w − κ) = (−1)ⁿ φ(Fκ)
  have hP : ∏ i, w i = (-1 : K) ^ n * φ (eval 0 (specialize (serreAnFamilyOdd n) t)) := by
    have h0 := congrArg (eval 0) hfact
    rw [eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
    rw [heval0] at h0
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h0
    have : (-1 : K) ^ n * φ (eval 0 (specialize (serreAnFamilyOdd n) t))
        = (-1) ^ n * ((-1) ^ n * ∏ i, w i) := by rw [h0]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  have hQ : ∏ i, (w i - φ κtq) = (-1 : K) ^ n * φ (eval κtq (specialize (serreAnFamilyOdd n) t)) := by
    have h1 := congrArg (eval (φ κtq)) hfact
    rw [eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [hevalκ] at h1
    simp_rw [← neg_sub (w _) (φ κtq)] at h1
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h1
    have : (-1 : K) ^ n * φ (eval κtq (specialize (serreAnFamilyOdd n) t))
        = (-1) ^ n * ((-1) ^ n * ∏ i, (w i - φ κtq)) := by rw [h1]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  -- The ℚ-level closed-form identity for the sign-cleaned discriminant.
  have hℚ : (-1 : ℚ) ^ (n * (n - 1) / 2)
        * ((n : ℚ) ^ n * ((-1) ^ n * (eval 0 (specialize (serreAnFamilyOdd n) t))) ^ (n - 2)
          * ((-1) ^ n * (eval κtq (specialize (serreAnFamilyOdd n) t))))
      = serreAnDiscValOdd n t := by
    rw [hF0, hFκ, serreAnDiscValOdd, ← hkq, ← hκtq, hkq]
    obtain ⟨m, rfl⟩ := hodd
    rw [show (2 * m + 1 - 1) / 2 = m by omega]
    simp only [mul_pow, div_pow, ← pow_mul]
    -- Sign collapse: the total (−1)-exponent is even for odd `n`.
    have hEven : Even ((2 * m + 1) * (2 * m + 1 - 1) / 2 + (2 * m + 1) * (2 * m + 1 - 2)
        + m * (2 * m + 1 - 2) + (2 * m + 1)) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (k + 1) + 1 - 1 = 2 * (k + 1) by omega,
          show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega,
          show (2 * (k + 1) + 1) * (2 * (k + 1)) / 2 = (2 * (k + 1) + 1) * (k + 1) by
            rw [show (2 * (k + 1) + 1) * (2 * (k + 1)) = ((2 * (k + 1) + 1) * (k + 1)) * 2 by ring]
            omega]
      exact ⟨4 * k * k + 9 * k + 5, by ring⟩
    have hsign : (-1 : ℚ) ^ ((2 * m + 1) * (2 * m + 1 - 1) / 2)
        * (-1) ^ ((2 * m + 1) * (2 * m + 1 - 2))
        * (-1) ^ (m * (2 * m + 1 - 2))
        * (-1) ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← pow_add, ← pow_add]
      exact hEven.neg_one_pow
    -- Expand the RHS closed-form powers to align atoms with the LHS.
    have hRHSn : ((2 * m + 1 : ℕ) : ℚ) ^ (2 * (2 * m + 1) - 2)
        = ((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1) * ((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1 - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hRHSκ : κtq ^ ((2 * m + 1 - 1) ^ 2)
        = κtq ^ ((2 * m + 1 - 1) * (2 * m + 1 - 2)) * κtq ^ (2 * m + 1 - 1) := by
      rw [← pow_add]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (k + 1) + 1 - 1 = 2 * k + 2 by omega,
          show 2 * (k + 1) + 1 - 2 = 2 * k + 1 by omega]
      ring
    have hRHSd : (((2 * m + 1 : ℕ) : ℚ) - 1) ^ (2 * m + 1 - 1)
        = (((2 * m + 1 : ℕ) : ℚ) - 1) ^ (2 * m + 1 - 2) * (((2 * m + 1 : ℕ) : ℚ) - 1) := by
      rw [show 2 * m + 1 - 1 = (2 * m + 1 - 2) + 1 by omega, pow_add, pow_one]
    rw [hRHSn, hRHSκ, hRHSd, div_mul_eq_div_div]
    linear_combination
      (((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1) * ((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1 - 2)
          * (t : ℚ) ^ 2 * κtq ^ ((2 * m + 1 - 1) * (2 * m + 1 - 2)) * κtq ^ (2 * m + 1 - 1)
          / (((2 * m + 1 : ℕ) : ℚ) - 1) ^ (2 * m + 1 - 2) / (((2 * m + 1 : ℕ) : ℚ) - 1)) * hsign
  -- final assembly
  show (-1 : K) ^ (n * (n - 1) / 2) *
      ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j) = φ (serreAnDiscValOdd n t)
  rw [hK0, hP, hQ, ← hℚ]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

/-- **[algebraic core — general discriminant identity]** For a separable specialization the
`discSq` of the roots equals `algebraMap ℚ _ (serreAnDiscValOdd n t)`. -/
theorem serreAnFamilyOdd_discSq_val (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamilyOdd n) t).rootSet
        (specialize (serreAnFamilyOdd n) t).SplittingField) :
    discSq (fun i => (v i : (specialize (serreAnFamilyOdd n) t).SplittingField)) =
      algebraMap ℚ (specialize (serreAnFamilyOdd n) t).SplittingField (serreAnDiscValOdd n t) := by
  rw [discSq, discElem_sq_eq_sign_mul_prod_erase (fun i ↦ (v i :
    (specialize (serreAnFamilyOdd n) t).SplittingField))]
  exact serreAnFamilyOdd_signed_prod_erase_val n hn hodd t hsep v

/-- **[algebraic core — odd case, discriminant-square identity]** For **odd** `n` and a separable
specialization, `discSq` of the roots equals `(algebraMap ℚ _ (serreAnDeltaOdd n t))²`. -/
theorem serreAnFamilyOdd_discSq_eq_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamilyOdd n) t).rootSet
        (specialize (serreAnFamilyOdd n) t).SplittingField) :
    discSq (fun i => (v i : (specialize (serreAnFamilyOdd n) t).SplittingField)) =
      (algebraMap ℚ (specialize (serreAnFamilyOdd n) t).SplittingField (serreAnDeltaOdd n t)) ^ 2 := by
  rw [serreAnFamilyOdd_discSq_val n hn hodd t hsep v, ← serreAnDeltaOdd_sq_eq n hn hodd t, map_pow]

/-- **[algebraic core — the discriminant-square certificate, separable case]** For **odd** `n`,
whenever the specialization is separable the `discSq` of the roots is a perfect square in `ℚ`. -/
theorem serreAnFamilyOdd_disc_isSquare_of_separable (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ)
    (hsep : (specialize (serreAnFamilyOdd n) t).Separable) :
    ∃ v : Fin n ≃ (specialize (serreAnFamilyOdd n) t).rootSet
        (specialize (serreAnFamilyOdd n) t).SplittingField,
      ∃ d : ℚ, discSq (fun i => (v i : (specialize (serreAnFamilyOdd n) t).SplittingField)) =
        (algebraMap ℚ (specialize (serreAnFamilyOdd n) t).SplittingField d) ^ 2 := by
  obtain ⟨v⟩ := serreAnFamilyOdd_rootEnum_nonempty n hn t hsep
  exact ⟨v, serreAnDeltaOdd n t, serreAnFamilyOdd_discSq_eq_odd n hn hodd t hsep v⟩

end AlternatingFamily

end
