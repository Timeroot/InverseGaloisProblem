/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamily
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# Serre's explicit `Aₙ`-family (Serre §4.5) — the concrete substituted family

This file develops the *same* mathematical content as the scaffold existential
`AlternatingFamily.exists_anFamily_disc_isSquare` (in `Hilbert/AlternatingFamily.lean`),
but around a **concrete `def`** so that downstream uses are coupled to a fixed polynomial
instead of an arbitrary existential witness.

Serre's substituted family (for `n` even), *Topics in Galois Theory* §4.5, is

  `g(X, T) = (n−1)·Xⁿ − n·X^{n-1} + 1 + (−1)^{n/2}·(n−1)·T²`.

Its `X`-discriminant is identically a square in `ℚ[T]`, so every specialization has square
discriminant and Galois group `⊆ Aₙ`.

We normalise `g` to be **monic in `X`** by dividing through by the leading coefficient
`n − 1`:

  `serreAnFamily n = Xⁿ − (n/(n−1))·X^{n-1} + 1/(n−1) + (−1)^{n/2}·T²`.

As an element of `ℚ[T][X]` (outer variable `X`, coefficient variable `T = C X`), the constant
(in `X`) coefficient is the `ℚ[T]`-element `C (1/(n−1)) + C ((−1)^{n/2})·X²`.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

/-- **Serre's explicit `Aₙ`-family** `Xⁿ − (n/(n−1))·X^{n-1} + 1/(n−1) + (−1)^{n/2}·T²`,
normalised monic in `X`, as an element of `ℚ[T][X]`.

This is Serre's substituted family `(n−1)Xⁿ − nX^{n-1} + 1 + (−1)^{n/2}(n−1)T²` divided by
its leading coefficient `n − 1`.  The genus-`0` substitution has made the `X`-discriminant an
identical square in `ℚ[T]`, so every integer specialization has square discriminant and
Galois group `⊆ Aₙ`. -/
def serreAnFamily (n : ℕ) : Polynomial (Polynomial ℚ) :=
  X ^ n - C (C ((n : ℚ) / ((n : ℚ) - 1))) * X ^ (n - 1)
    + C (C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2)

/-- The constant-in-`X` coefficient of `serreAnFamily n`, as an element of `ℚ[T]`. -/
theorem serreAnFamily_eq (n : ℕ) :
    serreAnFamily n = X ^ n
      - (C (C ((n : ℚ) / ((n : ℚ) - 1))) * X ^ (n - 1)
        - C (C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2)) := by
  unfold serreAnFamily; ring

/-- **[algebraic leaf]** `serreAnFamily n` is monic (in `X`) for `n ≥ 2`. -/
theorem serreAnFamily_monic (n : ℕ) (hn : 2 ≤ n) : (serreAnFamily n).Monic := by
  rw [serreAnFamily_eq]
  apply monic_X_pow_sub
  have hle : (C (C ((n : ℚ) / ((n : ℚ) - 1))) * X ^ (n - 1)
      - C (C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2)
        : Polynomial (Polynomial ℚ)).degree ≤ (↑(n - 1)) := by
    refine le_trans (degree_sub_le _ _) ?_
    apply max_le
    · exact degree_C_mul_X_pow_le _ _
    · exact le_trans degree_C_le (by exact_mod_cast Nat.zero_le (n - 1))
  refine lt_of_le_of_lt hle ?_
  exact_mod_cast (by omega : n - 1 < n)

/-- **[algebraic leaf]** `serreAnFamily n` has `X`-degree `n` for `n ≥ 2`. -/
theorem serreAnFamily_natDegree (n : ℕ) (hn : 2 ≤ n) :
    (serreAnFamily n).natDegree = n := by
  have hmonic := serreAnFamily_monic n hn
  -- Monic of the given leading-term shape ⇒ degree = n.
  rw [serreAnFamily_eq]
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · rw [natDegree_X_pow]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
      rw [natDegree_X_pow]; omega
    · rw [natDegree_C]; omega

/-- **[algebraic leaf]** The `X`-derivative of `serreAnFamily` is `n·X^{n-1} − n·X^{n-2}`
(the constant-in-`X` term contributes nothing, and `(n−1)·(n/(n−1)) = n`).  Its critical
points are `X = 0` and `X = 1`, matching the collision structure forced by the substitution. -/
theorem serreAnFamily_derivative (n : ℕ) (hn : 2 ≤ n) :
    derivative (serreAnFamily n) = C (n : Polynomial ℚ) * X ^ (n - 1)
      - C (n : Polynomial ℚ) * X ^ (n - 2) := by
  have hne : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  unfold serreAnFamily
  simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul, derivative_C,
    add_zero, ← mul_assoc]
  rw [show n - 1 - 1 = n - 2 by omega]
  -- reduce to the coefficient identity `(n/(n−1)) · (n−1) = n` in `ℚ`
  congr 1
  congr 1
  rw [← C_mul]
  congr 1
  rw [← map_natCast (C : ℚ →+* Polynomial ℚ) (n - 1),
      ← map_natCast (C : ℚ →+* Polynomial ℚ) n, ← C_mul]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp

/-- **[algebraic leaf]** The explicit integer specialization
`serreAnFamily n |_t = Xⁿ − (n/(n−1))X^{n-1} + (1/(n−1) + (−1)^{n/2} t²)` in `ℚ[X]`. -/
theorem specialize_serreAnFamily (n : ℕ) (t : ℤ) :
    specialize (serreAnFamily n) t
      = X ^ n - C ((n : ℚ) / ((n : ℚ) - 1)) * X ^ (n - 1)
        + C (1 / ((n : ℚ) - 1) + (-1 : ℚ) ^ (n / 2) * (t : ℚ) ^ 2) := by
  unfold specialize serreAnFamily
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

/-- **[algebraic leaf]** Every integer specialization of `serreAnFamily n` is monic. -/
theorem specialize_serreAnFamily_monic (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    (specialize (serreAnFamily n) t).Monic :=
  specialize_monic _ (serreAnFamily_monic n hn) t

/-- **[algebraic leaf]** Every integer specialization of `serreAnFamily n` has degree `n`. -/
theorem specialize_serreAnFamily_natDegree (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    (specialize (serreAnFamily n) t).natDegree = n := by
  unfold specialize
  rw [(serreAnFamily_monic n hn).natDegree_map, serreAnFamily_natDegree n hn]

/-- **[algebraic leaf]** The `X`-derivative of every integer specialization is
`n·X^{n-1} − n·X^{n-2}` (independent of `t`, since the `t`-dependence sits in the constant term). -/
theorem specialize_serreAnFamily_derivative (n : ℕ) (hn : 2 ≤ n) (t : ℤ) :
    derivative (specialize (serreAnFamily n) t)
      = C (n : ℚ) * X ^ (n - 1) - C (n : ℚ) * X ^ (n - 2) := by
  rw [specialize, Polynomial.derivative_map, serreAnFamily_derivative n hn]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

/-- **[algebraic leaf — separability]** `serreAnFamily n |_t` is separable for all but finitely
many `t ∈ ℤ`.  The exceptions are the finitely many integer roots of the (nonzero) `X`-discriminant
`D(T)² ∈ ℚ[T]`.  This is the cofinite hypothesis under which the per-`t` `discSq`-conjunct below
actually admits a root-enumeration `Fin n ≃ rootSet` (at the finitely many non-separable `t` the
root set is strictly smaller than `n`, so no such equivalence exists — exactly as for the base
family `anBaseFamily_separable_cofinite`). -/
theorem serreAnFamily_separable_cofinite (n : ℕ) (hn : 2 ≤ n) :
    {t : ℤ | ¬ (specialize (serreAnFamily n) t).Separable}.Finite := by
  set φ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
  have hφinj : Function.Injective φ := φ.injective
  set a : ℚ := (n : ℚ) / ((n : ℚ) - 1) with ha
  set b : ℚ := 1 / ((n : ℚ) - 1) with hb
  set s : ℚ := (-1 : ℚ) ^ (n / 2) with hs
  have hsne : s ≠ 0 := pow_ne_zero _ (by norm_num)
  -- Each collision `s·t² = k` has only finitely many integer solutions.
  have hfin_quad : ∀ k : ℚ, {t : ℤ | s * (t : ℚ) ^ 2 = k}.Finite := by
    intro k
    have hpoly_ne : (C s * X ^ 2 - C k : Polynomial ℚ) ≠ 0 := by
      intro h
      have hc := congr_arg (fun p => Polynomial.coeff p 2) h
      simp only [coeff_sub, coeff_C_mul, coeff_X_pow, if_true, mul_one, coeff_C,
        coeff_zero] at hc
      simp at hc
      exact hsne hc
    have hqfin : {q : ℚ | s * q ^ 2 = k}.Finite := by
      apply Set.Finite.subset (C s * X ^ 2 - C k : Polynomial ℚ).roots.toFinset.finite_toSet
      intro q hq
      simp only [Set.mem_setOf_eq] at hq
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hpoly_ne]
      simp only [IsRoot.def, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
      linarith [hq]
    refine Set.Finite.subset (hqfin.preimage (f := fun t : ℤ => (t : ℚ))
      (fun x _ y _ h => by simpa using h)) ?_
    intro t ht; exact ht
  -- The bad set is contained in the two collision loci `r = 0` and `r = 1`.
  refine Set.Finite.subset ((hfin_quad (-b)).union (hfin_quad (a - 1 - b))) ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  have hne_ft : specialize (serreAnFamily n) t ≠ 0 :=
    (specialize_serreAnFamily_monic n hn t).ne_zero
  -- non-separable ⇒ a common root of `f_t` and `f_t'` in the algebraic closure
  have hcommon : ∃ r : AlgebraicClosure ℚ,
      eval r (map φ (specialize (serreAnFamily n) t)) = 0 ∧
      eval r (map φ (derivative (specialize (serreAnFamily n) t))) = 0 := by
    by_contra hc
    push_neg at hc
    apply ht
    rw [Polynomial.Separable]
    apply isCoprime_of_irreducible_dvd
    · exact fun h => hne_ft h.1
    · intro z hz hz' hz''
      have hdeg : (z.map φ).degree ≠ 0 := by
        rw [Polynomial.degree_map]; exact hz.degree_pos.ne'
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
      have hxf : eval x (map φ (specialize (serreAnFamily n) t)) = 0 := by
        have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ x hz'
          (by simpa [Polynomial.eval_map] using hx)
        simpa [Polynomial.eval_map] using this
      have hxf' : eval x (map φ (derivative (specialize (serreAnFamily n) t))) = 0 := by
        have := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero φ x hz''
          (by simpa [Polynomial.eval_map] using hx)
        simpa [Polynomial.eval_map] using this
      exact hc x hxf hxf'
  obtain ⟨r, hrf, hrf'⟩ := hcommon
  -- the common root of `f_t'` must be `0` or `1`
  rw [specialize_serreAnFamily_derivative n hn t] at hrf'
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by rw [Nat.cast_ne_zero]; omega
  have hr01 : r = 0 ∨ r = 1 := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_natCast, eval_sub, eval_mul, eval_pow, eval_X,
      Polynomial.eval_natCast, map_natCast] at hrf'
    have hfact : (n : AlgebraicClosure ℚ) * r ^ (n - 2) * (r - 1) = 0 := by
      have hm : n - 1 = (n - 2) + 1 := by omega
      rw [hm, pow_succ] at hrf'
      linear_combination hrf'
    rcases mul_eq_zero.mp hfact with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hn0
      · rcases eq_or_ne (n - 2) 0 with he | he
        · rw [he, pow_zero] at h'; exact absurd h' one_ne_zero
        · exact Or.inl ((pow_eq_zero_iff he).mp h')
    · exact Or.inr (by linear_combination h)
  -- plug `r ∈ {0,1}` into `f_t(r) = 0` to pin down `t`
  rw [specialize_serreAnFamily n t] at hrf
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, eval_add, eval_sub, eval_mul, eval_pow, eval_X,
    eval_C, ← ha, ← hb, ← hs] at hrf
  simp only [Set.mem_union, Set.mem_setOf_eq]
  rcases hr01 with h0 | h1
  · left
    subst h0
    rw [zero_pow (by omega : n ≠ 0), zero_pow (by omega : n - 1 ≠ 0)] at hrf
    simp only [mul_zero, sub_zero, zero_add] at hrf
    have hq : b + s * (t : ℚ) ^ 2 = 0 := by
      have := hrf; rw [show (0 : AlgebraicClosure ℚ) = φ 0 by rw [map_zero]] at this
      exact hφinj this
    linarith [hq]
  · right
    subst h1
    simp only [one_pow, mul_one] at hrf
    have hq : (1 : ℚ) - a + (b + s * (t : ℚ) ^ 2) = 0 := by
      apply hφinj
      rw [map_add, map_sub, map_one, map_zero]
      linear_combination hrf
    linarith [hq]

/-- **[algebraic leaf]** For a separable specialization the `n` roots are distinct, so the root
set in the splitting field has cardinality exactly `n`. -/
theorem serreAnFamily_card_rootSet (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable) :
    Fintype.card ((specialize (serreAnFamily n) t).rootSet
      (specialize (serreAnFamily n) t).SplittingField) = n := by
  rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits _),
    specialize_serreAnFamily_natDegree n hn t]

/-- **[algebraic leaf]** Hence a root-enumeration `Fin n ≃ rootSet` exists for separable `t`. -/
theorem serreAnFamily_rootEnum_nonempty (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable) :
    Nonempty (Fin n ≃ (specialize (serreAnFamily n) t).rootSet
      (specialize (serreAnFamily n) t).SplittingField) :=
  ⟨(Fintype.equivFinOfCardEq (serreAnFamily_card_rootSet n hn t hsep)).symm⟩

/-- **The explicit rational square-root of the `X`-discriminant** of `serreAnFamily n` at the
integer specialization `t`, for **even** `n`.

The closed-form discriminant (verified: it equals `nⁿ · t² · qⁿ⁻²` with
`q = 1/(n−1) + (−1)^{n/2} t²`) is, *for even `n`*, the perfect square

  `δ² = (n^{n/2} · t · q^{n/2−1})²`,

so `δ = n^{n/2} · t · q^{n/2−1}` is the rational `δ` whose square is the discriminant. -/
def serreAnDelta (n : ℕ) (t : ℤ) : ℚ :=
  (n : ℚ) ^ (n / 2) * (t : ℚ)
    * (1 / ((n : ℚ) - 1) + (-1 : ℚ) ^ (n / 2) * (t : ℚ) ^ 2) ^ (n / 2 - 1)

/-- **The closed-form `X`-discriminant** of `serreAnFamily n` at the integer specialization `t`,
as an element of `ℚ`:  `disc = nⁿ · t² · qⁿ⁻²` with `q = 1/(n−1) + (−1)^{n/2} t²`.

This formula is parity-independent (it is the value of the discriminant for every `n ≥ 2`); it is
a **rational square precisely when `n` is even** (see `serreAnDelta_sq_eq`). -/
def serreAnDiscVal (n : ℕ) (t : ℤ) : ℚ :=
  (n : ℚ) ^ n * (t : ℚ) ^ 2
    * (1 / ((n : ℚ) - 1) + (-1 : ℚ) ^ (n / 2) * (t : ℚ) ^ 2) ^ (n - 2)

/-- **[algebraic leaf — even parity square]** For **even** `n ≥ 2`, the closed-form discriminant
`serreAnDiscVal n t = nⁿ t² qⁿ⁻²` is the square of `serreAnDelta n t = n^{n/2} t q^{n/2−1}`:
writing `n = 2m`, `(n^{n/2})² = nⁿ`, `(t)² = t²`, `(q^{n/2−1})² = qⁿ⁻²`. -/
theorem serreAnDelta_sq_eq (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (t : ℤ) :
    (serreAnDelta n t) ^ 2 = serreAnDiscVal n t := by
  obtain ⟨m, rfl⟩ := heven
  have h2 : (m + m) / 2 = m := by omega
  unfold serreAnDelta serreAnDiscVal
  rw [h2, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    show m * 2 = m + m by omega, show (m - 1) * 2 = m + m - 2 by omega]

open Finset in
/-- **[general algebra — discriminant as signed off-diagonal product]** For any family
`w : Fin n → L` in a field, the squared discriminant element `discElem w²` equals the sign
`(−1)^{n(n−1)/2}` times the full off-diagonal product `∏ᵢ ∏_{j≠i}(wᵢ − wⱼ)`.

Reason: `∏ᵢ∏_{j≠i}(wᵢ−wⱼ) = ∏_{i<j}(wᵢ−wⱼ)(wⱼ−wᵢ) = ∏_{i<j} −(wⱼ−wᵢ)² = (−1)^{n(n−1)/2} discElem w²`;
multiply both sides by `(−1)^{n(n−1)/2}`. -/
theorem discElem_sq_eq_sign_mul_prod_erase {L : Type*} [Field L] {n : ℕ} (w : Fin n → L) :
    (discElem w) ^ 2 =
      (-1 : L) ^ (n * (n - 1) / 2) * ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j) := by
  have herase : ∀ i : Fin n, ∏ j ∈ Finset.univ.erase i, (w i - w j)
      = (∏ j ∈ Ioi i, (w i - w j)) * ∏ j ∈ Iio i, (w i - w j) := by
    intro i
    rw [show Finset.univ.erase i = (Ioi i).disjUnion (Iio i) (disjoint_Ioi_Iio i) by
      ext j
      simp only [mem_erase, mem_univ, and_true, disjUnion_eq_union, mem_union, mem_Ioi, mem_Iio]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim (·.ne') (·.ne)⟩,
      prod_disjUnion]
  have hlower : ∏ i, ∏ j ∈ Iio i, (w i - w j) = discElem w := by
    unfold discElem
    exact prod_comm' (fun x y => by simp [mem_Iio, mem_Ioi])
  have hsum : ∑ i : Fin n, (Ioi i).card = n * (n - 1) / 2 := by
    simp_rw [Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n, sum_range_reflect (fun i => i) n,
      sum_range_id]
  have hsign : (∏ i : Fin n, ∏ _j ∈ Ioi i, (-1 : L)) = (-1 : L) ^ (n * (n - 1) / 2) := by
    simp_rw [prod_const]
    rw [prod_pow_eq_pow_sum, hsum]
  have hupper : ∏ i, ∏ j ∈ Ioi i, (w i - w j) = (-1 : L) ^ (n * (n - 1) / 2) * discElem w := by
    unfold discElem
    rw [← hsign, ← prod_mul_distrib]
    apply prod_congr rfl; intro i _
    rw [← prod_mul_distrib]
    apply prod_congr rfl; intro j _
    ring
  have hP : ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
      = (-1 : L) ^ (n * (n - 1) / 2) * (discElem w) ^ 2 := by
    simp_rw [herase]
    rw [prod_mul_distrib, hlower, hupper]
    ring
  rw [hP, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- **[algebraic core — the signed off-diagonal product value]** For a separable
specialization the signed off-diagonal product of the root differences equals (the image of) the
closed-form rational discriminant `serreAnDiscVal n t`.

This is the family-specific computation: since `F(t)` factors as `∏ᵢ(X − wᵢ)` over its splitting
field, `∏_{j≠i}(wᵢ − wⱼ) = F(t)′(wᵢ) = n·wᵢⁿ⁻²·(wᵢ − 1)`, so
`∏ᵢ∏_{j≠i}(wᵢ−wⱼ) = nⁿ (∏wᵢ)ⁿ⁻² ∏(wᵢ−1)`.  Vieta gives `∏wᵢ = (−1)ⁿ q`,
`∏(wᵢ−1) = (−1)ⁿ F(t)(1) = (−1)ⁿ (−1)^{n/2} t²`; collecting the signs against `(−1)^{n(n−1)/2}`
yields `nⁿ t² qⁿ⁻² = serreAnDiscVal n t`. -/
theorem serreAnFamily_signed_prod_erase_val (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamily n) t).rootSet
        (specialize (serreAnFamily n) t).SplittingField) :
    (-1 : (specialize (serreAnFamily n) t).SplittingField) ^ (n * (n - 1) / 2) *
        ∏ i, ∏ j ∈ Finset.univ.erase i,
          ((v i : (specialize (serreAnFamily n) t).SplittingField) - (v j : _)) =
      algebraMap ℚ (specialize (serreAnFamily n) t).SplittingField (serreAnDiscVal n t) := by
  classical
  set φ : ℚ →+* (specialize (serreAnFamily n) t).SplittingField := algebraMap ℚ (specialize (serreAnFamily n) t).SplittingField with hφdef
  set w : Fin n → (specialize (serreAnFamily n) t).SplittingField := fun i => (v i : (specialize (serreAnFamily n) t).SplittingField) with hwdef
  have hne1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hmonic : (specialize (serreAnFamily n) t).Monic := specialize_serreAnFamily_monic n hn t
  have hwinj : Function.Injective w := fun i j h => v.injective (Subtype.ext h)
  -- Root bridge
  have hbridge : ((specialize (serreAnFamily n) t).map φ).roots = Multiset.map w Finset.univ.val := by
    have hnd : ((specialize (serreAnFamily n) t).map φ).roots.Nodup := nodup_roots (hsep.map)
    have hsub : Multiset.map (Subtype.val) (Finset.univ : Finset ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField)).val
        = ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField).toFinset.val := by
      have hmap : ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField).toFinset = Finset.map (Function.Embedding.subtype _)
          (Finset.univ : Finset ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField)) := by ext x; simp
      rw [hmap, Finset.map_val]; rfl
    have hrs : ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField).toFinset.val = ((specialize (serreAnFamily n) t).map φ).roots := by
      refine (Multiset.Nodup.ext ((specialize (serreAnFamily n) t).rootSet (specialize (serreAnFamily n) t).SplittingField).toFinset.nodup hnd).mpr (fun a => ?_)
      rw [← Finset.mem_def, Set.mem_toFinset]
      simp only [Polynomial.mem_rootSet', Polynomial.mem_roots', Polynomial.IsRoot.def,
        Polynomial.aeval_def, Polynomial.eval_map]
      exact Iff.rfl
    rw [← hrs, ← hsub, ← Multiset.map_univ_val_equiv v, Multiset.map_map]
    rfl
  -- Splits over the splitting field
  have hsplitK : ((specialize (serreAnFamily n) t).map φ).Splits := SplittingField.splits (specialize (serreAnFamily n) t)
  have hwmem : ∀ i, w i ∈ ((specialize (serreAnFamily n) t).map φ).roots := fun i => by
    rw [hbridge]; exact Multiset.mem_map_of_mem w (Finset.mem_univ i)
  -- Per-root: ∏_{j≠i}(w i - w j) = eval (w i) (deriv (specialize (serreAnFamily n) t).map φ)
  have hpe : ∀ i, ∏ j ∈ Finset.univ.erase i, (w i - w j) = eval (w i) (derivative ((specialize (serreAnFamily n) t).map φ)) := by
    intro i
    rw [hsplitK.eval_root_derivative (hmonic.map φ) (hwmem i), hbridge,
      ← Multiset.map_erase w hwinj, ← Finset.erase_val, Multiset.map_map]
    rfl
  -- derivative of (specialize (serreAnFamily n) t).map φ
  have hde : derivative ((specialize (serreAnFamily n) t).map φ) = C (n : (specialize (serreAnFamily n) t).SplittingField) * X ^ (n - 1) - C (n : (specialize (serreAnFamily n) t).SplittingField) * X ^ (n - 2) := by
    rw [Polynomial.derivative_map, specialize_serreAnFamily_derivative n hn t]
    simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_natCast]
  -- eval of deriv at w i = (n:K) * w i^(n-2) * (w i - 1)
  have hev : ∀ i, eval (w i) (derivative ((specialize (serreAnFamily n) t).map φ)) = (n : (specialize (serreAnFamily n) t).SplittingField) * w i ^ (n - 2) * (w i - 1) := by
    intro i
    rw [hde]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  -- Product over all i of the per-root value
  have hK0 : ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
      = (n : (specialize (serreAnFamily n) t).SplittingField) ^ n * (∏ i, w i) ^ (n - 2) * ∏ i, (w i - 1) := by
    have hterm : ∀ i, ∏ j ∈ Finset.univ.erase i, (w i - w j)
        = (n : (specialize (serreAnFamily n) t).SplittingField) * w i ^ (n - 2) * (w i - 1) := fun i => (hpe i).trans (hev i)
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
      Finset.card_univ, Fintype.card_fin]
  -- Factorization of (specialize (serreAnFamily n) t) over its splitting field
  have hmdeg : ((specialize (serreAnFamily n) t).map φ).natDegree = n := by
    rw [hmonic.natDegree_map, specialize_serreAnFamily_natDegree n hn t]
  have hcard : Multiset.card ((specialize (serreAnFamily n) t).map φ).roots = ((specialize (serreAnFamily n) t).map φ).natDegree := by
    rw [hbridge, Multiset.card_map, hmdeg]; simp
  have hfact : (specialize (serreAnFamily n) t).map φ = ∏ i, (X - C (w i)) := by
    have hh := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hmonic.map φ) hcard
    rw [hbridge, Multiset.map_map] at hh
    rw [← hh]; rfl
  -- eval-at-point transport ℚ → K
  have heval0 : eval 0 ((specialize (serreAnFamily n) t).map φ) = φ (eval 0 (specialize (serreAnFamily n) t)) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have heval1 : eval 1 ((specialize (serreAnFamily n) t).map φ) = φ (eval 1 (specialize (serreAnFamily n) t)) := by
    rw [Polynomial.eval_map, ← map_one φ, Polynomial.eval₂_at_apply]
  -- constant and 1-values of (specialize (serreAnFamily n) t)
  have hF0 : eval 0 (specialize (serreAnFamily n) t) = 1 / ((n:ℚ) - 1) + (-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2 := by
    rw [specialize_serreAnFamily n t]
    simp [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
  have hF1 : eval 1 (specialize (serreAnFamily n) t) = (-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2 := by
    rw [specialize_serreAnFamily n t]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, one_pow, mul_one]
    field_simp
    ring
  -- Vieta: product of roots and of (root - 1)
  have hP : ∏ i, w i
      = (-1:(specialize (serreAnFamily n) t).SplittingField) ^ n * φ (1 / ((n:ℚ) - 1) + (-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2) := by
    have h0 := congrArg (eval 0) hfact
    rw [eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
    rw [heval0, hF0] at h0
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h0
    have : (-1:(specialize (serreAnFamily n) t).SplittingField) ^ n * φ (1 / ((n:ℚ) - 1) + (-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2)
        = (-1) ^ n * ((-1) ^ n * ∏ i, w i) := by rw [h0]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  have hQ : ∏ i, (w i - 1)
      = (-1:(specialize (serreAnFamily n) t).SplittingField) ^ n * φ ((-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2) := by
    have h1 := congrArg (eval 1) hfact
    rw [eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [heval1, hF1] at h1
    simp_rw [← neg_sub (w _) 1] at h1
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h1
    have : (-1:(specialize (serreAnFamily n) t).SplittingField) ^ n * φ ((-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2)
        = (-1) ^ n * ((-1) ^ n * ∏ i, (w i - 1)) := by rw [h1]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  -- sign bookkeeping
  have hE : Even (n * (n - 1) / 2 + n * (n - 2) + n + n / 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rcases Nat.even_or_odd k with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · simp only [show p + p + 2 - 1 = p + p + 1 by omega, show p + p + 2 - 2 = p + p by omega]
      rw [show (p + p + 2) * (p + p + 1) / 2 = (p + 1) * (p + p + 1) by
            rw [show (p + p + 2) * (p + p + 1) = 2 * ((p + 1) * (p + p + 1)) by ring]; omega,
          show (p + p + 2) / 2 = p + 1 by omega]
      exact ⟨3 * p * p + 5 * p + 2, by ring⟩
    · simp only [show 2 * p + 1 + 2 - 1 = 2 * p + 2 by omega,
        show 2 * p + 1 + 2 - 2 = 2 * p + 1 by omega]
      rw [show (2 * p + 1 + 2) * (2 * p + 2) / 2 = (2 * p + 3) * (p + 1) by
            rw [show (2 * p + 1 + 2) * (2 * p + 2) = 2 * ((2 * p + 3) * (p + 1)) by ring]; omega,
          show (2 * p + 1 + 2) / 2 = p + 1 by omega]
      exact ⟨3 * p * p + 8 * p + 5, by ring⟩
  have hsign : (-1:(specialize (serreAnFamily n) t).SplittingField) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 2)) *
      (-1) ^ n * (-1) ^ (n / 2) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]; exact hE.neg_one_pow
  -- final assembly
  show (-1:(specialize (serreAnFamily n) t).SplittingField) ^ (n * (n - 1) / 2) *
      ∏ i, ∏ j ∈ Finset.univ.erase i, (w i - w j) = φ (serreAnDiscVal n t)
  rw [hK0, hP, hQ]
  simp only [serreAnDiscVal, map_mul, map_pow, map_natCast, map_neg, map_one, mul_pow]
  rw [← pow_mul]
  linear_combination
    ((n:(specialize (serreAnFamily n) t).SplittingField) ^ n *
      φ (1 / ((n:ℚ) - 1) + (-1:ℚ) ^ (n / 2) * (t:ℚ) ^ 2) ^ (n - 2) *
      φ (t:ℚ) ^ 2) * hsign

/-- **[algebraic core — the general discriminant identity]** For a separable specialization, with
any root-enumeration `v`, the `discSq` of the roots equals (the image of) the closed-form rational
discriminant `serreAnDiscVal n t`.  This holds for **both** parities of `n`; the parity only
matters for whether the result is a *square*.  Assembled from the general combinatorial identity
`discElem_sq_eq_sign_mul_prod_erase` and the family value `serreAnFamily_signed_prod_erase_val`. -/
theorem serreAnFamily_discSq_val (n : ℕ) (hn : 2 ≤ n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamily n) t).rootSet
        (specialize (serreAnFamily n) t).SplittingField) :
    discSq (fun i => (v i : (specialize (serreAnFamily n) t).SplittingField)) =
      algebraMap ℚ (specialize (serreAnFamily n) t).SplittingField (serreAnDiscVal n t) := by
  rw [discSq, discElem_sq_eq_sign_mul_prod_erase (fun i => (v i :
    (specialize (serreAnFamily n) t).SplittingField))]
  exact serreAnFamily_signed_prod_erase_val n hn t hsep v

/-- **[algebraic core — even case, the discriminant-square identity]** For **even** `n` and a
separable specialization, with any root-enumeration `v`, the `discSq` of the roots equals the
square of the explicit rational `serreAnDelta n t`.  Immediate from the general discriminant
value `serreAnFamily_discSq_val` and the even-parity square identity `serreAnDelta_sq_eq`. -/
theorem serreAnFamily_discSq_eq_even (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable)
    (v : Fin n ≃ (specialize (serreAnFamily n) t).rootSet
        (specialize (serreAnFamily n) t).SplittingField) :
    discSq (fun i => (v i : (specialize (serreAnFamily n) t).SplittingField)) =
      (algebraMap ℚ (specialize (serreAnFamily n) t).SplittingField (serreAnDelta n t)) ^ 2 := by
  rw [serreAnFamily_discSq_val n hn t hsep v, ← serreAnDelta_sq_eq n hn heven t, map_pow]

/-- **[algebraic core — the discriminant-square certificate, separable case]** Whenever the
specialization is separable (so its `n` roots are distinct and a root-enumeration exists), the
`discSq` of the roots is a perfect square in `ℚ`.  This is the honestly-scoped heart of the
`Aₙ` descent for the concrete family: it isolates the general-degree-`n` discriminant identity
"`disc_X(serreAnFamily n)` is identically a square in `ℚ[T]`" from the (separately false, at the
finitely many bad `t`) demand that a `Fin n ≃ rootSet` exist unconditionally.

**SCOPE — `Even n`.** `serreAnFamily` is Serre's **even-`n`** substituted family: its closed-form
`X`-discriminant is `nⁿ · t² · qⁿ⁻²` with `q = 1/(n−1) + (−1)^{n/2} t²`, which is a rational square
exactly when `n` is even.  (For odd `n` it is `nⁿ⁻¹·n·t²·qⁿ⁻²`, *not* a square in general — e.g.
`n = 3, t = 1` gives `disc = −27/2 < 0`; odd `n` is handled by the separate conic family
`serreAnFamilyOdd`.)  Hence the `Even n` hypothesis; the certificate is then discharged by the
even-parity square identity `serreAnFamily_discSq_eq_even`. -/
theorem serreAnFamily_disc_isSquare_of_separable (n : ℕ) (hn : 2 ≤ n) (heven : Even n) (t : ℤ)
    (hsep : (specialize (serreAnFamily n) t).Separable) :
    ∃ v : Fin n ≃ (specialize (serreAnFamily n) t).rootSet
        (specialize (serreAnFamily n) t).SplittingField,
      ∃ d : ℚ, discSq (fun i => (v i : (specialize (serreAnFamily n) t).SplittingField)) =
        (algebraMap ℚ (specialize (serreAnFamily n) t).SplittingField d) ^ 2 := by
  obtain ⟨v⟩ := serreAnFamily_rootEnum_nonempty n hn t hsep
  exact ⟨v, serreAnDelta n t, serreAnFamily_discSq_eq_even n hn heven t hsep v⟩

end AlternatingFamily

end
