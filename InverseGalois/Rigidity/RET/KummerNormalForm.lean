/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.MultiKummer

/-!
# Rational functions modulo `n`-th powers

A cyclic cover of the line of degree `n` is a Kummer cover `wⁿ = a` for some rational function `a`
(this is Kummer theory, `Mathlib/FieldTheory/KummerExtension.lean`), and `a` matters only modulo
`n`-th powers.  Over an algebraically closed field of constants every rational function is, modulo
`n`-th powers, a product of linear polynomials `T - p` with exponents `< n`: the constants are
`n`-th powers because the field is algebraically closed, and the linear factors of the numerator
and the denominator can be collected with their multiplicities reduced modulo `n`.

This module proves exactly that, in the shape the multi-point Kummer cover of `MultiKummer`
consumes: `a = (∏ᵢ (T - tᵢ)^{eᵢ}) · bⁿ` with the `tᵢ` distinct and `eᵢ < n`.

## Main definitions

* `Rigidity.RET.linProd` — the product of the linear polynomials listed by a multiset of points.
* `Rigidity.RET.IsLinPow` — being a product of linear polynomials with an `n`-th power.

## Main results

* `Rigidity.RET.isLinPow_of_ne_zero` — every nonzero rational function is such a product.
* `Rigidity.RET.exists_multiA_mul_pow` — the normal form with distinct points and exponents `< n`.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ### Products of linear polynomials -/

/-- The product of the linear polynomials `T - p`, with `p` running over a multiset of points of
`ℚ̄`, read in `ℚ̄(T)`. -/
def linProd (m : Multiset k) : RatFunc k :=
  (m.map fun p => algebraMap (Polynomial k) (RatFunc k) (X - C p)).prod

@[simp]
theorem linProd_zero : linProd (0 : Multiset k) = 1 := by simp [linProd]

theorem linProd_add (m m' : Multiset k) : linProd (m + m') = linProd m * linProd m' := by
  simp [linProd, Multiset.prod_add]

theorem linProd_ne_zero (m : Multiset k) : linProd m ≠ 0 := by
  refine Multiset.prod_ne_zero fun h => ?_
  obtain ⟨p, -, hp⟩ := Multiset.mem_map.mp h
  exact X_sub_C_ne_zero p (IsFractionRing.injective (Polynomial k) (RatFunc k)
    (hp.trans (map_zero _).symm))

theorem linProd_replicate (j : ℕ) (p : k) :
    linProd (Multiset.replicate j p) = algebraMap (Polynomial k) (RatFunc k) (X - C p) ^ j := by
  simp [linProd, Multiset.map_replicate, Multiset.prod_replicate]

/-! ### Every rational function is a product of linear polynomials and an `n`-th power -/

/-- A rational function is a product of linear polynomials with an `n`-th power. -/
def IsLinPow (n : ℕ) (a : RatFunc k) : Prop :=
  ∃ (m : Multiset k) (b : RatFunc k), b ≠ 0 ∧ a = linProd m * b ^ n

/-- **A nonzero polynomial is a product of linear polynomials and an `n`-th power.**  The linear
factors are its roots — the field of constants is algebraically closed — and the leading
coefficient is an `n`-th power for the same reason. -/
theorem isLinPow_polynomial {n : ℕ} (hn : 0 < n) {p : Polynomial k} (hp : p ≠ 0) :
    IsLinPow n (algebraMap (Polynomial k) (RatFunc k) p) := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq p.leadingCoeff hn
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hp (leadingCoeff_eq_zero.mp (by rw [← hd, zero_pow hn.ne']))
  refine ⟨p.roots, algebraMap (Polynomial k) (RatFunc k) (C d), ?_, ?_⟩
  · exact fun h => hd0 (C_eq_zero.mp (IsFractionRing.injective (Polynomial k) (RatFunc k)
      (h.trans (map_zero _).symm)))
  · conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
    rw [map_mul, map_multiset_prod, Multiset.map_map, ← map_pow, ← C_pow, hd, mul_comm]
    rfl

/-- **Every nonzero rational function is a product of linear polynomials and an `n`-th power.** -/
theorem isLinPow_of_ne_zero {n : ℕ} (hn : 0 < n) {a : RatFunc k} (ha : a ≠ 0) : IsLinPow n a := by
  have hden : a.denom ≠ 0 := a.denom_ne_zero
  have hnum : a.num ≠ 0 := RatFunc.num_ne_zero ha
  have hD : algebraMap (Polynomial k) (RatFunc k) a.denom ≠ 0 := fun h =>
    hden (IsFractionRing.injective (Polynomial k) (RatFunc k) (h.trans (map_zero _).symm))
  obtain ⟨m, b, hb, hval⟩ :=
    isLinPow_polynomial hn (mul_ne_zero hnum (pow_ne_zero (n - 1) hden))
  have hnd : a = algebraMap (Polynomial k) (RatFunc k) a.num
      * (algebraMap (Polynomial k) (RatFunc k) a.denom)⁻¹ := by
    conv_lhs => rw [← RatFunc.num_div_denom a]
    rw [div_eq_mul_inv]
  have hpow : (algebraMap (Polynomial k) (RatFunc k) a.denom) ^ n
      = (algebraMap (Polynomial k) (RatFunc k) a.denom) ^ (n - 1)
        * algebraMap (Polynomial k) (RatFunc k) a.denom := by
    rw [← pow_succ]
    congr 1
    omega
  refine ⟨m, b * (algebraMap (Polynomial k) (RatFunc k) a.denom)⁻¹,
    mul_ne_zero hb (inv_ne_zero hD), ?_⟩
  rw [mul_pow, ← mul_assoc, ← hval, map_mul, map_pow]
  conv_lhs => rw [hnd]
  rw [inv_pow, hpow]
  field_simp

/-! ### Reducing the exponents modulo `n` -/

open scoped Classical in
/-- The multiplicities of the linear factors can be taken `< n`: a block of `n` equal factors is
an `n`-th power. -/
theorem exists_count_lt {n : ℕ} (hn : 0 < n) :
    ∀ (N : ℕ) (m : Multiset k), m.card ≤ N → ∀ b : RatFunc k, b ≠ 0 →
      ∃ (m' : Multiset k) (b' : RatFunc k), b' ≠ 0 ∧ (∀ p, m'.count p < n) ∧
        linProd m * b ^ n = linProd m' * b' ^ n := by
  intro N
  induction N with
  | zero =>
      intro m hm b hb
      have hm0 : m = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hm)
      subst hm0
      exact ⟨0, b, hb, fun p => by simpa using hn, rfl⟩
  | succ N ih =>
      intro m hm b hb
      by_cases hex : ∃ p, n ≤ m.count p
      · obtain ⟨p, hp⟩ := hex
        obtain ⟨m₀, rfl⟩ :=
          Multiset.le_iff_exists_add.mp (Multiset.le_count_iff_replicate_le.mp hp)
        have hcard : m₀.card ≤ N := by
          have := Multiset.card_add (Multiset.replicate n p) m₀
          rw [Multiset.card_replicate] at this
          omega
        obtain ⟨m', b', hb', hcount, heq⟩ := ih m₀ hcard
          (b * algebraMap (Polynomial k) (RatFunc k) (X - C p)) (by
            refine mul_ne_zero hb fun h => ?_
            exact X_sub_C_ne_zero p (IsFractionRing.injective (Polynomial k) (RatFunc k)
              (h.trans (map_zero _).symm)))
        refine ⟨m', b', hb', hcount, ?_⟩
        rw [← heq, linProd_add, linProd_replicate, mul_pow]
        ring
      · push_neg at hex
        exact ⟨m, b, hb, hex, rfl⟩

/-! ### The normal form -/

open scoped Classical in
/-- **Normal form of a rational function modulo `n`-th powers.**  Every nonzero rational function
over `ℚ̄` is `(∏ᵢ (T - tᵢ)^{eᵢ}) · bⁿ` for distinct points `tᵢ` and exponents `eᵢ < n`. -/
theorem exists_multiA_mul_pow {n : ℕ} (hn : 0 < n) {a : RatFunc k} (ha : a ≠ 0) :
    ∃ (r : ℕ) (t : Fin r → k) (e : Fin r → ℕ) (b : RatFunc k),
      Function.Injective t ∧ (∀ i, e i < n) ∧ b ≠ 0 ∧
      a = algebraMap (Polynomial k) (RatFunc k) (multiA t e) * b ^ n := by
  obtain ⟨m, b, hb, hval⟩ := isLinPow_of_ne_zero hn ha
  obtain ⟨m', b', hb', hcount, heq⟩ := exists_count_lt hn m.card m le_rfl b hb
  set s : Finset k := m'.toFinset with hs
  refine ⟨s.card, fun i => (s.equivFin.symm i : k),
    fun i => m'.count ((s.equivFin.symm i : k)), b', ?_, ?_, hb', ?_⟩
  · exact fun i j hij => s.equivFin.symm.injective (Subtype.ext hij)
  · exact fun i => hcount _
  · have hlin : algebraMap (Polynomial k) (RatFunc k)
        (multiA (fun i => ((s.equivFin.symm i : k)))
          (fun i => m'.count ((s.equivFin.symm i : k)))) = linProd m' := by
      rw [multiA, map_prod]
      simp only [map_pow]
      rw [linProd, Finset.prod_multiset_map_count, ← Finset.prod_coe_sort s
        (fun p => algebraMap (Polynomial k) (RatFunc k) (X - C p) ^ m'.count p)]
      exact Fintype.prod_equiv s.equivFin.symm _ _ fun i => rfl
    rw [hlin, ← heq, ← hval]

end Rigidity.RET
