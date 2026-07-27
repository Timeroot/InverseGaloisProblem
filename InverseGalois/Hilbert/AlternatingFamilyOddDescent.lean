/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamilyOdd
import InverseGalois.Hilbert.AlternatingFamilyDescent
import InverseGalois.Resolvent.AlternatingResolvent
import InverseGalois.Resolvent.AlternatingResolventDescent
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# The `δ`-descent of the `Aₙ`-orbit resolvent (Serre §4.5, **odd** `n`)

Odd-`n` mirror of `Hilbert/AlternatingFamilyDescent.lean`.  Where that file descends the
`Aₙ`-orbit resolvent of `serreAnFamily n` (even `n`) via the identical-square certificate
`serreAnDeltaPoly`, this file does the same for the conic-parametrised **odd**-`n` family
`serreAnFamilyOdd n`, whose `X`-discriminant is *identically a square in `ℚ[U]`* (the polynomial
lift `serreAnDeltaPolyOdd`).
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

open AlternatingResolvent AlternatingInvariants ResolventFamily

/-- **The `ℚ[U]` lift of `serreAnDeltaOdd`.** The explicit square root of the `X`-discriminant of
`serreAnFamilyOdd n`, as a polynomial in the coefficient variable `U`:
`serreAnDeltaPolyOdd n = C(n^{n-1}/(n-1)^{(n-1)/2}) · U · (C k − U²)^{(n-1)²/2}` with
`k = (−1)^{(n-1)/2}·n`. -/
def serreAnDeltaPolyOdd (n : ℕ) : Polynomial ℚ :=
  C ((n : ℚ) ^ (n - 1) / ((n : ℚ) - 1) ^ ((n - 1) / 2)) * X
    * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ ((n - 1) ^ 2 / 2)

/-- **The `ℚ[U]` closed-form `X`-discriminant of `serreAnFamilyOdd n`**:
`serreAnDiscValPolyOdd n = C(n^{2n-2}/(n-1)^{n-1}) · U² · (C k − U²)^{(n-1)²}`. -/
def serreAnDiscValPolyOdd (n : ℕ) : Polynomial ℚ :=
  C ((n : ℚ) ^ (2 * n - 2) / ((n : ℚ) - 1) ^ (n - 1)) * X ^ 2
    * (C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2) ^ ((n - 1) ^ 2)

/-- Evaluating `serreAnDeltaPolyOdd n` at an integer `t` recovers `serreAnDeltaOdd n t`. -/
theorem serreAnDeltaPolyOdd_eval (n : ℕ) (t : ℤ) :
    (serreAnDeltaPolyOdd n).eval (t : ℚ) = serreAnDeltaOdd n t := by
  simp only [serreAnDeltaPolyOdd, serreAnDeltaOdd, eval_mul, eval_C, eval_X, eval_pow, eval_sub]
  ring

/-- Evaluating `serreAnDiscValPolyOdd n` at an integer `t` recovers `serreAnDiscValOdd n t`. -/
theorem serreAnDiscValPolyOdd_eval (n : ℕ) (t : ℤ) :
    (serreAnDiscValPolyOdd n).eval (t : ℚ) = serreAnDiscValOdd n t := by
  simp only [serreAnDiscValPolyOdd, serreAnDiscValOdd, eval_mul, eval_C, eval_X, eval_pow, eval_sub]
  ring

/-- **[identical-square certificate, `ℚ[U]`]** For **odd** `n`, `serreAnDeltaPolyOdd n` squares to
the closed-form discriminant `serreAnDiscValPolyOdd n`. -/
theorem serreAnDeltaPolyOdd_sq (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    (serreAnDeltaPolyOdd n) ^ 2 = serreAnDiscValPolyOdd n := by
  -- Both sides are polynomials in `ℚ[X]` that agree at every integer point (via the pointwise
  -- square certificate `serreAnDeltaOdd_sq_eq`), hence agree identically.
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : (Set.range (fun t : ℤ => (t : ℚ))).Infinite :=
    Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)
  refine hinf.mono ?_
  rintro _ ⟨t, rfl⟩
  simp only [Set.mem_setOf_eq, eval_pow, serreAnDeltaPolyOdd_eval, serreAnDiscValPolyOdd_eval]
  exact serreAnDeltaOdd_sq_eq n hn hodd t

/-- **[Vieta transport, odd]** Mirror of `vieta_map` for `serreAnFamilyOdd`. -/
theorem vieta_map_odd {A : Type} [Field A] [Algebra ℚ A] (n : ℕ) (hn : 2 ≤ n)
    (ev : Polynomial ℚ →+* A) (x : Fin n → A)
    (halg : algebraMap ℚ A = ev.comp Polynomial.C)
    (hx : ((serreAnFamilyOdd n).map ev).natDegree = n)
    (hx' : ((serreAnFamilyOdd n).map ev).roots = Finset.univ.val.map x)
    (V W : Polynomial (MvPolynomial (Fin n) ℚ))
    (hVW : W.map (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i.val + 1))).toRingHom = V) :
    (W.map (MvPolynomial.aeval
        (fun i : Fin n => (-1 : Polynomial ℚ) ^ (i.val + 1)
          * (serreAnFamilyOdd n).coeff (n - (i.val + 1)))).toRingHom).map ev
      = V.map (MvPolynomial.aeval x).toRingHom := by
  have hF : (serreAnFamilyOdd n).Monic := serreAnFamilyOdd_monic n hn
  convert congr_arg (Polynomial.map ((MvPolynomial.aeval x).toRingHom)) hVW using 1
  rw [Polynomial.map_map, Polynomial.map_map]
  congr! 1
  ext i
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq, halg, RingHom.comp_apply]
  · have h_vieta : ev ((serreAnFamilyOdd n).coeff (n - (i.val + 1)))
        = (-1) ^ (i.val + 1) * (Finset.univ.val.map x).esymm (i.val + 1) := by
      have h_vieta_prod : ((serreAnFamilyOdd n).map ev)
          = Polynomial.C (ev ((serreAnFamilyOdd n).leadingCoeff))
            * Multiset.prod (Multiset.map (fun β => Polynomial.X - Polynomial.C β)
                (Finset.univ.val.map x)) := by
        convert Polynomial.Splits.eq_prod_roots_of_monic _ _
        all_goals try infer_instance
        · aesop
        · rw [Polynomial.splits_iff_card_roots]
          rw [hx', Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> aesop
        · exact hF.map ev
      convert congr_arg (fun p => p.coeff (n - (i.val + 1))) h_vieta_prod using 1
      · rw [Polynomial.coeff_map]
      · rw [Polynomial.coeff_C_mul, Multiset.prod_X_sub_C_coeff]
        · simp [hF.leadingCoeff]
          rw [Nat.sub_sub_self (by linarith [Fin.is_lt i])]
        · simp
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X, map_mul, map_pow, map_neg, map_one]
    rw [h_vieta, MvPolynomial.aeval_esymm_eq_multiset_esymm, ← mul_assoc, ← pow_add,
      Even.neg_one_pow (⟨i.val + 1, rfl⟩ : Even ((i.val + 1) + (i.val + 1))), one_mul]

/-- **[odd disc scalar identity]** The pure-`ℚ`, sign-cleaned closed form of the discriminant of
`specialize (serreAnFamilyOdd n) t`.  This is exactly the `hℚ` step of
`serreAnFamilyOdd_signed_prod_erase_val`, extracted so the general (arbitrary-`ev`) discriminant
identity can reuse it via polynomial infinite-agreement. -/
theorem serreAnFamilyOdd_disc_scalar (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) (t : ℤ) :
    (-1 : ℚ) ^ (n * (n - 1) / 2)
      * ((n : ℚ) ^ n
        * ((-1) ^ n * eval 0 (specialize (serreAnFamilyOdd n) t)) ^ (n - 2)
        * ((-1) ^ n
          * eval ((-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2)
              (specialize (serreAnFamilyOdd n) t)))
      = serreAnDiscValOdd n t := by
  set kq : ℚ := (-1 : ℚ) ^ ((n - 1) / 2) * n with hkq
  set κtq : ℚ := kq - (t : ℚ) ^ 2 with hκtq
  have hne1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hF0 : eval 0 (specialize (serreAnFamilyOdd n) t) = kq / ((n : ℚ) - 1) * κtq ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq, ← hκtq]
    simp [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
  have hFκ : eval κtq (specialize (serreAnFamilyOdd n) t)
      = (t : ℚ) ^ 2 / ((n : ℚ) - 1) * κtq ^ (n - 1) := by
    rw [specialize_serreAnFamilyOdd n t, ← hkq, ← hκtq]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    have hpow : κtq ^ n = κtq * κtq ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hpow]
    have hkey : κtq - (n : ℚ) / ((n : ℚ) - 1) * κtq + kq / ((n : ℚ) - 1)
        = (t : ℚ) ^ 2 / ((n : ℚ) - 1) := by
      rw [hκtq]; field_simp; ring
    linear_combination (κtq ^ (n - 1)) * hkey
  rw [hF0, hFκ, serreAnDiscValOdd, ← hkq, ← hκtq, hkq]
  obtain ⟨m, rfl⟩ := hodd
  rw [show (2 * m + 1 - 1) / 2 = m by omega]
  simp only [mul_pow, div_pow, ← pow_mul]
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
  have hRHSn : ((2 * m + 1 : ℕ) : ℚ) ^ (2 * (2 * m + 1) - 2)
      = ((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1) * ((2 * m + 1 : ℕ) : ℚ) ^ (2 * m + 1 - 2) := by
    rw [← pow_add]; congr 1; omega
  have hRHSκ : κtq ^ ((2 * m + 1 - 1) ^ 2)
      = κtq ^ ((2 * m + 1 - 1) * (2 * m + 1 - 2)) * κtq ^ (2 * m + 1 - 1) := by
    rw [← pow_add]; congr 1
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

/-- **[Step 1 — the general discriminant identity, odd]** For any field `A`, ring hom
`ev : ℚ[U] →+* A` and root-enumeration `x` describing a splitting of `serreAnFamilyOdd n`, the
square of the discriminant element equals `ev (serreAnDiscValPolyOdd n)`. -/
theorem serreAnFamilyOdd_discSq_general {A : Type*} [Field A] (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n)
    (ev : Polynomial ℚ →+* A) (x : Fin n → A)
    (hdeg : ((serreAnFamilyOdd n).map ev).natDegree = n)
    (hroots : ((serreAnFamilyOdd n).map ev).roots = Finset.univ.val.map x) :
    (discElem x) ^ 2 = ev (serreAnDiscValPolyOdd n) := by
  classical
  set Fm := (serreAnFamilyOdd n).map ev with hFm
  set κ : Polynomial ℚ := C ((-1 : ℚ) ^ ((n - 1) / 2) * n) - X ^ 2 with hκ
  set b : A := ev κ with hb
  have hmonicF : (serreAnFamilyOdd n).Monic := serreAnFamilyOdd_monic n hn
  have hFmMonic : Fm.Monic := hmonicF.map ev
  have hcard : Multiset.card Fm.roots = n := by
    rw [hroots, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hcard' : Multiset.card Fm.roots = Fm.natDegree := by rw [hcard, hdeg]
  have hfact : Fm = ∏ i, (X - C (x i)) := by
    have hh := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFmMonic hcard'
    rw [hroots, Multiset.map_map] at hh
    rw [← hh]; rfl
  -- per-root: derivative eval = product over the other roots
  have hderiv_eval : ∀ i, eval (x i) (derivative Fm) = ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
    intro i
    rw [hfact, derivative_prod_finset, eval_finset_sum]
    rw [Finset.sum_eq_single i]
    · simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, eval_prod,
        eval_sub, eval_X, eval_C]
    · intro a _ hai
      rw [eval_mul]
      apply mul_eq_zero_of_left
      rw [eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hai, Finset.mem_univ i⟩)
        (by rw [eval_sub, eval_X, eval_C, sub_self])
    · intro h; exact absurd (Finset.mem_univ i) h
  -- the derivative in closed form (odd family: second coefficient `n·(k − U²)`)
  have hderiv : derivative Fm = C (n : A) * X ^ (n - 1) - C ((n : A) * b) * X ^ (n - 2) := by
    rw [hFm, Polynomial.derivative_map, serreAnFamilyOdd_derivative n hn]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C]
    rw [← hκ, map_mul, ← hb]
    simp only [map_natCast]
  have hev : ∀ i, eval (x i) (derivative Fm) = (n : A) * x i ^ (n - 2) * (x i - b) := by
    intro i
    rw [hderiv]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hK0 : ∏ i, ∏ j ∈ Finset.univ.erase i, (x i - x j)
      = (n : A) ^ n * (∏ i, x i) ^ (n - 2) * ∏ i, (x i - b) := by
    have hterm : ∀ i, ∏ j ∈ Finset.univ.erase i, (x i - x j)
        = (n : A) * x i ^ (n - 2) * (x i - b) := fun i => (hderiv_eval i).symm.trans (hev i)
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
      Finset.card_univ, Fintype.card_fin]
  -- eval-transport of Fm at `0` and at `b = ev κ`
  have heval0 : eval (0 : A) Fm = ev (eval (0 : Polynomial ℚ) (serreAnFamilyOdd n)) := by
    rw [hFm, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have hevalb : eval b Fm = ev (eval κ (serreAnFamilyOdd n)) := by
    rw [hb, hFm, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  -- Vieta: products of roots and of `(root − b)`
  have hP : ∏ i, x i = (-1 : A) ^ n * ev (eval (0 : Polynomial ℚ) (serreAnFamilyOdd n)) := by
    have h0 := congrArg (eval (0 : A)) hfact
    rw [heval0, eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h0
    have : (-1 : A) ^ n * ev (eval (0 : Polynomial ℚ) (serreAnFamilyOdd n))
        = (-1) ^ n * ((-1) ^ n * ∏ i, x i) := by rw [h0]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  have hQ : ∏ i, (x i - b) = (-1 : A) ^ n * ev (eval κ (serreAnFamilyOdd n)) := by
    have h1 := congrArg (eval b) hfact
    rw [hevalb, eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    simp_rw [← neg_sub (x _) b] at h1
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin] at h1
    have : (-1 : A) ^ n * ev (eval κ (serreAnFamilyOdd n))
        = (-1) ^ n * ((-1) ^ n * ∏ i, (x i - b)) := by rw [h1]
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul] at this
    exact this.symm
  -- the `ℚ[U]`-level sign-cleaned closed form, lifted from the scalar identity by infinite agreement
  have hpolyid : (-1 : Polynomial ℚ) ^ (n * (n - 1) / 2)
        * ((n : Polynomial ℚ) ^ n
          * ((-1) ^ n * eval (0 : Polynomial ℚ) (serreAnFamilyOdd n)) ^ (n - 2)
          * ((-1) ^ n * eval κ (serreAnFamilyOdd n)))
      = serreAnDiscValPolyOdd n := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : (Set.range (fun t : ℤ => (t : ℚ))).Infinite :=
      Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)
    refine hinf.mono ?_
    rintro _ ⟨t, rfl⟩
    rw [Set.mem_setOf_eq]
    have htr : ∀ c : Polynomial ℚ, eval (t : ℚ) (eval c (serreAnFamilyOdd n))
        = eval (eval (t : ℚ) c) (specialize (serreAnFamilyOdd n) t) := by
      intro c
      rw [specialize, show eval (t : ℚ) c = Polynomial.evalRingHom (t : ℚ) c from rfl,
        Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.coe_evalRingHom]
    have hκt : eval (t : ℚ) κ = (-1 : ℚ) ^ ((n - 1) / 2) * n - (t : ℚ) ^ 2 := by
      rw [hκ]; simp [eval_sub, eval_pow, eval_X]
    simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_natCast, serreAnDiscValPolyOdd_eval]
    rw [htr, htr, eval_zero, hκt]
    exact serreAnFamilyOdd_disc_scalar n hn hodd t
  -- final assembly: push `ev` through the closed form
  rw [discElem_sq_eq_sign_mul_prod_erase x, hK0, hP, hQ, ← hpolyid]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

/-- **[Step 2 — descent identity, odd]** For `n ≥ 2`, `Odd n`, there is a `G ∈ ℚ[U][Y]` coupled to
`serreAnFamilyOdd n` by `IsAltResolvent`. -/
theorem altResolvent_identity_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    ∃ G : Polynomial (Polynomial ℚ), IsAltResolvent n (serreAnFamilyOdd n) G := by
  classical
  set U : Polynomial (MvPolynomial (Fin n) ℚ) :=
    altResolventProduct n (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) with hU
  choose s t hs ht hst using fun k => altResolventProduct_coeff_symm_add_vander_mul_symm n k hn
  set Us : Polynomial (MvPolynomial (Fin n) ℚ) :=
    ∑ i ∈ U.support, Polynomial.monomial i (s i) with hUs
  set Ut : Polynomial (MvPolynomial (Fin n) ℚ) :=
    ∑ i ∈ U.support, Polynomial.monomial i (t i) with hUt
  have hUs_coeff : ∀ k, Us.coeff k = if k ∈ U.support then s k else 0 := by
    intro k
    rw [hUs, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' U.support k]
  have hUt_coeff : ∀ k, Ut.coeff k = if k ∈ U.support then t k else 0 := by
    intro k
    rw [hUt, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' U.support k]
  have hUs_symm : ∀ k, (Us.coeff k).IsSymmetric := by
    intro k; rw [hUs_coeff]; split
    · exact hs k
    · intro e; simp
  have hUt_symm : ∀ k, (Ut.coeff k).IsSymmetric := by
    intro k; rw [hUt_coeff]; split
    · exact ht k
    · intro e; simp
  have hU_decomp : U = Us + Polynomial.C (AlternatingInvariants.vander n) * Ut := by
    refine Polynomial.ext (fun k => ?_)
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, hUs_coeff, hUt_coeff]
    by_cases hk : k ∈ U.support
    · simp only [hk, if_true]; exact hst k
    · simp only [hk, if_false, mul_zero, add_zero]
      simpa [Polynomial.mem_support_iff] using hk
  obtain ⟨Shat, hShat⟩ := ResolventFamily.exists_esymm_lift_rat n Us hUs_symm
  obtain ⟨That, hThat⟩ := ResolventFamily.exists_esymm_lift_rat n Ut hUt_symm
  set cval : MvPolynomial (Fin n) ℚ →+* Polynomial ℚ :=
    (MvPolynomial.aeval
      (fun i : Fin n => (-1 : Polynomial ℚ) ^ (i.val + 1)
        * (serreAnFamilyOdd n).coeff (n - (i.val + 1)))).toRingHom with hcval
  refine ⟨Shat.map cval + Polynomial.C (serreAnDeltaPolyOdd n) * That.map cval, ?_⟩
  intro A _ ev x hdeg hroots
  letI : Algebra ℚ A := (ev.comp Polynomial.C).toAlgebra
  have halg : algebraMap ℚ A = ev.comp Polynomial.C := rfl
  have hmapS : (Shat.map cval).map ev = Us.map (MvPolynomial.aeval x).toRingHom := by
    rw [hcval]; exact vieta_map_odd n hn ev x halg hdeg hroots Us Shat hShat
  have hmapT : (That.map cval).map ev = Ut.map (MvPolynomial.aeval x).toRingHom := by
    rw [hcval]; exact vieta_map_odd n hn ev x halg hdeg hroots Ut That hThat
  have hGmapev : (Shat.map cval + Polynomial.C (serreAnDeltaPolyOdd n) * That.map cval).map ev
      = Us.map (MvPolynomial.aeval x).toRingHom
        + Polynomial.C (ev (serreAnDeltaPolyOdd n)) * Ut.map (MvPolynomial.aeval x).toRingHom := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hmapS, hmapT]
  have haltprod : ∀ x' : Fin n → A, altResolventProduct n x'
      = Us.map (MvPolynomial.aeval x').toRingHom
        + Polynomial.C (discElem x') * Ut.map (MvPolynomial.aeval x').toRingHom := by
    intro x'
    have h1 : U.map (MvPolynomial.aeval x').toRingHom = altResolventProduct n x' := by
      rw [hU, altResolventProduct_map]
      congr 1
      funext i
      simp
    rw [← h1, hU_decomp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [discElem_eq_aeval_vander x']
  have hsq : (discElem x) ^ 2 = (ev (serreAnDeltaPolyOdd n)) ^ 2 := by
    rw [serreAnFamilyOdd_discSq_general n hn hodd ev x hdeg hroots,
      ← serreAnDeltaPolyOdd_sq n hn hodd, map_pow]
  have hcases : discElem x = ev (serreAnDeltaPolyOdd n) ∨
      discElem x = -(ev (serreAnDeltaPolyOdd n)) := by
    have hfac : (discElem x - ev (serreAnDeltaPolyOdd n))
        * (discElem x + ev (serreAnDeltaPolyOdd n)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with hpos | hneg
  · refine ⟨x, hroots, ?_⟩
    rw [hGmapev, haltprod x, hpos]
  · set τ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ with hτ
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have hreindex : Finset.univ.val.map (x ∘ τ) = Finset.univ.val.map x := by
      have h1 : Finset.univ.val.map (⇑τ) = Finset.univ.val := by
        have h := congrArg Finset.val (Finset.map_univ_equiv τ)
        rw [Finset.map_val, Equiv.coe_toEmbedding] at h
        exact h
      rw [← Multiset.map_map, h1]
    have hsymm_map : ∀ (W : Polynomial (MvPolynomial (Fin n) ℚ)),
        (∀ k, (W.coeff k).IsSymmetric) →
        W.map (MvPolynomial.aeval (x ∘ τ)).toRingHom = W.map (MvPolynomial.aeval x).toRingHom := by
      intro W hW
      ext k
      simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [← MvPolynomial.aeval_rename, (hW k) τ]
    have hdisc' : discElem (x ∘ τ) = ev (serreAnDeltaPolyOdd n) := by
      rw [discElem_perm x τ, hτ, Equiv.Perm.sign_swap hne]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      rw [hneg]; ring
    refine ⟨x ∘ τ, ?_, ?_⟩
    · rw [hroots, hreindex]
    · rw [hGmapev, haltprod (x ∘ τ), hsymm_map Us hUs_symm, hsymm_map Ut hUt_symm, hdisc']

/-- **[Step 3 — descended resolvent with degree/monicity, odd]**. -/
theorem exists_descended_altResolvent_odd (n : ℕ) (hn : 2 ≤ n) (hodd : Odd n) :
    ∃ G : Polynomial (Polynomial ℚ), G.Monic ∧ G.natDegree = n.factorial / 2 ∧
      IsAltResolvent n (serreAnFamilyOdd n) G := by
  obtain ⟨G, hG⟩ := altResolvent_identity_odd n hn hodd
  set K := AlgebraicClosure (FractionRing (Polynomial ℚ))
  set ev₀ : Polynomial ℚ →+* K :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) with hev₀
  have hinj : Function.Injective ev₀ :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  have hmono : (serreAnFamilyOdd n).Monic := serreAnFamilyOdd_monic n hn
  have hlc : ev₀ ((serreAnFamilyOdd n).leadingCoeff) ≠ 0 := by
    rw [hmono.leadingCoeff, map_one]; exact one_ne_zero
  have hdeg₀ : ((serreAnFamilyOdd n).map ev₀).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero ev₀ hlc, serreAnFamilyOdd_natDegree n hn]
  have hsplit : ((serreAnFamilyOdd n).map ev₀).Splits := IsAlgClosed.splits _
  have hcard : ((serreAnFamilyOdd n).map ev₀).roots.card = n :=
    (Polynomial.splits_iff_card_roots.mp hsplit).trans hdeg₀
  obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq ((serreAnFamilyOdd n).map ev₀).roots n hcard
  obtain ⟨x', -, hGmap⟩ := hG ev₀ x hdeg₀ hx.symm
  refine ⟨G, ?_, ?_, hG⟩
  · have hm : (G.map ev₀).leadingCoeff = 1 := by
      rw [hGmap]; exact altResolventProduct_monic n x'
    rw [Polynomial.leadingCoeff_map_of_injective hinj] at hm
    exact hinj (hm.trans (map_one ev₀).symm)
  · have hd : (G.map ev₀).natDegree = n.factorial / 2 := by
      rw [hGmap]; exact altResolventProduct_natDegree n hn x'
    rwa [Polynomial.natDegree_map_eq_of_injective hinj] at hd

/-- **[Step 4 — root property, odd]**. -/
theorem altResolvent_root_property_odd (n : ℕ) (hn : 2 ≤ n) (G : Polynomial (Polynomial ℚ))
    (hG : IsAltResolvent n (serreAnFamilyOdd n) G) :
    ∀ t : ℤ, ∃ α : (specialize (serreAnFamilyOdd n) t).SplittingField,
      (aeval α) (specialize G t) = 0 := by
  intro t
  set A := (specialize (serreAnFamilyOdd n) t).SplittingField
  set ι := algebraMap ℚ A
  set ev := ι.comp (Polynomial.evalRingHom (t : ℚ))
  have hmono : (serreAnFamilyOdd n).Monic := serreAnFamilyOdd_monic n hn
  obtain ⟨x, hx⟩ : ∃ x : Fin n → A, Finset.univ.val.map x = ((serreAnFamilyOdd n).map ev).roots := by
    apply ResolventConstruction.exists_fin_map_eq
    have h_card_roots : ((serreAnFamilyOdd n).map ev).roots.card = ((serreAnFamilyOdd n).map ev).natDegree := by
      convert Polynomial.splits_iff_card_roots.mp _
      convert Polynomial.SplittingField.splits (specialize (serreAnFamilyOdd n) t) using 1
      unfold specialize
      aesop
    rw [h_card_roots, Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;>
      simp_all [serreAnFamilyOdd_natDegree n hn]
  obtain ⟨x', -, hGmap⟩ := hG ev x
    (by rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;>
      simp_all [serreAnFamilyOdd_natDegree n hn]) hx.symm
  use genForm n x' (1 : Equiv.Perm (Fin n))
  convert congr_arg (Polynomial.eval (genForm n x' 1)) hGmap using 1
  · simp only [aeval_def, specialize, Polynomial.eval_map, Polynomial.eval₂_map]
    rfl
  · exact (altResolventProduct_isRoot_genForm_one n x').symm

end AlternatingFamily

end
