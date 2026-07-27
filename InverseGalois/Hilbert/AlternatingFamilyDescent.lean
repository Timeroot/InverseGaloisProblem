/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.AlternatingFamilyDisc
import InverseGalois.Resolvent.AlternatingResolvent
import InverseGalois.Resolvent.AlternatingResolventDescent
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# The `δ`-descent of the `Aₙ`-orbit resolvent (Serre §4.5, even `n`)

The structural core still missing from `AlternatingFamily.exists_altResolvent`: the descent of the
`Aₙ`-orbit resolvent `∏_{σ∈Aₙ}(Y − w_σ)` of the concrete family `serreAnFamily n` to a genuine
`G ∈ ℚ[T][Y]`.  Unlike the `Sₙ` resolvent (`ResolventFamily.fullResolvent_identity`), whose
coefficients are *symmetric* and descend along Vieta directly, the `Aₙ`-orbit coefficients descend
only as `s + δ·t` with `s, t` symmetric and `δ = √disc` the Vandermonde
(`AlternatingResolvent.altResolventProduct_coeff_symm_add_vander_mul_symm`).  They become genuinely
rational precisely because `disc(serreAnFamily n)` is an **identical square** in `ℚ[T]` (even `n`);
the explicit square root is `serreAnDeltaPoly n` built here.

## The `ℚ[T]` identical-square certificate

`serreAnDeltaPoly n` is the polynomial-in-`T` lift of Agent C's per-point root
`AlternatingFamily.serreAnDelta`, and `serreAnDeltaPoly_sq` proves it squares to the closed-form
discriminant `serreAnDiscValPoly n` (for even `n`) — the identical-square certificate as a bare
`ℚ[T]` identity, the polynomial-level upgrade of `serreAnFamily.serreAnDelta_sq_eq`.

## The Vandermonde bridge

`discElem_eq_aeval_vander`: the field-level discriminant element `discElem v = ∏_{i<j}(vⱼ−vᵢ)`
(`PolynomialGaloisTheory`) is *definitionally* the evaluation of the invariant-theoretic
Vandermonde `AlternatingInvariants.vander n` at `v`.  This is what couples the descent's `δ·t`
term to the concrete `√disc`: at a splitting specialisation with root-enumeration `x`, the
`Aₙ`-orbit coefficient's `δ`-part is `discElem x = ±(ev serreAnDeltaPoly)`, the sign selecting the
coset-orientation `x'` in `IsAltResolvent`.
-/

open Polynomial

noncomputable section

namespace AlternatingFamily

open AlternatingResolvent AlternatingInvariants ResolventFamily

/-- **The `ℚ[T]` lift of `serreAnDelta`.** The explicit square root of the `X`-discriminant of
`serreAnFamily n`, as a polynomial in the coefficient variable `T`:
`serreAnDeltaPoly n = n^{n/2} · T · (1/(n−1) + (−1)^{n/2} T²)^{n/2−1}`. -/
def serreAnDeltaPoly (n : ℕ) : Polynomial ℚ :=
  C ((n : ℚ) ^ (n / 2)) * X
    * (C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2) ^ (n / 2 - 1)

/-- **The `ℚ[T]` closed-form `X`-discriminant of `serreAnFamily n`** (parity-independent value):
`serreAnDiscValPoly n = n^n · T² · (1/(n−1) + (−1)^{n/2} T²)^{n−2}`. -/
def serreAnDiscValPoly (n : ℕ) : Polynomial ℚ :=
  C ((n : ℚ) ^ n) * X ^ 2
    * (C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2) ^ (n - 2)

/-- Evaluating `serreAnDeltaPoly n` at an integer `t` recovers Agent C's per-point root
`serreAnDelta n t`. -/
theorem serreAnDeltaPoly_eval (n : ℕ) (t : ℤ) :
    (serreAnDeltaPoly n).eval (t : ℚ) = serreAnDelta n t := by
  simp [serreAnDeltaPoly, serreAnDelta]

/-- Evaluating `serreAnDiscValPoly n` at an integer `t` recovers `serreAnDiscVal n t`. -/
theorem serreAnDiscValPoly_eval (n : ℕ) (t : ℤ) :
    (serreAnDiscValPoly n).eval (t : ℚ) = serreAnDiscVal n t := by
  simp [serreAnDiscValPoly, serreAnDiscVal]

/-- **[identical-square certificate, `ℚ[T]`]** For **even** `n`, `serreAnDeltaPoly n` squares to
the closed-form discriminant `serreAnDiscValPoly n`: the polynomial-level upgrade of
`serreAnDelta_sq_eq`.  (`n = 2m`: `(n^{m})² = n^{2m} = nⁿ`, `T·T = T²`, and
`(q^{m−1})² = q^{2m−2} = q^{n−2}`.) -/
theorem serreAnDeltaPoly_sq (n : ℕ) (heven : Even n) :
    (serreAnDeltaPoly n) ^ 2 = serreAnDiscValPoly n := by
  obtain ⟨m, rfl⟩ := heven
  have h2 : (m + m) / 2 = m := by omega
  simp only [serreAnDeltaPoly, serreAnDiscValPoly, h2]
  rw [mul_pow, mul_pow, ← C_pow, ← pow_mul, ← pow_mul,
      show m * 2 = m + m from by ring, show (m - 1) * 2 = m + m - 2 from by omega]

/-- **The Vandermonde bridge.** The field-level discriminant element `discElem v = ∏_{i<j}(vⱼ−vᵢ)`
is the evaluation of the invariant-theoretic Vandermonde `vander n` at `v`.  Both are the same
product `∏_i ∏_{j∈Ioi i}(vⱼ − vᵢ)`, so this is essentially definitional (via `aeval` on the
product). -/
theorem discElem_eq_aeval_vander {L : Type*} [Field L] [Algebra ℚ L] {n : ℕ} (v : Fin n → L) :
    MvPolynomial.aeval v (vander n) = discElem v := by
  simp only [vander, discElem, map_prod, map_sub, MvPolynomial.aeval_X]

/-- **The coupling predicate** (defined here, imported by the analytic file, to break the import
cycle).  `G ∈ ℚ[T][Y]` is the descended `Aₙ`-orbit resolvent of `F ∈ ℚ[T][X]`. -/
def IsAltResolvent (n : ℕ) (F G : Polynomial (Polynomial ℚ)) : Prop :=
  ∀ {A : Type} [Field A] (ev : Polynomial ℚ →+* A) (x : Fin n → A),
    (F.map ev).natDegree = n →
    (F.map ev).roots = Finset.univ.val.map x →
    ∃ x' : Fin n → A,
      (F.map ev).roots = Finset.univ.val.map x' ∧
      G.map ev = altResolventProduct n x'

/-- **[Vieta transport]** Mirror of the core of `ResolventFamily.fullResolvent_identity`: if `W`
is the elementary-symmetric lift of `V`, then mapping `W` through the Vieta substitution
(`X_i ↦ (-1)^{i+1} F.coeff (n-(i+1))`) and then specialising by `ev` equals mapping `V` by
`aeval x`, whenever `ev`/`x` describe a splitting of `serreAnFamily n`. -/
theorem vieta_map {A : Type} [Field A] [Algebra ℚ A] (n : ℕ) (hn : 2 ≤ n)
    (ev : Polynomial ℚ →+* A) (x : Fin n → A)
    (halg : algebraMap ℚ A = ev.comp Polynomial.C)
    (hx : ((serreAnFamily n).map ev).natDegree = n)
    (hx' : ((serreAnFamily n).map ev).roots = Finset.univ.val.map x)
    (V W : Polynomial (MvPolynomial (Fin n) ℚ))
    (hVW : W.map (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i.val + 1))).toRingHom = V) :
    (W.map (MvPolynomial.aeval
        (fun i : Fin n => (-1 : Polynomial ℚ) ^ (i.val + 1)
          * (serreAnFamily n).coeff (n - (i.val + 1)))).toRingHom).map ev
      = V.map (MvPolynomial.aeval x).toRingHom := by
  have hF : (serreAnFamily n).Monic := serreAnFamily_monic n hn
  convert congr_arg (Polynomial.map ((MvPolynomial.aeval x).toRingHom)) hVW using 1
  rw [Polynomial.map_map, Polynomial.map_map]
  congr! 1
  ext i
  · simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq, halg, RingHom.comp_apply]
  · have h_vieta : ev ((serreAnFamily n).coeff (n - (i.val + 1)))
        = (-1) ^ (i.val + 1) * (Finset.univ.val.map x).esymm (i.val + 1) := by
      have h_vieta_prod : ((serreAnFamily n).map ev)
          = Polynomial.C (ev ((serreAnFamily n).leadingCoeff))
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

/-- **[Step 1 — the general discriminant identity]** For any field `A`, ring hom
`ev : ℚ[T] →+* A` and root-enumeration `x` describing a splitting of `serreAnFamily n`, the
square of the discriminant element equals `ev (serreAnDiscValPoly n)`.  Generalises
`serreAnFamily_signed_prod_erase_val` from integer specialisations to arbitrary `ev`. -/
theorem serreAnFamily_discSq_general {A : Type*} [Field A] (n : ℕ) (hn : 2 ≤ n)
    (ev : Polynomial ℚ →+* A) (x : Fin n → A)
    (hdeg : ((serreAnFamily n).map ev).natDegree = n)
    (hroots : ((serreAnFamily n).map ev).roots = Finset.univ.val.map x) :
    (discElem x) ^ 2 = ev (serreAnDiscValPoly n) := by
  classical
  set Fm := (serreAnFamily n).map ev with hFm
  have hmonicF : (serreAnFamily n).Monic := serreAnFamily_monic n hn
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
  -- the derivative in closed form
  have hderiv : derivative Fm = C (n : A) * X ^ (n - 1) - C (n : A) * X ^ (n - 2) := by
    rw [hFm, Polynomial.derivative_map, serreAnFamily_derivative n hn]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_natCast, map_natCast]
  have hev : ∀ i, eval (x i) (derivative Fm) = (n : A) * x i ^ (n - 2) * (x i - 1) := by
    intro i
    rw [hderiv]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hK0 : ∏ i, ∏ j ∈ Finset.univ.erase i, (x i - x j)
      = (n : A) ^ n * (∏ i, x i) ^ (n - 2) * ∏ i, (x i - 1) := by
    have hterm : ∀ i, ∏ j ∈ Finset.univ.erase i, (x i - x j)
        = (n : A) * x i ^ (n - 2) * (x i - 1) := fun i => (hderiv_eval i).symm.trans (hev i)
    simp_rw [hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
      Finset.card_univ, Fintype.card_fin]
  -- eval-transport of Fm at 0 and 1
  have heval0 : eval (0 : A) Fm = ev (eval (0 : Polynomial ℚ) (serreAnFamily n)) := by
    rw [hFm, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  have heval1 : eval (1 : A) Fm = ev (eval (1 : Polynomial ℚ) (serreAnFamily n)) := by
    have h1A : (1 : A) = ev 1 := (map_one ev).symm
    rw [hFm, Polynomial.eval_map, h1A, Polynomial.eval₂_at_apply]
  -- constant and at-1 values of serreAnFamily n (in ℚ[T])
  have hF0 : eval (0 : Polynomial ℚ) (serreAnFamily n)
      = C (1 / ((n : ℚ) - 1)) + C ((-1 : ℚ) ^ (n / 2)) * X ^ 2 := by
    simp only [serreAnFamily, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    rw [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
    ring
  have hF1 : eval (1 : Polynomial ℚ) (serreAnFamily n) = C ((-1 : ℚ) ^ (n / 2)) * X ^ 2 := by
    have hne1 : (n : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      linarith
    simp only [serreAnFamily, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, one_pow,
      mul_one]
    have h0 : (1 : Polynomial ℚ) - C ((n : ℚ) / ((n : ℚ) - 1)) + C (1 / ((n : ℚ) - 1)) = 0 := by
      rw [← C_1, ← C_sub, ← C_add,
        show (1 : ℚ) - (n : ℚ) / ((n : ℚ) - 1) + 1 / ((n : ℚ) - 1) = 0 from by field_simp; ring,
        C_0]
    linear_combination h0
  -- Vieta: products of roots and of (root − 1)
  have hP : ∏ i, x i = (-1 : A) ^ n * ev (eval (0 : Polynomial ℚ) (serreAnFamily n)) := by
    have h0 := congrArg (eval (0 : A)) hfact
    rw [heval0, eval_prod] at h0
    simp only [eval_sub, eval_X, eval_C, zero_sub] at h0
    have hswap0 : (∏ i : Fin n, (-x i : A)) = (-1 : A) ^ n * ∏ i, x i := by
      rw [show ((-1 : A)) ^ n = ∏ _i : Fin n, (-1 : A) by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
          ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by ring)
    rw [hswap0] at h0
    rw [h0, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  have hQ : ∏ i, (x i - 1) = (-1 : A) ^ n * ev (eval (1 : Polynomial ℚ) (serreAnFamily n)) := by
    have h1 := congrArg (eval (1 : A)) hfact
    rw [heval1, eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    have hswap1 : (∏ i : Fin n, ((1 : A) - x i)) = (-1 : A) ^ n * ∏ i, (x i - 1) := by
      rw [show ((-1 : A)) ^ n = ∏ _i : Fin n, (-1 : A) by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
          ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by ring)
    rw [hswap1] at h1
    rw [h1, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨n, rfl⟩, one_mul]
  -- sign bookkeeping (as in serreAnFamily_signed_prod_erase_val)
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
  have hsign : (-1 : A) ^ (n * (n - 1) / 2) * (-1) ^ (n * (n - 2)) *
      (-1) ^ n * (-1) ^ (n / 2) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add]; exact hE.neg_one_pow
  -- basic scalar images under ev
  have hcm1 : ev (C (-1 : ℚ)) = (-1 : A) := by simp
  have hcn1 : ev (C ((n : ℚ))) = (n : A) := by
    rw [map_natCast, map_natCast]
  have hev0 : ev (eval (0 : Polynomial ℚ) (serreAnFamily n))
      = ev (C (1 / ((n : ℚ) - 1))) + (-1 : A) ^ (n / 2) * (ev X) ^ 2 := by
    rw [hF0]; simp only [map_add, map_mul, map_pow, hcm1]
  have hev1 : ev (eval (1 : Polynomial ℚ) (serreAnFamily n)) = (-1 : A) ^ (n / 2) * (ev X) ^ 2 := by
    rw [hF1]; simp only [map_mul, map_pow, hcm1]
  have hRHS : ev (serreAnDiscValPoly n)
      = (n : A) ^ n * (ev X) ^ 2
        * (ev (C (1 / ((n : ℚ) - 1))) + (-1 : A) ^ (n / 2) * (ev X) ^ 2) ^ (n - 2) := by
    simp only [serreAnDiscValPoly, map_mul, map_add, map_pow, hcm1, hcn1]
  -- combine so the power base stays an atomic product `(-1)^n * q`
  have hPq : ∏ i, x i
      = (-1 : A) ^ n * (ev (C (1 / ((n : ℚ) - 1))) + (-1 : A) ^ (n / 2) * (ev X) ^ 2) := by
    rw [hP, hev0]
  have hQq : ∏ i, (x i - 1) = (-1 : A) ^ n * ((-1 : A) ^ (n / 2) * (ev X) ^ 2) := by
    rw [hQ, hev1]
  -- final assembly
  rw [discElem_sq_eq_sign_mul_prod_erase x, hK0, hQq, hRHS, hPq, mul_pow]
  linear_combination
    ((n : A) ^ n
        * (ev (C (1 / ((n : ℚ) - 1))) + (-1 : A) ^ (n / 2) * (ev X) ^ 2) ^ (n - 2)
        * (ev X) ^ 2) * hsign

/-- **[Step 2 — descent identity]** For `n ≥ 2`, `Even n`, there is a `G ∈ ℚ[T][Y]` coupled to
`serreAnFamily n` by `IsAltResolvent`.  The `Aₙ`-orbit coefficients descend as `s + δ·t` with
`s, t` symmetric; `s`,`t` descend by Vieta and `δ = √disc` is the rational `serreAnDeltaPoly n`. -/
theorem altResolvent_identity (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ∃ G : Polynomial (Polynomial ℚ), IsAltResolvent n (serreAnFamily n) G := by
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
        * (serreAnFamily n).coeff (n - (i.val + 1)))).toRingHom with hcval
  refine ⟨Shat.map cval + Polynomial.C (serreAnDeltaPoly n) * That.map cval, ?_⟩
  intro A _ ev x hdeg hroots
  letI : Algebra ℚ A := (ev.comp Polynomial.C).toAlgebra
  have halg : algebraMap ℚ A = ev.comp Polynomial.C := rfl
  -- Vieta transport of the two symmetric parts
  have hmapS : (Shat.map cval).map ev = Us.map (MvPolynomial.aeval x).toRingHom := by
    rw [hcval]; exact vieta_map n hn ev x halg hdeg hroots Us Shat hShat
  have hmapT : (That.map cval).map ev = Ut.map (MvPolynomial.aeval x).toRingHom := by
    rw [hcval]; exact vieta_map n hn ev x halg hdeg hroots Ut That hThat
  -- the specialised G
  have hGmapev : (Shat.map cval + Polynomial.C (serreAnDeltaPoly n) * That.map cval).map ev
      = Us.map (MvPolynomial.aeval x).toRingHom
        + Polynomial.C (ev (serreAnDeltaPoly n)) * Ut.map (MvPolynomial.aeval x).toRingHom := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hmapS, hmapT]
  -- the orbit product of an arbitrary enumeration in terms of Us, Ut
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
  -- the square identity fixes δ up to sign
  have hsq : (discElem x) ^ 2 = (ev (serreAnDeltaPoly n)) ^ 2 := by
    rw [serreAnFamily_discSq_general n hn ev x hdeg hroots, ← serreAnDeltaPoly_sq n heven, map_pow]
  have hcases : discElem x = ev (serreAnDeltaPoly n) ∨ discElem x = -(ev (serreAnDeltaPoly n)) := by
    have hfac : (discElem x - ev (serreAnDeltaPoly n)) * (discElem x + ev (serreAnDeltaPoly n)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcases with hpos | hneg
  · refine ⟨x, hroots, ?_⟩
    rw [hGmapev, haltprod x, hpos]
  · set τ : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ with hτ
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    -- reindexing by a permutation fixes the roots multiset
    have hreindex : Finset.univ.val.map (x ∘ τ) = Finset.univ.val.map x := by
      have h1 : Finset.univ.val.map (⇑τ) = Finset.univ.val := by
        have h := congrArg Finset.val (Finset.map_univ_equiv τ)
        rw [Finset.map_val, Equiv.coe_toEmbedding] at h
        exact h
      rw [← Multiset.map_map, h1]
    -- symmetric polynomials are invariant under reindexing the roots
    have hsymm_map : ∀ (W : Polynomial (MvPolynomial (Fin n) ℚ)),
        (∀ k, (W.coeff k).IsSymmetric) →
        W.map (MvPolynomial.aeval (x ∘ τ)).toRingHom = W.map (MvPolynomial.aeval x).toRingHom := by
      intro W hW
      ext k
      simp only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [← MvPolynomial.aeval_rename, (hW k) τ]
    -- the odd transposition flips the sign, matching the other coset
    have hdisc' : discElem (x ∘ τ) = ev (serreAnDeltaPoly n) := by
      rw [discElem_perm x τ, hτ, Equiv.Perm.sign_swap hne]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      rw [hneg]; ring
    refine ⟨x ∘ τ, ?_, ?_⟩
    · rw [hroots, hreindex]
    · rw [hGmapev, haltprod (x ∘ τ), hsymm_map Us hUs_symm, hsymm_map Ut hUt_symm, hdisc']

/-- **[Step 3 — descended resolvent with degree/monicity]** Specialising `altResolvent_identity`
at an injective ring hom into an algebraically closed field where `serreAnFamily n` splits reads
off monicity and the `Y`-degree `n!/2`. Mirrors `ResolventFamily.exists_descended_resolvent`. -/
theorem exists_descended_altResolvent (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ∃ G : Polynomial (Polynomial ℚ), G.Monic ∧ G.natDegree = n.factorial / 2 ∧
      IsAltResolvent n (serreAnFamily n) G := by
  obtain ⟨G, hG⟩ := altResolvent_identity n hn heven
  set K := AlgebraicClosure (FractionRing (Polynomial ℚ))
  set ev₀ : Polynomial ℚ →+* K :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) with hev₀
  have hinj : Function.Injective ev₀ :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  have hmono : (serreAnFamily n).Monic := serreAnFamily_monic n hn
  have hlc : ev₀ ((serreAnFamily n).leadingCoeff) ≠ 0 := by
    rw [hmono.leadingCoeff, map_one]; exact one_ne_zero
  have hdeg₀ : ((serreAnFamily n).map ev₀).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero ev₀ hlc, serreAnFamily_natDegree n hn]
  have hsplit : ((serreAnFamily n).map ev₀).Splits := IsAlgClosed.splits _
  have hcard : ((serreAnFamily n).map ev₀).roots.card = n :=
    (Polynomial.splits_iff_card_roots.mp hsplit).trans hdeg₀
  obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq ((serreAnFamily n).map ev₀).roots n hcard
  obtain ⟨x', -, hGmap⟩ := hG ev₀ x hdeg₀ hx.symm
  refine ⟨G, ?_, ?_, hG⟩
  · have hm : (G.map ev₀).leadingCoeff = 1 := by
      rw [hGmap]; exact altResolventProduct_monic n x'
    rw [Polynomial.leadingCoeff_map_of_injective hinj] at hm
    exact hinj (hm.trans (map_one ev₀).symm)
  · have hd : (G.map ev₀).natDegree = n.factorial / 2 := by
      rw [hGmap]; exact altResolventProduct_natDegree n hn x'
    rwa [Polynomial.natDegree_map_eq_of_injective hinj] at hd

/-- **[Step 4 — root property]** For every integer `t`, the specialised resolvent `G(t)` has a
root inside the splitting field of `serreAnFamily n |_t`.  Mirrors
`ResolventFamily.resolvent_root_property`, using `altResolventProduct_isRoot_genForm_one`. -/
theorem altResolvent_root_property (n : ℕ) (hn : 2 ≤ n) (G : Polynomial (Polynomial ℚ))
    (hG : IsAltResolvent n (serreAnFamily n) G) :
    ∀ t : ℤ, ∃ α : (specialize (serreAnFamily n) t).SplittingField,
      (aeval α) (specialize G t) = 0 := by
  intro t
  set A := (specialize (serreAnFamily n) t).SplittingField
  set ι := algebraMap ℚ A
  set ev := ι.comp (Polynomial.evalRingHom (t : ℚ))
  have hmono : (serreAnFamily n).Monic := serreAnFamily_monic n hn
  obtain ⟨x, hx⟩ : ∃ x : Fin n → A, Finset.univ.val.map x = ((serreAnFamily n).map ev).roots := by
    apply ResolventConstruction.exists_fin_map_eq
    have h_card_roots : ((serreAnFamily n).map ev).roots.card = ((serreAnFamily n).map ev).natDegree := by
      convert Polynomial.splits_iff_card_roots.mp _
      convert Polynomial.SplittingField.splits (specialize (serreAnFamily n) t) using 1
      unfold specialize
      aesop
    rw [h_card_roots, Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;>
      simp_all [serreAnFamily_natDegree n hn]
  obtain ⟨x', -, hGmap⟩ := hG ev x
    (by rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;>
      simp_all [serreAnFamily_natDegree n hn]) hx.symm
  use genForm n x' (1 : Equiv.Perm (Fin n))
  convert congr_arg (Polynomial.eval (genForm n x' 1)) hGmap using 1
  · simp only [aeval_def, specialize, Polynomial.eval_map, Polynomial.eval₂_map]
    rfl
  · exact (altResolventProduct_isRoot_genForm_one n x').symm

end AlternatingFamily

end
