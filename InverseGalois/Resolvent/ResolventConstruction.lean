/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Construction of the k-subset resolvent (symmetric-function descent)

This file provides the algebraic infrastructure behind `resolvent_exists` in
`InverseGalois.Hilbert.Analytic.DorgeBauer`.  Given a monic `F ∈ ℤ[T][X]` of `X`-degree `d` and an integer
tuple `lam : Fin k → ℤ`, we build a *resolvent* polynomial `P ∈ ℤ[T][Y]` whose roots (in any
splitting field of `F`) are the values

`w_S = ∑_{j=1}^k lam_j · e_j(S)`,

where `S` ranges over the `k`-element sub-multisets of the roots of `F` and `e_j(S)` is the
`j`-th elementary symmetric function of `S`.

The construction is via the *universal* resolvent over `MvPolynomial (Fin d) ℤ` and the
fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgHom_surjective`), which
descends the (manifestly symmetric) coefficients of the universal resolvent to genuine
integer polynomials in `T`.  The main outputs are:

* `resolventProduct` — the product `∏_S (Y - w_S)` over a multiset of roots.
* `resolvent_identity` — existence of `P ∈ ℤ[T][Y]` whose image under **any** specialization
  `ev : ℤ[T] →+* A` (into a field in which `F` splits) equals `resolventProduct`.
* `exists_resolvent_poly` — the same `P`, additionally monic of `Y`-degree `d.choose k`.
* `exists_generic_lam` — a *genericity* statement: if `F` is irreducible over the base field
  `K` then for a suitable integer tuple `lam` no `w_S` lies in `K`.
* `two_le_natDegree_choose` — `2 ≤ d.choose k` for `1 ≤ k < d`.
-/

open Polynomial

noncomputable section

namespace ResolventConstruction

/-- The value `w_S = ∑_{j=1}^k lam_j · e_j(S)` attached to a multiset `S` of roots. -/
def wval {A : Type*} [CommRing A] (k : ℕ) (lam : Fin k → ℤ) (s : Multiset A) : A :=
  ∑ j : Fin k, (lam j : A) * s.esymm (↑j + 1)

/-- The `k`-subset resolvent product `∏_{S} (Y - w_S)` over a multiset `r` of roots. -/
def resolventProduct {A : Type*} [CommRing A] (k : ℕ) (lam : Fin k → ℤ)
    (r : Multiset A) : Polynomial A :=
  ((r.powersetCard k).map (fun s ↦ Polynomial.X - Polynomial.C (wval k lam s))).prod

/-
`resolventProduct` is monic (it is a product of monic linear factors).
-/
lemma resolventProduct_monic {A : Type*} [CommRing A] (k : ℕ) (lam : Fin k → ℤ)
    (r : Multiset A) : (resolventProduct k lam r).Monic := by
  apply Polynomial.monic_multiset_prod_of_monic
  exact fun _ _ ↦ Polynomial.monic_X_sub_C _

/-
The `Y`-degree of `resolventProduct` is the number of `k`-subsets of `r`.
-/
lemma resolventProduct_natDegree {A : Type*} [CommRing A] [Nontrivial A] (k : ℕ)
    (lam : Fin k → ℤ) (r : Multiset A) :
    (resolventProduct k lam r).natDegree = (r.powersetCard k).card := by
  convert Polynomial.natDegree_multiset_prod_of_monic _ _
  · simp [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
  · intro f hf
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.monic_X_sub_C _

/-
For `1 ≤ k < d` there are at least two `k`-subsets, so `2 ≤ d.choose k`.
-/
lemma two_le_natDegree_choose {d k : ℕ} (hk : 1 ≤ k) (hk' : k < d) : 2 ≤ d.choose k := by
  induction hk' <;> simp_all
  exact le_trans ‹_› (Nat.choose_le_succ _ _)

/-!
## The universal resolvent and its descent to `ℤ[T]`

`resolvent_identity` is the technical core: the resolvent `P ∈ ℤ[T][Y]` exists as an honest
integer polynomial, and its specialization under any ring hom `ev : ℤ[T] →+* A` (into a field
where `F` splits with the right number of roots) is `resolventProduct k lam (F.map ev).roots`.
This is proved by building the universal resolvent over `MvPolynomial (Fin d) ℤ`, whose
coefficients are symmetric and hence, by `MvPolynomial.esymmAlgHom_surjective`, are integer
polynomials in the elementary symmetric functions; substituting the (signed) coefficients of
`F` for these gives `P`.
-/

/-
Elementary symmetric functions commute with ring homomorphisms.
-/
lemma esymm_map_ringHom {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (s : Multiset A) (n : ℕ) : (s.map φ).esymm n = φ (s.esymm n) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map]
  induction' (Multiset.powersetCard n s) using Multiset.induction_on with a s ih <;> simp_all [map_multiset_prod]

/-
The resolvent value `w_S` commutes with ring homomorphisms.
-/
lemma wval_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (k : ℕ) (lam : Fin k → ℤ)
    (s : Multiset A) : φ (wval k lam s) = wval k lam (s.map φ) := by
  unfold wval
  simp [*]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [esymm_map_ringHom]

/-
The resolvent product commutes with ring homomorphisms (applied coefficientwise).
-/
lemma resolventProduct_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (k : ℕ)
    (lam : Fin k → ℤ) (r : Multiset A) :
    (resolventProduct k lam r).map φ = resolventProduct k lam (r.map φ) := by
  -- Now apply the definition of `resolventProduct` and the fact that `Polynomial.map` commutes with multiplication.
  simp [resolventProduct, Polynomial.map_multiset_prod, Multiset.map_map,
    Multiset.powersetCard_map, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  simp [wval_map]

/-
The coefficients of the universal resolvent (over the variables `X_i`) are symmetric:
applying `rename σ` to the whole product permutes the variables, hence permutes the multiset
`{X_i}` and the family of `k`-subsets, leaving the product unchanged.
-/
lemma resolventProduct_univ_isSymmetric (d k : ℕ) (lam : Fin k → ℤ) (i : ℕ) :
    ((resolventProduct k lam
      (Finset.univ.val.map (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℤ))).coeff i).IsSymmetric := by
  intro σ
  simp [resolventProduct]
  -- By definition of `resolventProduct`, we know that its coefficients are symmetric.
  have h_symm :
      (MvPolynomial.rename σ).toRingHom ((resolventProduct k lam
          (Multiset.map (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℤ) Finset.univ.val)).coeff i) =
        ((resolventProduct k lam
          (Multiset.map (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℤ) Finset.univ.val)).map
            (MvPolynomial.rename σ).toRingHom).coeff i := by
    rw [Polynomial.coeff_map]
  convert h_symm using 1
  · unfold resolventProduct
    aesop
  · rw [resolventProduct_map]
    rw [show (Multiset.map (⇑ (MvPolynomial.rename ⇑σ).toRingHom)
        (Multiset.map MvPolynomial.X Finset.univ.val)) =
        Multiset.map MvPolynomial.X (Finset.univ.val.map σ) from ?_]
    · simp [resolventProduct]
    · simp
      rw [List.ofFn_eq_map, List.ofFn_eq_map]
      have h_perm : List.Perm (List.map (fun x ↦ σ x) (List.finRange d)) (List.finRange d) := by
        grind only [Equiv.Perm.map_finRange_perm]
      convert h_perm.map _ using 1
      simp [Function.comp]

/-
**Descent.**  A polynomial whose coefficients are all symmetric lifts through the
elementary-symmetric substitution `X_i ↦ e_{i+1}` (fundamental theorem of symmetric
polynomials, `MvPolynomial.esymmAlgHom_surjective`).
-/
lemma exists_esymm_lift (d : ℕ) (U : Polynomial (MvPolynomial (Fin d) ℤ))
    (hU : ∀ i, (U.coeff i).IsSymmetric) :
    ∃ Uhat : Polynomial (MvPolynomial (Fin d) ℤ),
      Uhat.map ((MvPolynomial.aeval
        (fun i : Fin d ↦ MvPolynomial.esymm (Fin d) ℤ (↑i + 1))).toRingHom) = U := by
  -- By the fundamental theorem of symmetric polynomials, each coefficient of `U` can be written as a polynomial in the elementary symmetric functions.
  have h_coeff : ∀ i, ∃ p : Polynomial (MvPolynomial (Fin d) ℤ),
      Polynomial.map (MvPolynomial.aeval (fun i : Fin d ↦ MvPolynomial.esymm (Fin d) ℤ (i.val + 1))).toRingHom p =
        Polynomial.C (U.coeff i) := by
    intro i
    have := hU i
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective ℤ (show Fintype.card (Fin d) ≤ d by simp) ⟨U.coeff i, this⟩
    use Polynomial.C p
    convert congr_arg Subtype.val hp using 1
    simp [MvPolynomial.esymmAlgHom_apply]
  choose p hp using h_coeff
  use ∑ i ∈ U.support, Polynomial.monomial i (p i |> Polynomial.coeff <| 0)
  ext i
  simp [Polynomial.coeff_monomial]
  split_ifs with h <;> simp_all [Polynomial.ext_iff]

/-
A multiset of cardinality `n` can be enumerated by a function on `Fin n`.
-/
lemma exists_fin_map_eq {A : Type*} (r : Multiset A) (n : ℕ) (h : r.card = n) :
    ∃ ρ : Fin n → A, Finset.univ.val.map ρ = r := by
  rcases r with ⟨l⟩
  simp_all
  refine ⟨fun i ↦ l.get ⟨i, by linarith [Fin.is_lt i]⟩, ?_⟩
  rw [List.ofFn_eq_map]
  aesop

/-
**Symmetric-function descent (universal resolvent).**  There is an integer polynomial `P`
whose specialization under any field-valued ring hom `ev` for which `F.map ev` splits equals
the resolvent product over the roots of `F.map ev`.
-/
lemma resolvent_identity (F : Polynomial (Polynomial ℤ)) (hF : F.Monic)
    (k : ℕ) (lam : Fin k → ℤ) :
    ∃ P : Polynomial (Polynomial ℤ),
      ∀ {A : Type} [Field A] (ev : Polynomial ℤ →+* A),
        (F.map ev).natDegree = F.natDegree →
        (F.map ev).roots.card = F.natDegree →
        P.map ev = resolventProduct k lam (F.map ev).roots := by
  by_contra! h_contra
  -- Set d := F.natDegree, R := Finset.univ.val.map (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℤ), and U := resolventProduct k lam R (a polynomial over MvPolynomial (Fin d) ℤ).
  set d := F.natDegree with hd
  set R : Multiset (MvPolynomial (Fin d) ℤ) := Finset.univ.val.map (MvPolynomial.X : Fin d → MvPolynomial (Fin d) ℤ)
  set U : Polynomial (MvPolynomial (Fin d) ℤ) := resolventProduct k lam R
  have hU : ∀ i : ℕ, (U.coeff i).IsSymmetric := by
    apply resolventProduct_univ_isSymmetric
  obtain ⟨Uhat, hUhat⟩ := exists_esymm_lift d U hU
  -- Let `eVals : Fin d → ℤ[T]`, `eVals i = (-1)^(↑i+1) * F.coeff (d - (↑i+1))`, and `cval := (MvPolynomial.aeval eVals).toRingHom`.
  set eVals : Fin d → ℤ[X] := fun i ↦ (-1 : ℤ[X]) ^ (i.val + 1) * (F.coeff (d - (i.val + 1)))
  set cval : MvPolynomial (Fin d) ℤ →+* ℤ[X] := (MvPolynomial.aeval eVals).toRingHom
  set P : Polynomial ℤ[X] := Uhat.map cval
  have hP : ∀ {A : Type} [Field A] (ev : ℤ[X] →+* A), (F.map ev).natDegree = d →
      (F.map ev).roots.card = d → (P.map ev) = resolventProduct k lam (F.map ev).roots := by
    intros A _ ev hdeg hcard
    set p : Polynomial A := F.map ev
    set r : Multiset A := p.roots
    obtain ⟨ρ, hρ⟩ := exists_fin_map_eq r d hcard
    set aρ : MvPolynomial (Fin d) ℤ →+* A := (MvPolynomial.aeval ρ).toRingHom
    have h_ring_hom : ev.comp cval =
        aρ.comp ((MvPolynomial.aeval (fun i : Fin d ↦ MvPolynomial.esymm (Fin d) ℤ (i.val + 1))).toRingHom) := by
      ext i
      · simp [cval, aρ]
      · have h_vieta : p.coeff (d - (i.val + 1)) = 1 * (-1 : A) ^ (i.val + 1) * r.esymm (i.val + 1) := by
          have h_vieta_i : p = Polynomial.C (p.leadingCoeff) *
              Multiset.prod (Multiset.map (fun x ↦ Polynomial.X - Polynomial.C x) r) := by
            convert Polynomial.Splits.eq_prod_roots _
            rw [Polynomial.splits_iff_card_roots]
            grind
          conv_lhs => rw [h_vieta_i]
          rw [Polynomial.coeff_C_mul, Multiset.prod_X_sub_C_coeff]
          · rw [hcard]
            rw [Nat.sub_sub_self (by linarith [Fin.is_lt i])]
            ring_nf
            rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero] <;> norm_num [hF]
          · exact hcard.symm ▸ Nat.sub_le _ _
        simp +zetaDelta at *
        rw [h_vieta, mul_left_comm]
        rw [← hρ]
        norm_num [MvPolynomial.aeval_esymm_eq_multiset_esymm]
        ring_nf
        norm_num [pow_mul']
    convert congr_arg (Polynomial.map aρ) hUhat using 1
    · rw [Polynomial.map_map]
      rw [h_ring_hom, Polynomial.map_map]
    · rw [← hρ, resolventProduct_map]
      simp +zetaDelta at *
      congr! 2
      exact List.ext_get (by simp) (by simp [Function.comp])
  exact absurd (h_contra P) (by
    push_neg
    tauto)

/-
**Resolvent existence.**  The resolvent `P` of `resolvent_identity`, additionally monic of
`Y`-degree `d.choose k`.
-/
lemma exists_resolvent_poly (F : Polynomial (Polynomial ℤ)) (hF : F.Monic)
    (k : ℕ) (lam : Fin k → ℤ) :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.natDegree = F.natDegree.choose k ∧
      ∀ {A : Type} [Field A] (ev : Polynomial ℤ →+* A),
        (F.map ev).natDegree = F.natDegree →
        (F.map ev).roots.card = F.natDegree →
        P.map ev = resolventProduct k lam (F.map ev).roots := by
  -- By `resolvent_identity`, there exists a polynomial `P` satisfying the given conditions.
  obtain ⟨P, hP⟩ := resolvent_identity F hF k lam
  refine ⟨P, ?_, ?_, hP⟩
  · -- Let `A` be an algebraically closed field of characteristic `0`, such as `ℂ`.
    set A := FractionRing (Polynomial ℤ)
    obtain ⟨ev,hev⟩ : ∃ ev : Polynomial ℤ →+* AlgebraicClosure A, Function.Injective ev := by
      exact ⟨(algebraMap A (AlgebraicClosure A)).comp (algebraMap (Polynomial ℤ) A),
        (algebraMap A (AlgebraicClosure A)).injective.comp (IsFractionRing.injective _ _)⟩
    have hP_monic : (P.map ev).Monic := by
      have hP_monic : (resolventProduct k lam (map ev F).roots).Monic :=
        resolventProduct_monic k lam (map ev F).roots
      have hP_monic : (map ev F).Splits := IsAlgClosed.splits _
      rw [Polynomial.splits_iff_card_roots] at hP_monic
      aesop
    rw [Polynomial.Monic, Polynomial.leadingCoeff_map_of_injective hev] at hP_monic
    aesop
  · obtain ⟨A, hA⟩ : ∃ A : Type, ∃ (inst : Field A), ∃ (ev : Polynomial ℤ →+* A),
        Function.Injective ev ∧ (F.map ev).natDegree = F.natDegree ∧
          (F.map ev).roots.card = F.natDegree := by
      obtain ⟨A, hA⟩ : ∃ A : Type, ∃ (inst : Field A), ∃ (ev : Polynomial ℤ →+* A),
          Function.Injective ev ∧ (F.map ev).Splits := by
        use AlgebraicClosure (FractionRing (Polynomial ℤ))
        refine ⟨inferInstance,
          (algebraMap (Polynomial ℤ) (FractionRing (Polynomial ℤ))).comp
            (algebraMap (Polynomial ℤ) (Polynomial ℤ)) |> RingHom.comp
            (algebraMap (FractionRing (Polynomial ℤ)) (AlgebraicClosure (FractionRing (Polynomial ℤ)))),
          ?_, ?_⟩
        · exact fun x y hxy ↦ by simpa using hxy
        · exact IsAlgClosed.splits _
      obtain ⟨inst, ev, hev₁, hev₂⟩ := hA
      use A, inst, ev
      simp_all [Polynomial.splits_iff_card_roots]
    obtain ⟨inst, ev, hev, hF₁, hF₂⟩ := hA
    specialize hP ev hF₁ hF₂
    replace hP := congr_arg Polynomial.natDegree hP
    simp_all
    rw [← hF₂, resolventProduct_natDegree] at *
    rw [← Polynomial.natDegree_map_eq_of_injective hev]
    aesop

/-!
## Genericity: choosing `lam` so that no `w_S` is rational

If `f` is irreducible over `K` (so it has no factor of degree `k` with `0 < k < d`), then for
each `k`-subset `S` of the roots (in a splitting field `L`) not all elementary symmetric
functions `e_j(S)` lie in `K`.  Over the infinite field `ℚ` the tuples `lam` for which
`w_S ∈ K` form a proper subspace, so a generic integer `lam` avoids all of them.
-/

/-
If a `k`-subset `S` of the roots of an irreducible `f` had all elementary symmetric
functions in the base field `K`, then `∏_{β ∈ S}(X - β)` would descend to a degree-`k` factor
of `f` over `K`, contradicting irreducibility.  Hence some `e_j(S) ∉ K`.
-/
lemma exists_esymm_notMem {K L : Type} [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hsplit : (f.map (algebraMap K L)).roots.card = f.natDegree)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree)
    (s : Multiset L) (hs : s ∈ (f.map (algebraMap K L)).roots.powersetCard k) :
    ∃ j : Fin k, s.esymm (↑j + 1) ∉ Set.range (algebraMap K L) := by
  by_contra! h_contra
  obtain ⟨gK, hgK⟩ : ∃ gK : Polynomial K, gK.Monic ∧
      gK.map (algebraMap K L) = Multiset.prod (s.map (fun β ↦ Polynomial.X - Polynomial.C β)) ∧
        gK.natDegree = k := by
    have h_lift : ∃ gK : Polynomial K,
        gK.map (algebraMap K L) = Multiset.prod (s.map (fun β ↦ Polynomial.X - Polynomial.C β)) ∧
          gK.natDegree = k := by
      have h_lift : ∃ gK : Polynomial K,
          gK.map (algebraMap K L) = Multiset.prod (s.map (fun β ↦ Polynomial.X - Polynomial.C β)) := by
        have h_lift : ∀ j : ℕ, j ≤ k →
            (Multiset.prod (s.map (fun β ↦ Polynomial.X - Polynomial.C β))).coeff j ∈ Set.range (algebraMap K L) := by
          intro j hj
          by_cases hj' : j = k <;> simp_all [Multiset.prod_X_sub_C_coeff]
          · exact ⟨1, by simp [Multiset.esymm]⟩
          · obtain ⟨y, hy⟩ := h_contra ⟨k - j - 1, by omega⟩
            use (-1) ^ (k - j) * y
            simp_all [Nat.sub_sub, add_comm]
            rw [show 1 + (k - (j + 1)) = k - j by omega]
        choose! g hg using h_lift
        use ∑ j ∈ Finset.range (k + 1), g j • Polynomial.X ^ j
        ext j
        simp [Polynomial.coeff_X_pow]
        split_ifs <;> simp_all [Polynomial.coeff_eq_zero_of_natDegree_lt]
      obtain ⟨gK, hgK⟩ := h_lift
      use gK
      have := congr_arg Polynomial.natDegree hgK
      rw [Polynomial.natDegree_map, Polynomial.natDegree_multiset_prod] at this <;> simp_all
      exact fun x hx ↦ Polynomial.X_sub_C_ne_zero x
    obtain ⟨gK, hgK₁, hgK₂⟩ := h_lift
    use gK
    simp_all [Polynomial.Monic.def]
    replace hgK₁ := congr_arg Polynomial.leadingCoeff hgK₁
    simp_all [Polynomial.leadingCoeff_multiset_prod]
  have h_div : gK ∣ f := by
    have h_div : Multiset.prod (s.map (fun β ↦ Polynomial.X - Polynomial.C β)) ∣
        Polynomial.map (algebraMap K L) f := by
      have h_div :
          Multiset.map (fun β ↦ Polynomial.X - Polynomial.C β) s ≤
            Multiset.map (fun β ↦ Polynomial.X - Polynomial.C β)
              (Polynomial.roots (Polynomial.map (algebraMap K L) f)) := by
        exact Multiset.map_le_map <| Multiset.mem_powersetCard.mp hs |>.1
      apply dvd_trans (Multiset.prod_dvd_prod_of_le h_div)
      exact Polynomial.prod_multiset_X_sub_C_dvd (Polynomial.map (algebraMap K L) f)
    rw [← Polynomial.map_dvd_map' (algebraMap K L)]
    aesop
  obtain ⟨q, rfl⟩ := h_div
  simp_all [irreducible_mul_iff]
  cases hf_irr <;> simp_all [Polynomial.natDegree_mul', Polynomial.Monic.def]
  · rw [Polynomial.isUnit_iff] at *
    aesop
  · exact absurd (Polynomial.natDegree_eq_zero_of_isUnit (by tauto)) (by linarith)

/-
**Genericity of the linear form.**  For `f` irreducible monic over `K` splitting in `L`
(char 0) with `1 ≤ k < deg f`, there is an integer tuple `lam` such that for every `k`-subset
`S` of the roots the value `w_S = ∑ lam_j e_j(S)` does not lie in `K`.
-/
lemma exists_generic_lam {K L : Type} [Field K] [Field L] [Algebra K L] [CharZero L]
    (f : Polynomial K) (hf_irr : Irreducible f) (hf_monic : f.Monic)
    (hsplit : (f.map (algebraMap K L)).roots.card = f.natDegree)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k < f.natDegree) :
    ∃ lam : Fin k → ℤ, ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k,
      wval k lam s ∉ Set.range (algebraMap K L) := by
  -- Work over the infinite field ℚ with module `M := Fin k → ℚ`.
  set M := Fin k → ℚ
  -- For each s, define the ℚ-linear map `Φ_s : M →ₗ[ℚ] L`, `Φ_s μ = ∑ j : Fin k, algebraMap ℚ L (μ j) * s.esymm (↑j+1)`, and the submodule `p i := Submodule.comap Φ_s R'` where `R'` is `Set.range (algebraMap K L)` regarded as a ℚ-submodule of L.
  have h_linear_maps : ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k, ∃ Φ_s : M →ₗ[ℚ] L,
      ∀ μ : M, Φ_s μ = ∑ j : Fin k, algebraMap ℚ L (μ j) * s.esymm (↑j + 1) := by
    intro s hs
    refine ⟨{ toFun := fun μ ↦ ∑ j : Fin k, algebraMap ℚ L (μ j) * s.esymm (j.val + 1)
              map_add' := ?_, map_smul' := ?_ }, ?_⟩
    all_goals norm_num [Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Algebra.smul_def]
    · simp +zetaDelta at *
      exact fun x y ↦ by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · simp +zetaDelta at *
      exact fun m x ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  choose! Φ hΦ using h_linear_maps
  -- By `Submodule.exists_forall_notMem_of_forall_ne_top` get `μ : M = Fin k → ℚ` with `Φ_s μ ∉ R'` for every s (in the toFinset, equivalently every s in the powersetCard multiset).
  obtain ⟨μ, hμ⟩ : ∃ μ : M, ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k,
      Φ s μ ∉ Set.range (algebraMap K L) := by
    have h_submodule : ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k,
        ∃ p : Submodule ℚ M, p ≠ ⊤ ∧ ∀ μ : M, μ ∈ p ↔ Φ s μ ∈ Set.range (algebraMap K L) := by
      intro s hs
      obtain ⟨p, hp⟩ : ∃ p : Submodule ℚ M, ∀ μ : M, μ ∈ p ↔ Φ s μ ∈ Set.range (algebraMap K L) := by
        have h_submodule : ∃ p : Submodule ℚ L, ∀ x : L, x ∈ p ↔ x ∈ Set.range (algebraMap K L) := by
          refine ⟨Submodule.span ℚ (Set.range (algebraMap K L)), ?_⟩
          intro x
          exact ⟨fun hx ↦ by
            rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx
            obtain ⟨c, rfl⟩ := hx
            simp [Finsupp.sum]
            use ∑ x ∈ c.support, c x • x
            simp [Algebra.smul_def]
            simp [Rat.smul_def], fun hx ↦ by
            exact Submodule.subset_span hx⟩
        exact ⟨Submodule.comap (Φ s) h_submodule.choose, fun μ ↦ by simpa using h_submodule.choose_spec (Φ s μ)⟩
      have := exists_esymm_notMem f hf_irr hf_monic hsplit k hk hk' s hs
      simp_all [Submodule.eq_top_iff']
      refine ⟨p, ?_, hp⟩
      obtain ⟨j, hj⟩ := this
      use fun i ↦ if i = j then 1 else 0
      simp_all
      simp_all [Finset.sum_eq_single j]
    choose! p hp₁ hp₂ using h_submodule
    have h_submodule : ∃ μ : M, ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k, μ ∉ p s := by
      have h_submodule : ∀ (S : Finset (Multiset L)), (∀ s ∈ S, p s ≠ ⊤) → ∃ μ : M, ∀ s ∈ S, μ ∉ p s := by
        intros S hS
        convert Submodule.exists_forall_notMem_of_forall_ne_top (fun s : S => p s) (fun s => hS s s.2) using 1
        simp
      convert h_submodule (Multiset.toFinset (Multiset.powersetCard k (map (algebraMap K L) f |> Polynomial.roots))) _
      · grind +splitImp
      · exact Classical.decEq _
      · grind
    exact ⟨h_submodule.choose, fun s hs ↦ fun h ↦ h_submodule.choose_spec s hs <| hp₂ s hs _ |>.2 h⟩
  -- Clear denominators: pick `n : ℤ`, `n ≠ 0`, and `lam : Fin k → ℤ` with `(lam j : ℚ) = n * μ j` for all j (product of denominators).
  obtain ⟨n, hn_ne_zero, lam, hlam⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∃ lam : Fin k → ℤ, ∀ j : Fin k, (lam j : ℚ) = n * μ j := by
    -- Let `n` be the product of the denominators of the entries of `μ`.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n ≠ 0 ∧ ∀ j : Fin k, (μ j).den ∣ n := by
      exact ⟨∏ j, (μ j |> Rat.den),
        Finset.prod_ne_zero_iff.mpr fun j _ ↦ Nat.cast_ne_zero.mpr <| Rat.den_nz _,
        fun j ↦ Finset.dvd_prod_of_mem _ <| Finset.mem_univ _⟩
    refine ⟨n, mod_cast hn.1, fun j ↦ (n * μ j |> Rat.num), fun j ↦ ?_⟩
    simp
    obtain ⟨m, hm⟩ := hn.2 j
    simp [hm, mul_assoc, mul_left_comm, Rat.mul_num]
  -- Then for each s, `wval k lam s = ∑ j (lam j : L) * s.esymm (↑j+1) = ∑ j algebraMap ℚ L (lam j : ℚ) * s.esymm (↑j+1) = (n : L) * Φ_s μ`, using `(lam j : L) = algebraMap ℚ L (lam j : ℚ) = (n:L) * algebraMap ℚ L (μ j)`.
  have h_wval : ∀ s ∈ (f.map (algebraMap K L)).roots.powersetCard k, wval k lam s = (n : L) * Φ s μ := by
    intro s hs
    simp [hΦ s hs, wval, Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun _ _ ↦ by
      rw [show (lam _ : L) = n * μ _ from mod_cast hlam _]
      ring
  refine ⟨lam, fun s hs ↦ ?_⟩
  contrapose! hμ
  obtain ⟨x, hx⟩ := hμ
  refine ⟨s, hs, ⟨x / n, ?_⟩⟩
  simp_all [mul_comm, div_eq_mul_inv]

/-!
## Roots of the resolvent product
-/

/-
Each value `w_S` for a `k`-subset `S` of `r` is a root of `resolventProduct`.
-/
lemma isRoot_resolventProduct_of_mem {A : Type*} [CommRing A] (k : ℕ) (lam : Fin k → ℤ)
    (r : Multiset A) {s : Multiset A} (hs : s ∈ r.powersetCard k) :
    (resolventProduct k lam r).IsRoot (wval k lam s) := by
  unfold resolventProduct
  simp [Polynomial.eval_multiset_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨s, hs, sub_self _⟩)

/-
Any root of `resolventProduct` (over a domain) equals some `w_S`.
-/
lemma exists_mem_of_isRoot_resolventProduct {A : Type*} [CommRing A] [IsDomain A] (k : ℕ)
    (lam : Fin k → ℤ) (r : Multiset A) {a : A}
    (ha : (resolventProduct k lam r).IsRoot a) :
    ∃ s ∈ r.powersetCard k, wval k lam s = a := by
  simp_all [resolventProduct, Polynomial.eval_multiset_prod]
  exact ⟨ha.choose, ha.choose_spec.1, sub_eq_zero.mp ha.choose_spec.2 |> Eq.symm⟩

/-!
## Vieta: the resolvent values of an integer polynomial are integers
-/

/-
The elementary symmetric functions of the roots of `g.map φ` lie in the range of `φ`
(they are, up to sign, coefficients of `g.map φ`, i.e. images of coefficients of `g`).
-/
lemma esymm_roots_map_mem_range {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (g : Polynomial R) (hg : g.Monic)
    (hcard : (g.map φ).roots.card = g.natDegree) (m : ℕ) :
    (g.map φ).roots.esymm m ∈ Set.range φ := by
  by_cases hm : m ≤ g.natDegree
  · have h_coeff : Polynomial.coeff (Polynomial.map φ g) (Polynomial.natDegree g - m) =
        (-1 : A) ^ m * (Polynomial.roots (Polynomial.map φ g)).esymm m := by
      convert Polynomial.coeff_eq_esymm_roots_of_card
        (show Multiset.card (Polynomial.roots (Polynomial.map φ g)) =
          Polynomial.natDegree (Polynomial.map φ g) from ?_) ?_ using 1
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> simp_all [Polynomial.Monic.def]
        rw [Nat.sub_sub_self hm, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero] <;> aesop
      · rw [hcard, Polynomial.natDegree_map_of_leadingCoeff_ne_zero]
        aesop
      · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> aesop
    use (-1 : R) ^ m * g.coeff (Polynomial.natDegree g - m)
    by_cases h : Even m <;> simp_all
  · simp [Multiset.esymm, show m > (g.map φ |> Polynomial.roots |> Multiset.card) from hcard.symm ▸ not_le.mp hm]
    exact ⟨0, map_zero φ⟩

/-
The resolvent value `w_S` for `S =` the roots of `g.map φ` lies in the range of `φ`.
-/
lemma wval_roots_map_mem_range {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (φ : R →+* A) (g : Polynomial R) (hg : g.Monic)
    (hcard : (g.map φ).roots.card = g.natDegree) (k : ℕ) (lam : Fin k → ℤ) :
    wval k lam (g.map φ).roots ∈ Set.range φ := by
  convert SetLike.mem_coe.mpr
    (Subring.sum_mem φ.range fun j (hj : j ∈ (Finset.univ : Finset (Fin k))) ↦
      Subring.mul_mem φ.range ?_ ?_)
  · exact ⟨lam j, by simp⟩
  · exact esymm_roots_map_mem_range φ g hg hcard (j + 1)

end ResolventConstruction
