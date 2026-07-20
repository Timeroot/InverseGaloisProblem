/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.HilbertIrreducibility
import InverseGalois.Resolvent.ResolventConstruction
import InverseGalois.Hilbert.Analytic.NewtonPuiseux
import InverseGalois.Hilbert.Analytic.MorseSwap

/-!
# The generic resolvent family (backwards decomposition of `exists_resolvent_family`)

This file develops the *large-scale strokes* of the proof of
`IsInverseGalois.exists_resolvent_family` (in `InverseGalois.Hilbert.SymmetricViaHIT`) as a small
number of named lemmas.  The main theorem `exists_resolvent_family` is then assembled from:

* `exists_resolvent_family_core` — everything **except** the "infinitely many irreducible
  specialisations" conjunct, and
* `hilbert_irreducibility_theorem` — which supplies that final conjunct from irreducibility
  and absolute irreducibility of the resolvent `G`.

## The concrete family

We use the classical **Morse family** `F = Xⁿ − X − T` (`genPoly n`), an element of
`ℚ[T][X]` (i.e. `Polynomial (Polynomial ℚ)`), where the outer variable is `X` and `T` is the
coefficient variable.  For `n ≥ 2` the underlying polynomial `g(X) = Xⁿ − X` is a *Morse*
polynomial (its critical points, the roots of `g′ = nXⁿ⁻¹ − 1`, have pairwise distinct
critical values), so the family `g(X) = T` has geometric monodromy group `Sₙ` over `ℂ(T)`,
hence arithmetic Galois group `Sₙ` over `ℚ(T)` as well.

## The resolvent

For a tuple of roots `x : Fin n → A` we form the **generic linear resolvent** using the
linear forms `w_σ = ∑ᵢ i · x_(σ i)` indexed by `σ ∈ Sₙ`.  The product
`∏_σ (Y − w_σ)` (`fullResolventProduct`) has degree `n!` and is a symmetric function of the
`x`, so it descends to a polynomial `G ∈ ℚ[T][Y]` (`IsFullResolvent`).  Because the
coefficients `i` are pairwise distinct, the `n!` forms are pairwise distinct whenever the
roots are, so:

* `G` is irreducible over `ℚ(T)` iff the arithmetic Galois group is `Sₙ`
  (`fullResolvent_irreducible`), and
* `G` is absolutely irreducible iff the geometric Galois group is `Sₙ`
  (`fullResolvent_abs_irreducible`).

## The decomposition lemmas

* `genPoly_monic`, `genPoly_natDegree` — bookkeeping for `F = Xⁿ − X − T` (`n ≥ 2`).
* `genPoly_separable_cofinite` — `F(t, X)` is separable for all but finitely many `t`.
* `exists_fullResolvent` — existence of the descended resolvent `G` (monic, degree `n!`,
  satisfying the descent identity `IsFullResolvent`, with the per-`t` resolvent-root
  property).  This is the *symmetric-function descent*, the structural (non-monodromy) core.
* `fullResolvent_irreducible`, `fullResolvent_abs_irreducible` — the two deep
  (arithmetic / geometric) `Sₙ` inputs.
* `resolvent_family_core_one` — the trivial `n = 1` base case.
* `exists_resolvent_family_core` — the assembled core (all conjuncts but the last).
-/

open Polynomial

noncomputable section

namespace ResolventFamily

/-- The Morse family `F = Xⁿ − X − T` as an element of `ℚ[T][X]`. -/
def genPoly (n : ℕ) : Polynomial (Polynomial ℚ) := X ^ n - X - C X

/-- The linear form `w_σ = ∑ᵢ i · x_(σ i)` attached to a permutation `σ` of the roots. -/
def genForm {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) (σ : Equiv.Perm (Fin n)) : A :=
  ∑ i : Fin n, ((i : ℕ) : A) * x (σ i)

/-- The generic linear resolvent product `∏_σ (Y − w_σ)` over all `σ ∈ Sₙ`. -/
def fullResolventProduct {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) : Polynomial A :=
  ∏ σ : Equiv.Perm (Fin n), (Polynomial.X - Polynomial.C (genForm n x σ))

/-- `G ∈ ℚ[T][Y]` is the (descended) generic linear resolvent of `F ∈ ℚ[T][X]`: for every
field `A` and specialisation `ev : ℚ[T] →+* A` in which `F` splits with roots enumerated by
`x : Fin n → A`, the specialised `G` equals the resolvent product of those roots. -/
def IsFullResolvent (n : ℕ) (F G : Polynomial (Polynomial ℚ)) : Prop :=
  ∀ {A : Type} [Field A] (ev : Polynomial ℚ →+* A) (x : Fin n → A),
    (F.map ev).natDegree = n →
    (F.map ev).roots = Finset.univ.val.map x →
    G.map ev = fullResolventProduct n x

/-- `genForm` commutes with ring homomorphisms. -/
theorem genForm_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (n : ℕ)
    (x : Fin n → A) (σ : Equiv.Perm (Fin n)) :
    φ (genForm n x σ) = genForm n (fun i => φ (x i)) σ := by
  unfold genForm
  simp [map_sum, map_mul]

/-- The resolvent product commutes with ring homomorphisms. -/
theorem fullResolventProduct_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (n : ℕ) (x : Fin n → A) :
    (fullResolventProduct n x).map φ = fullResolventProduct n (fun i => φ (x i)) := by
  unfold fullResolventProduct
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, genForm_map]

/-- The resolvent product is monic (a product of monic linear factors). -/
theorem fullResolventProduct_monic {A : Type*} [CommRing A] (n : ℕ) (x : Fin n → A) :
    (fullResolventProduct n x).Monic := by
  unfold fullResolventProduct
  exact monic_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)

/-- The resolvent product has degree `n!` (it is a product of `n!` monic linear factors). -/
theorem fullResolventProduct_natDegree {A : Type*} [CommRing A] [Nontrivial A] (n : ℕ)
    (x : Fin n → A) :
    (fullResolventProduct n x).natDegree = n.factorial := by
  unfold fullResolventProduct
  rw [natDegree_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)]
  simp [Fintype.card_perm, Fintype.card_fin]

/-- The Morse family `Xⁿ − X − T` is monic (for `n ≥ 2`, so the leading `Xⁿ` term dominates
the `−X` and `−T` terms). -/
theorem genPoly_monic (n : ℕ) (hn : 2 ≤ n) : (genPoly n).Monic := by
  have h : genPoly n = X ^ n - (X + C X) := by
    unfold genPoly
    ring
  rw [h]
  apply monic_X_pow_sub
  have hle : (X + C X : Polynomial (Polynomial ℚ)).degree ≤ 1 := by
    refine le_trans (degree_add_le _ _) ?_
    rw [degree_X]
    exact max_le le_rfl (le_trans (degree_C_le) (by norm_num))
  refine lt_of_le_of_lt hle ?_
  exact_mod_cast (by omega : (1:ℕ) < n)

/-- The Morse family `Xⁿ − X − T` has `X`-degree `n` (for `n ≥ 2`). -/
theorem genPoly_natDegree (n : ℕ) (hn : 2 ≤ n) : (genPoly n).natDegree = n := by
  unfold genPoly
  have h1 : ((X : Polynomial (Polynomial ℚ))^n - X).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp
      omega
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simpa using h1
  · rw [h1]
    have : (C (X : Polynomial ℚ)).natDegree = 0 := natDegree_C _
    omega

/-
**Separability of the specialisations.** `F(t, X) = Xⁿ − X − t` is separable for all but
finitely many `t ∈ ℤ` (the exceptions are the finitely many roots of the discriminant, a
nonzero polynomial in `t`).
-/
theorem genPoly_separable_cofinite (n : ℕ) (hn : 2 ≤ n) :
    {t : ℤ | ¬ (specialize (genPoly n) t).Separable}.Finite := by
  -- By definition of $D$, we know that its roots are finite.
  have hD_roots_finite : Set.Finite (SetLike.coe (Polynomial.roots
      (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1) - 1 : Polynomial ℚ)).toFinset) := by
    exact Set.toFinite _
  have hD_roots_finite : Set.Finite {t : ℚ | ∃ r : AlgebraicClosure ℚ,
      Polynomial.eval r (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (Polynomial.C (n : ℚ) * Polynomial.X ^ (n - 1) - 1)) = 0 ∧
      Polynomial.eval r (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (Polynomial.X ^ n - Polynomial.X - Polynomial.C (t : ℚ))) = 0} := by
    refine' Set.Finite.subset (hD_roots_finite.image (fun r : ℚ => r ^ n - r)
      |> Set.Finite.image (fun t : ℚ => t)) _
    intro t ht
    obtain ⟨r, hr₁, hr₂⟩ := ht
    simp_all [sub_eq_iff_eq_add]
    have h_rational : ∃ q : ℚ, r = algebraMap ℚ (AlgebraicClosure ℚ) q := by
      have h_rational : r ^ (n - 1) = 1 / (n : ℚ) := by
        exact eq_one_div_of_mul_eq_one_right <| by simpa [mul_comm] using hr₁
      have h_rational : r ^ n = r * (1 / (n : ℚ)) := by
        rw [← h_rational, ← pow_succ', Nat.sub_add_cancel (by linarith)]
      simp_all
      refine ⟨t / ((n : ℚ) ⁻¹ - 1), ?_⟩
      push_cast
      rw [eq_div_iff (sub_ne_zero_of_ne <| by aesop)]
      linear_combination' hr₂
    obtain ⟨q, rfl⟩ := h_rational
    use q
    simp_all
    norm_cast at *
    exact ⟨⟨ne_of_apply_ne Polynomial.natDegree <| by erw [Polynomial.natDegree_C_mul_X_pow] <;> aesop, hr₁⟩, hr₂⟩
  refine' Set.Finite.subset (hD_roots_finite.preimage _) _
  use fun t => t
  · exact fun x hx y hy hxy => by simpa using hxy
  · intro t ht
    contrapose! ht
    simp_all [Polynomial.Separable]
    -- By definition of $D$, we know that its roots are finite, so we can apply the fact that a polynomial is separable if and only if it has no repeated roots.
    have h_separable : ∀ x : AlgebraicClosure ℚ,
        Polynomial.eval x (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
          (specialize (genPoly n) t)) = 0 →
        Polynomial.eval x (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
          (derivative (specialize (genPoly n) t))) ≠ 0 := by
      intro x hx
      specialize ht x
      simp_all [specialize, genPoly]
      cases n <;> simp_all [Polynomial.derivative_pow]
    apply isCoprime_of_irreducible_dvd
    · unfold specialize
      simp [genPoly]
      intro h
      replace h := congr_arg (fun p => Polynomial.coeff p n) h
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

/-
**Symmetry of the universal resolvent's coefficients.** Over `MvPolynomial (Fin n) ℚ` with
generic roots `Xᵢ`, every coefficient of `fullResolventProduct n (fun i => X i)` is a symmetric
polynomial: renaming the variables by `σ` reindexes the `n!` factors bijectively, leaving the
product unchanged.
-/
theorem fullResolventProduct_isSymmetric (n : ℕ) (k : ℕ) :
    (fullResolventProduct n (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℚ))).coeff k
      |>.IsSymmetric := by
  intro e
  convert congr_arg (fun p : Polynomial (MvPolynomial (Fin n) ℚ) => Polynomial.coeff p k)
    (show (fullResolventProduct n fun i => MvPolynomial.X i |> MvPolynomial.rename e)
      = fullResolventProduct n fun i => MvPolynomial.X i from ?_) using 1
  · convert congr_arg (fun p : Polynomial (MvPolynomial (Fin n) ℚ) => Polynomial.coeff p k)
      (fullResolventProduct_map (MvPolynomial.rename e |> AlgHom.toRingHom) n fun i => MvPolynomial.X i)
      using 1
    simp [Polynomial.coeff_map]
  · apply Finset.prod_bij (fun σ _ => e * σ)
    · exact fun _ _ => Finset.mem_univ _
    · aesop
    · exact fun b _ => ⟨e⁻¹ * b, Finset.mem_univ _, by simp⟩
    · unfold genForm
      aesop

/-- The ℚ-analogue of `ResolventConstruction.exists_esymm_lift`: a polynomial whose
coefficients are symmetric functions lifts along the elementary-symmetric substitution
`X_i ↦ e_{i+1}` (fundamental theorem of symmetric polynomials). -/
theorem exists_esymm_lift_rat (d : ℕ) (U : Polynomial (MvPolynomial (Fin d) ℚ))
    (hU : ∀ i, (U.coeff i).IsSymmetric) :
    ∃ Uhat : Polynomial (MvPolynomial (Fin d) ℚ),
      Uhat.map ((MvPolynomial.aeval
        (fun i : Fin d => MvPolynomial.esymm (Fin d) ℚ (↑i + 1))).toRingHom) = U := by
  have h_coeff : ∀ i, ∃ p : Polynomial (MvPolynomial (Fin d) ℚ),
      Polynomial.map (MvPolynomial.aeval (fun i => MvPolynomial.esymm (Fin d) ℚ (i.val + 1))).toRingHom p
        = Polynomial.C (U.coeff i) := by
    intro i
    have := hU i
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective ℚ
      (show Fintype.card (Fin d) ≤ d by simp) ⟨U.coeff i, this⟩
    use Polynomial.C p
    convert congr_arg Subtype.val hp using 1
    simp [MvPolynomial.esymmAlgHom_apply]
  choose p hp using h_coeff
  use ∑ i ∈ U.support, Polynomial.monomial i (p i |> Polynomial.coeff <| 0)
  ext i
  simp [Polynomial.coeff_monomial]
  split_ifs with h <;> simp_all [Polynomial.ext_iff]

/-
**The descent identity (existence of the descended resolvent as a bare `IsFullResolvent`).**
The hard structural core: for any monic `F` of `X`-degree `n` there is a `G ∈ ℚ[T][Y]`
satisfying the descent identity `IsFullResolvent n F G`.  Monicity and the degree `n!` are
then read off (`exists_descended_resolvent`) by specialising at an injective ring hom into an
algebraically closed field where `F` splits.

Proof (to formalise): let `U := fullResolventProduct n (fun i => MvPolynomial.X i)` over
`MvPolynomial (Fin n) ℚ`; its coefficients are symmetric (`fullResolventProduct_isSymmetric`),
so by `MvPolynomial.esymmAlgHom_surjective` they lift along `X_i ↦ e_{i+1}`; substituting
Vieta's `e_{i+1} ↦ (-1)^{i+1} F.coeff (n-(i+1))` produces `G`.  The descent identity then
follows from `fullResolventProduct_map` and Vieta as in
`ResolventConstruction.resolvent_identity`.
-/
theorem fullResolvent_identity (F : Polynomial (Polynomial ℚ)) (hF : F.Monic)
    (n : ℕ) (hFdeg : F.natDegree = n) :
    ∃ G : Polynomial (Polynomial ℚ), IsFullResolvent n F G := by
  obtain ⟨Uhat, hU⟩ : ∃ Uhat : Polynomial (MvPolynomial (Fin n) ℚ),
      Uhat.map ((MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℚ (i.val + 1))).toRingHom)
        = fullResolventProduct n (fun i => MvPolynomial.X i : Fin n → MvPolynomial (Fin n) ℚ) := by
    exact exists_esymm_lift_rat n _ (fun i => fullResolventProduct_isSymmetric n i)
  -- Set `cval := (MvPolynomial.aeval (fun i : Fin n => (-1)^(i.val+1) * F.coeff (n-(i.val+1)))).toRingHom` and `G := Uhat.map cval`.
  set cval : MvPolynomial (Fin n) ℚ →+* ℚ[X] :=
    (MvPolynomial.aeval (fun i : Fin n => (-1)^(i.val+1) * F.coeff (n-(i.val+1)))).toRingHom
  set G : Polynomial ℚ[X] := Uhat.map cval
  use G
  intro A _ ev x hx hx'
  simp_all
  convert congr_arg (Polynomial.map ((MvPolynomial.aeval x).toRingHom)) hU using 1
  any_goals exact (ev.comp Polynomial.C).toAlgebra
  · rw [Polynomial.map_map, Polynomial.map_map]
    congr! 1
    ext i
    simp [cval]
    have h_vieta : ∀ i : Fin n,
        ev (F.coeff (n - (i.val + 1))) = (-1)^(i.val + 1) * (Finset.univ.val.map x).esymm (i.val + 1) := by
      intro i
      have h_vieta : (F.map ev) = Polynomial.C (ev (F.leadingCoeff))
          * Multiset.prod (Multiset.map (fun β => Polynomial.X - Polynomial.C β) (Finset.univ.val.map x)) := by
        convert Polynomial.Splits.eq_prod_roots_of_monic _ _
        all_goals try infer_instance
        · aesop
        · rw [Polynomial.splits_iff_card_roots]
          rw [hx', Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> aesop
        · exact hF.map ev
      convert congr_arg (fun p => p.coeff (n - (i.val + 1))) h_vieta using 1
      · rw [Polynomial.coeff_map]
      · rw [Polynomial.coeff_C_mul, Multiset.prod_X_sub_C_coeff]
        · simp [hF.leadingCoeff]
          rw [Nat.sub_sub_self (by linarith [Fin.is_lt i])]
        · simp
    simp +zetaDelta at *
    rw [h_vieta i]
    ring_nf
    simp [pow_mul', MvPolynomial.aeval_esymm_eq_multiset_esymm]
  · convert fullResolventProduct_map _ _ _ using 1
    rotate_left
    convert fullResolventProduct_map _ _ _ using 1
    simp [fullResolventProduct]
    simp [Polynomial.map_prod, genForm]
    simp [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, MvPolynomial.aeval_X]

theorem exists_descended_resolvent (F : Polynomial (Polynomial ℚ)) (hF : F.Monic)
    (n : ℕ) (hFdeg : F.natDegree = n) :
    ∃ G : Polynomial (Polynomial ℚ), G.Monic ∧ G.natDegree = n.factorial ∧
      IsFullResolvent n F G := by
  obtain ⟨G, hG⟩ := fullResolvent_identity F hF n hFdeg
  -- Specialise at an injective ring hom into an algebraically closed field where `F` splits.
  set K := AlgebraicClosure (FractionRing (Polynomial ℚ))
  set ev₀ : Polynomial ℚ →+* K :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) with hev₀
  have hinj : Function.Injective ev₀ :=
    (algebraMap (FractionRing (Polynomial ℚ)) K).injective.comp
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  have hlc : ev₀ (F.leadingCoeff) ≠ 0 := by
    rw [hF.leadingCoeff, map_one]
    exact one_ne_zero
  have hdeg₀ : (F.map ev₀).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero ev₀ hlc, hFdeg]
  have hsplit : (F.map ev₀).Splits := IsAlgClosed.splits _
  have hcard : (F.map ev₀).roots.card = n :=
    (Polynomial.splits_iff_card_roots.mp hsplit).trans hdeg₀
  obtain ⟨x, hx⟩ := ResolventConstruction.exists_fin_map_eq (F.map ev₀).roots n hcard
  have hGmap : G.map ev₀ = fullResolventProduct n x := hG ev₀ x hdeg₀ hx.symm
  refine ⟨G, ?_, ?_, hG⟩
  · -- monic
    have hm : (G.map ev₀).leadingCoeff = 1 := by
      rw [hGmap]
      exact fullResolventProduct_monic n x
    rw [Polynomial.leadingCoeff_map_of_injective hinj] at hm
    show G.leadingCoeff = 1
    exact hinj (hm.trans (map_one ev₀).symm)
  · -- degree n!
    have hd : (G.map ev₀).natDegree = n.factorial := by
      rw [hGmap]
      exact fullResolventProduct_natDegree n x
    rwa [Polynomial.natDegree_map_eq_of_injective hinj] at hd

/-
**The per-specialisation resolvent-root property.** If `G` is the descended generic linear
resolvent of a monic `F` of `X`-degree `n`, then for every integer `t` the specialisation
`G(t, Y)` has a root inside the splitting field of `F(t, X)`.

Indeed, over `A := (F(t))`'s splitting field, `F(t)` splits with roots `x : Fin n → A`; the
descent identity `IsFullResolvent` gives `G(t).map (algebraMap ℚ A) = ∏_σ (Y − w_σ)`, and each
linear form `w_σ = ∑ᵢ i·x_(σ i)` lies in `A` and is a root of that product; take `α = w_id`.
-/
theorem resolvent_root_property (F G : Polynomial (Polynomial ℚ)) (hF : F.Monic)
    (n : ℕ) (hFdeg : F.natDegree = n) (hG : IsFullResolvent n F G) :
    ∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0 := by
  intro t
  set A := (specialize F t).SplittingField
  set ι := algebraMap ℚ A
  set p := specialize F t
  set ev := ι.comp (Polynomial.evalRingHom (t : ℚ))
  -- By `ResolventConstruction.exists_fin_map_eq` applied to `(F.map ev).roots` (card `n`), get `x : Fin n → A` with `Finset.univ.val.map x = (F.map ev).roots`.
  obtain ⟨x, hx⟩ : ∃ x : Fin n → A, Finset.univ.val.map x = (F.map ev).roots := by
    apply ResolventConstruction.exists_fin_map_eq
    have h_card_roots : (F.map ev).roots.card = (F.map ev).natDegree := by
      convert Polynomial.splits_iff_card_roots.mp _
      convert Polynomial.SplittingField.splits (specialize F t) using 1
      unfold specialize
      aesop
    rw [h_card_roots, Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> aesop
  -- By `hG`, we have `G.map ev = fullResolventProduct n x`.
  have hG_map : G.map ev = fullResolventProduct n x := by
    convert hG ev x _ _
    · rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num [hF, hFdeg]
    · exact hx.symm
  -- Let `α := genForm n x (1 : Equiv.Perm (Fin n))`.
  use genForm n x (1 : Equiv.Perm (Fin n))
  convert congr_arg (Polynomial.eval (genForm n x 1)) hG_map using 1
  · simp [specialize, aeval_def, Polynomial.eval_map]
    rw [Polynomial.eval₂_map]
  · simp [fullResolventProduct, Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]

/-- **Existence of the descended resolvent (symmetric-function descent).**

For `n ≥ 2` there is a monic `G ∈ ℚ[T][Y]` of degree `n!` which is the generic linear
resolvent of `F = Xⁿ − X − T` (`IsFullResolvent`) and which, at every integer specialisation
`t`, has a root inside the splitting field of `F(t, X)`. Assembled from
`exists_descended_resolvent` and `resolvent_root_property`. -/
theorem exists_fullResolvent (n : ℕ) (hn : 2 ≤ n) :
    ∃ G : Polynomial (Polynomial ℚ), G.Monic ∧ G.natDegree = n.factorial ∧
      IsFullResolvent n (genPoly n) G ∧
      (∀ t : ℤ, ∃ α : (specialize (genPoly n) t).SplittingField,
        (aeval α) (specialize G t) = 0) := by
  obtain ⟨G, hGmonic, hGdeg, hGfr⟩ :=
    exists_descended_resolvent (genPoly n) (genPoly_monic n hn) n (genPoly_natDegree n hn)
  exact ⟨G, hGmonic, hGdeg, hGfr,
    resolvent_root_property (genPoly n) G (genPoly_monic n hn) n (genPoly_natDegree n hn) hGfr⟩

/-!
### Base change to `ℚ̄(T)` and the geometric Galois group

We set up the base change of the Morse family `F = Xⁿ − X − T` to the rational function field
`ℚ̄(T)` over the algebraic closure `ℚ̄`, together with its Galois group.  The geometric
Galois group is expressed via the standard permutation representation
`Polynomial.Gal.galActionHom` on the roots; "the geometric Galois group is `Sₙ`" becomes
"this representation is surjective onto the full symmetric group on the roots".
-/

/-- `Fact` instance: any polynomial splits in its own splitting field.  (General; used to give
the `galActionHom` of `morseOverFrac` a well-formed statement over the splitting field.
Marked `local` so it does not leak into downstream files.) -/
local instance splitsInSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-- The ring map `ℚ[T] → ℚ̄(T)` (base change `ℚ → ℚ̄` on coefficients, then localisation). -/
def toClosureFrac : Polynomial ℚ →+* FractionRing (Polynomial (AlgebraicClosure ℚ)) :=
  (algebraMap (Polynomial (AlgebraicClosure ℚ))
      (FractionRing (Polynomial (AlgebraicClosure ℚ)))).comp
    (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))

/-- The Morse family `Xⁿ − X − T` base-changed to the geometric base field `ℚ̄(T)`. -/
def morseOverFrac (n : ℕ) : Polynomial (FractionRing (Polynomial (AlgebraicClosure ℚ))) :=
  (genPoly n).map toClosureFrac

/-- The base-change map `ℚ[T] → ℚ̄(T)` is injective. -/
theorem toClosureFrac_injective : Function.Injective toClosureFrac := by
  have h1 : Function.Injective
      (algebraMap (Polynomial (AlgebraicClosure ℚ))
        (FractionRing (Polynomial (AlgebraicClosure ℚ)))) :=
    IsFractionRing.injective (Polynomial (AlgebraicClosure ℚ))
      (FractionRing (Polynomial (AlgebraicClosure ℚ)))
  have h2 : Function.Injective (Polynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))) :=
    Polynomial.map_injective _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  exact h1.comp h2

/-- `morseOverFrac n` is monic. -/
theorem morseOverFrac_monic (n : ℕ) (hn : 2 ≤ n) : (morseOverFrac n).Monic :=
  (genPoly_monic n hn).map _

/-- `morseOverFrac n` has degree `n`. -/
theorem morseOverFrac_natDegree (n : ℕ) (hn : 2 ≤ n) : (morseOverFrac n).natDegree = n := by
  rw [morseOverFrac, Polynomial.natDegree_map_eq_of_injective toClosureFrac_injective]
  exact genPoly_natDegree n hn

/-
**The base-changed Morse family is separable over `ℚ̄(T)`.**

`Xⁿ − X − t` (with `t` the transcendental image of `T`) is separable: a common root `α` of
it and its derivative `nXⁿ⁻¹ − 1` would force `α = t·n/(1−n) ∈ ℚ̄(T)` (from `αⁿ = α/n`) and
`αⁿ⁻¹ = 1/n`, giving a nonzero polynomial relation over `ℚ̄` satisfied by the transcendental
`t`, a contradiction.
-/
set_option maxHeartbeats 1000000 in
theorem morseOverFrac_separable (n : ℕ) (hn : 2 ≤ n) : (morseOverFrac n).Separable := by
  refine' IsCoprime.symm _
  by_contra h_not_coprime
  -- Let $L$ be an algebraic closure of $\mathbb{Q}(T)$.
  set L := AlgebraicClosure (FractionRing (Polynomial (AlgebraicClosure ℚ)))
  -- Let $α$ be a root of $morseOverFrac n$ in $L$.
  obtain ⟨α, hα⟩ : ∃ α : L,
      (α^n - α - (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L)
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (Polynomial.X))) = 0 ∧ (n * α^(n-1) - 1) = 0 := by
    have h_common_root : ∃ α : L,
        Polynomial.eval α (Polynomial.map
          (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L) (morseOverFrac n)) = 0 ∧
        Polynomial.eval α (Polynomial.map
          (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L)
            (Polynomial.derivative (morseOverFrac n))) = 0 := by
      contrapose! h_not_coprime
      apply isCoprime_of_irreducible_dvd
      · intro h
        have := morseOverFrac_natDegree n hn
        aesop
      · intro z hz hz' hz''
        obtain ⟨α, hα⟩ : ∃ α : L,
          Polynomial.eval α (Polynomial.map (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L) z) = 0 := by
          apply_rules [@IsAlgClosed.exists_root]
          rw [Polynomial.degree_map]
          exact ne_of_gt (Polynomial.degree_pos_of_irreducible hz)
        refine h_not_coprime α ?_ ?_
        · simpa [hα] using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
            (Polynomial.map_dvd (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L) hz'') hα
        · simpa [hα] using Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
            (Polynomial.map_dvd (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L) hz') hα
    convert h_common_root using 4
    · unfold morseOverFrac
      simp [genPoly]
      unfold toClosureFrac
      aesop
    · unfold morseOverFrac
      norm_num [Polynomial.derivative_pow]
      unfold genPoly
      norm_num [Polynomial.derivative_pow]
  -- From $n * α^{n-1} - 1 = 0$, we get $α^{n-1} = 1/n$. Substitute into $α^n - α - t = 0$: $α/n - α - t = 0$, hence $α = t * n / (1 - n)$.
  have hα_val : α = (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ)))
        (Polynomial.X)) * (n : L) / (1 - (n : L)) := by
    have hα_val : α^n = α / (n : L) := by
      rw [eq_div_iff]
      · cases n <;> simp_all [pow_succ, mul_comm, mul_assoc]
        linear_combination' hα.2 * α
      · aesop
    rw [eq_div_iff] at * <;> norm_num at *
    · grind +revert
    · linarith
    · rw [sub_eq_zero]
      norm_cast
      linarith
  -- Substitute $α = t * n / (1 - n)$ into $α^{n-1} = 1/n$: $(t * n / (1 - n))^{n-1} = 1/n$.
  have h_subst : ((algebraMap (Polynomial (AlgebraicClosure ℚ))
        (FractionRing (Polynomial (AlgebraicClosure ℚ))) (Polynomial.X))
          * (n : FractionRing (Polynomial (AlgebraicClosure ℚ)))
          / (1 - (n : FractionRing (Polynomial (AlgebraicClosure ℚ))))) ^ (n - 1)
        = 1 / (n : FractionRing (Polynomial (AlgebraicClosure ℚ))) := by
    simp_all [sub_eq_iff_eq_add]
    rw [inv_eq_of_mul_eq_one_right]
    convert hα.2 using 1
    erw [← RingHom.injective (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ))) L) |>.eq_iff]
    norm_num
  -- This gives a nonzero polynomial equation over `AlgebraicClosure ℚ` satisfied by `T`, contradicting the transcendence of `T`.
  have h_poly_eq : ∃ p : Polynomial (AlgebraicClosure ℚ), p ≠ 0 ∧
      p.eval₂ (algebraMap (AlgebraicClosure ℚ) (FractionRing (Polynomial (AlgebraicClosure ℚ))))
        (algebraMap (Polynomial (AlgebraicClosure ℚ)) (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (Polynomial.X)) = 0 := by
    refine' ⟨(Polynomial.X * Polynomial.C (n : AlgebraicClosure ℚ)) ^ (n - 1)
      - Polynomial.C ((1 - n : AlgebraicClosure ℚ) ^ (n - 1) / n : AlgebraicClosure ℚ), _, _⟩ <;>
      norm_num
    · refine' ne_of_apply_ne Polynomial.natDegree _
      norm_num [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_mul', show n ≠ 0 by linarith]
      omega
    · convert sub_eq_zero.mpr (congr_arg (fun x : FractionRing (Polynomial (AlgebraicClosure ℚ)) =>
        x * (1 - n : FractionRing (Polynomial (AlgebraicClosure ℚ))) ^ (n - 1)) h_subst) using 1
      ring_nf
      have hne : (1 - n : FractionRing (Polynomial (AlgebraicClosure ℚ))) ≠ 0 :=
        sub_ne_zero_of_ne <| by
          norm_cast
          linarith
      norm_num [hne]
  obtain ⟨p, hp_ne_zero, hp_root⟩ := h_poly_eq
  simp_all [Polynomial.eval₂_eq_eval_map]

/-- Auxiliary coefficient embedding `A[X] → A[X][X]` used to build the variable swap of
`A[X][X]`: it sends the inner indeterminate to the outer one and constants `a` to `C (C a)`. -/
def swapCoeffHom (A : Type*) [CommRing A] : Polynomial A →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) Polynomial.X

/-- The ring endomorphism of `A[X][X]` that swaps the two indeterminates: the outer `X` goes to
`C X` and the coefficient variable (`C X`) goes to the outer `X`. -/
def swapVars (A : Type*) [CommRing A] :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (swapCoeffHom A) (Polynomial.C Polynomial.X)

theorem swapVars_comp_swapCoeffHom (A : Type*) [CommRing A] :
    (swapVars A).comp (swapCoeffHom A)
      = (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [swapVars, swapCoeffHom]
  · simp [swapVars, swapCoeffHom]

theorem swapVars_involutive (A : Type*) [CommRing A] :
    (swapVars A).comp (swapVars A) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro q
    show (swapVars A) ((swapVars A) (C q)) = C q
    have h1 : (swapVars A) (C q) = swapCoeffHom A q := by simp [swapVars]
    rw [h1]
    have := RingHom.congr_fun (swapVars_comp_swapCoeffHom A) q
    simpa using this
  · show (swapVars A) ((swapVars A) X) = X
    simp [swapVars, swapCoeffHom]

/-- The variable-swap ring automorphism of `A[X][X]`. -/
def swapVarsEquiv (A : Type*) [CommRing A] :
    Polynomial (Polynomial A) ≃+* Polynomial (Polynomial A) where
  toFun := swapVars A
  invFun := swapVars A
  left_inv := fun x => by
    have := RingHom.congr_fun (swapVars_involutive A) x
    simpa using this
  right_inv := fun x => by
    have := RingHom.congr_fun (swapVars_involutive A) x
    simpa using this
  map_mul' := map_mul _
  map_add' := map_add _

/-- Over an integral domain `A`, the polynomial `Xⁿ − X − T` (with `T` the coefficient
variable, i.e. `C X`) is irreducible in `A[X][X]`.  Swapping the two indeterminates turns it
into (a unit multiple of) `X − C (Xⁿ − X)`, which is irreducible as a linear monic polynomial
over the domain `A[X]`. -/
theorem X_pow_sub_X_sub_C_X_irreducible (A : Type*) [CommRing A] [IsDomain A] (n : ℕ) :
    Irreducible (X ^ n - X - C (X : Polynomial A)) := by
  have key : (swapVarsEquiv A) (X ^ n - X - C (X : Polynomial A))
      = -(X - C ((X : Polynomial A) ^ n - X)) := by
    simp only [swapVarsEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk]
    simp [swapVars, swapCoeffHom]
  rw [← MulEquiv.irreducible_iff (swapVarsEquiv A), key]
  have hu : IsUnit (-1 : Polynomial (Polynomial A)) :=
    (isUnit_one (M := Polynomial (Polynomial A))).neg
  have hneg : (-(X - C ((X : Polynomial A) ^ n - X)))
      = (-1 : Polynomial (Polynomial A)) * (X - C ((X : Polynomial A) ^ n - X)) := by ring
  rw [hneg]
  exact (irreducible_isUnit_mul hu).mpr (irreducible_X_sub_C _)

/-- **Absolute irreducibility of the Morse family over `ℚ̄(T)`.**

The base-changed Morse family `Xⁿ − X − T` is irreducible over the geometric base field
`ℚ̄(T)`.  This is the classical fact that `Xⁿ − X − T`, viewed in `ℚ̄[X, T]`, is linear (hence
irreducible) in the variable `T` and primitive in `X` (`X_pow_sub_X_sub_C_X_irreducible`);
Gauss's lemma (`Monic.irreducible_iff_irreducible_map_fraction_map`) then transports
irreducibility from `ℚ̄[T][X]` to `ℚ̄(T)[X]`. -/
theorem morseOverFrac_irreducible (n : ℕ) (hn : 2 ≤ n) : Irreducible (morseOverFrac n) := by
  have hmap : morseOverFrac n
      = ((genPoly n).map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
          (algebraMap (Polynomial (AlgebraicClosure ℚ))
            (FractionRing (Polynomial (AlgebraicClosure ℚ)))) := by
    rw [morseOverFrac, Polynomial.map_map, toClosureFrac]
  set P := (genPoly n).map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) with hPdef
  have hP : P = X ^ n - X - C (X : Polynomial (AlgebraicClosure ℚ)) := by
    rw [hPdef]
    unfold genPoly
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hPmonic : P.Monic := (genPoly_monic n hn).map _
  rw [hmap, ← Monic.irreducible_iff_irreducible_map_fraction_map hPmonic, hP]
  exact X_pow_sub_X_sub_C_X_irreducible (AlgebraicClosure ℚ) n

/-- **Transitivity of the geometric Galois action.**

Because `morseOverFrac n` is irreducible over `ℚ̄(T)`, the Galois group acts transitively on
the roots. -/
theorem morse_galAction_isPretransitive (n : ℕ) (hn : 2 ≤ n) :
    MulAction.IsPretransitive (morseOverFrac n).Gal
      ((morseOverFrac n).rootSet (morseOverFrac n).SplittingField) :=
  Gal.galAction_isPretransitive (morseOverFrac n) _ (morseOverFrac_irreducible n hn)

open scoped Classical in
/-- **Reduction to a generating set of transpositions.**

General criterion: for a polynomial `p` that splits in `E`, if its Galois action on the roots
is transitive and there is a generating set of the Galois group each of whose elements acts as
a transposition of the roots, then the permutation representation `galActionHom` is surjective
(i.e. the Galois group is the full symmetric group).  This is a direct wrapper around Mathlib's
`surjective_of_isSwap_of_isPretransitive`. -/
theorem galActionHom_surjective_of_swaps {F E : Type} [Field F] [Field E] [Algebra F E]
    (p : F[X]) [Fact ((p.map (algebraMap F E)).Splits)]
    [MulAction.IsPretransitive p.Gal (p.rootSet E)]
    (S : Set p.Gal) (hS1 : ∀ σ ∈ S, (Gal.galActionHom p E σ).IsSwap)
    (hS2 : Subgroup.closure S = ⊤) :
    Function.Surjective (Gal.galActionHom p E) := by
  classical
  exact surjective_of_isSwap_of_isPretransitive (G := p.Gal) (α := p.rootSet E) S hS1 hS2

open scoped Classical in
/-- **Reduction via Jordan's theorem (primitivity + one transposition).**

An alternative to `galActionHom_surjective_of_swaps`: for a polynomial `p` that splits in
`E`, if its Galois action on the roots is *primitive* and *some* Galois element acts as a
single transposition of the roots, then `galActionHom` is surjective (the Galois group is the
full symmetric group).  This wraps Mathlib's Jordan theorem
`Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`, transporting primitivity of the
`p.Gal`-action to the range subgroup via `MulAction.IsPreprimitive.of_surjective`. -/
theorem galActionHom_surjective_of_isPreprimitive_of_swap {F E : Type} [Field F] [Field E]
    [Algebra F E] (p : F[X]) [Fact ((p.map (algebraMap F E)).Splits)]
    [MulAction.IsPreprimitive p.Gal (p.rootSet E)]
    (σ : p.Gal) (hσ : (Gal.galActionHom p E σ).IsSwap) :
    Function.Surjective (Gal.galActionHom p E) := by
  classical
  set G := (Gal.galActionHom p E).range with hG
  have hequiv : MulAction.IsPreprimitive (G : Subgroup (Equiv.Perm (p.rootSet E)))
      (p.rootSet E) := by
    let f : (p.rootSet E) →ₑ[(Gal.galActionHom p E).rangeRestrict] (p.rootSet E) :=
      { toFun := id
        map_smul' := fun g x => rfl }
    exact MulAction.IsPreprimitive.of_surjective (M := p.Gal) (f := f) Function.surjective_id
  have hmem : (Gal.galActionHom p E σ) ∈ G := by
    rw [hG]
    exact ⟨σ, rfl⟩
  have htop : G = ⊤ :=
    Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hequiv _ hσ hmem
  rw [← MonoidHom.range_eq_top, ← hG, htop]

/-- The specialized generic polynomial agrees with the geometric Morse polynomial. -/
theorem morseOverFrac_eq_morseGeomPoly (n : ℕ) : morseOverFrac n = morseGeomPoly n := by
  have hmap : morseOverFrac n
      = ((genPoly n).map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
          (algebraMap (Polynomial (AlgebraicClosure ℚ))
            (FractionRing (Polynomial (AlgebraicClosure ℚ)))) := by
    rw [morseOverFrac, Polynomial.map_map, toClosureFrac]
  have hP : (genPoly n).map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))
      = genPolyC n := by
    unfold genPoly genPolyC
    simp [Polynomial.map_sub, Polynomial.map_pow]
  rw [hmap, hP, morseGeomPoly]

open scoped Classical in
/-- **The geometric monodromy input (the geometric Galois group is generated by
transpositions).**

Combined with transitivity (`morse_galAction_isPretransitive`) and the group-theoretic wrapper
`galActionHom_surjective_of_swaps`, this yields `morse_geometric_galois_surjective`. -/
theorem morse_gal_generated_by_swaps (n : ℕ) (hn : 2 ≤ n) :
    ∃ S : Set (morseOverFrac n).Gal,
      (∀ σ ∈ S,
        (Gal.galActionHom (morseOverFrac n) (morseOverFrac n).SplittingField σ).IsSwap) ∧
      Subgroup.closure S = ⊤ := by
  rw [morseOverFrac_eq_morseGeomPoly n]
  exact morseGeomPoly_gal_generated_by_swaps n hn

open scoped Classical in
/-- **The geometric monodromy input (the geometric Galois group is `Sₙ`).**

The permutation representation of the Galois group of the base-changed Morse family
`Xⁿ − X − T` over `ℚ̄(T)` on its roots is *surjective* onto the full symmetric group.
Equivalently, the geometric Galois group is `Sₙ`.

This is now assembled from three inputs: transitivity of the action
(`morse_galAction_isPretransitive`, which follows from irreducibility over `ℚ̄(T)`), the
generation of the group by transpositions (`morse_gal_generated_by_swaps`, the deep monodromy
computation), and the group-theoretic wrapper `galActionHom_surjective_of_swaps`. -/
theorem morse_geometric_galois_surjective (n : ℕ) (hn : 2 ≤ n) :
    Function.Surjective
      (Gal.galActionHom (morseOverFrac n) (morseOverFrac n).SplittingField) := by
  haveI := morse_galAction_isPretransitive n hn
  obtain ⟨S, hS1, hS2⟩ := morse_gal_generated_by_swaps n hn
  exact galActionHom_surjective_of_swaps (morseOverFrac n) S hS1 hS2

/-
**General Galois criterion for irreducibility.**  In a finite Galois extension `M/L`, a
monic polynomial `q ∈ L[Y]` with a root `w ∈ M` whose Galois orbit has cardinality equal to
`q.natDegree` is irreducible.  (The minimal polynomial of `w` divides `q`, has degree equal to
the orbit size, hence equals `q`.)
-/
theorem Monic.irreducible_of_galois_orbit_card
    {L M : Type*} [Field L] [Field M] [Algebra L M] [FiniteDimensional L M] [IsGalois L M]
    {q : L[X]} (hq : q.Monic) {w : M} (hw : (aeval w) q = 0)
    (hcard : Nat.card (MulAction.orbit (M ≃ₐ[L] M) w) = q.natDegree) :
    Irreducible q := by
  -- Since $w$ is a root of $q$, the minimal polynomial of $w$ over $L$ divides $q$.
  have h_minpoly_div : minpoly L w ∣ q := by
    exact minpoly.dvd L w hw
  -- Since $w$ is a root of $q$, the minimal polynomial of $w$ over $L$ has degree equal to the cardinality of its Galois orbit.
  have h_minpoly_deg : (minpoly L w).natDegree = Nat.card (MulAction.orbit (Gal(M/L)) w) := by
    have h_minpoly_deg : (minpoly L w).rootSet M = (MulAction.orbit (Gal(M/L)) w : Set M) := by
      ext x
      rw [Polynomial.mem_rootSet]
      rw [← Normal.minpoly_eq_iff_mem_orbit]
      constructor <;> intro h <;> simp_all
      · refine' minpoly.eq_of_irreducible_of_monic _ _ _
        · exact minpoly.irreducible (IsGalois.integral L x)
        · have h_minpoly_eq : minpoly L w = minpoly L x := by
            refine' minpoly.eq_of_irreducible_of_monic _ _ _
            · exact minpoly.irreducible (show IsIntegral L w from by exact (IsIntegral.of_finite L w))
            · exact h.2
            · exact minpoly.monic (show IsIntegral L w from by exact (IsIntegral.of_finite L w))
          exact h_minpoly_eq ▸ minpoly.aeval L w
        · exact minpoly.monic (show IsIntegral L x from by exact (IsGalois.integral L x))
      · exact ⟨minpoly.ne_zero (show IsIntegral L w from by exact (IsGalois.integral L w)),
          by rw [← h, minpoly.aeval]⟩
    rw [← h_minpoly_deg, Nat.card_eq_fintype_card]
    rw [Polynomial.card_rootSet_eq_natDegree]
    · exact IsGalois.separable L w
    · exact IsGalois.splits L w
  obtain ⟨p, rfl⟩ := h_minpoly_div
  rw [Polynomial.natDegree_mul'] at hcard
  · rw [irreducible_mul_iff]
    exact Or.inl ⟨minpoly.irreducible (show IsIntegral L w from by exact (IsIntegral.of_finite L w)),
      Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree] <;> aesop)⟩
  · aesop

/-
**Distinctness of the linear forms.**  If the roots `x` are distinct (in a characteristic
zero domain) and every transposition of two roots is realised by a ring endomorphism of `M`
(as happens for the Galois action of the full symmetric group), then the `n!` linear forms
`σ ↦ ∑ᵢ i·x_(σ i)` are pairwise distinct.

Proof: if `w_σ = w_τ` with `σ ≠ τ`, reindex to `∑_j c_j x_j = 0` with `c_j = σ⁻¹ j − τ⁻¹ j`;
as `σ ≠ τ` the integers `c_j` are not all equal (their equal value would have to be `0`), so
pick `a, b` with `c_a ≠ c_b`; applying the ring map realising the transposition `(a b)` and
subtracting gives `(c_a − c_b)(x_a − x_b) = 0`, forcing `x_a = x_b`, a contradiction.
-/
theorem genForm_perm_injective {n : ℕ} {M : Type*} [CommRing M] [IsDomain M] [CharZero M]
    (x : Fin n → M) (hxinj : Function.Injective x)
    (hswap : ∀ a b : Fin n, a ≠ b → ∃ f : M →+* M,
        ∀ j, f (x j) = x (Equiv.swap a b j)) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => genForm n x σ) := by
  intro σ τ hστ
  by_contra h_neq
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin n, a ≠ b ∧ (σ.symm a : ℤ) - (τ.symm a : ℤ) ≠ (σ.symm b : ℤ) - (τ.symm b : ℤ) := by
    by_cases h_eq : ∀ a b : Fin n, (σ.symm a : ℤ) - (τ.symm a : ℤ) = (σ.symm b : ℤ) - (τ.symm b : ℤ)
    · have h_eq_all : ∃ k : ℤ, ∀ a : Fin n, (σ.symm a : ℤ) = (τ.symm a : ℤ) + k := by
        rcases n with (_ | _ | n) <;> norm_num at *
        exact ⟨(σ.symm 0 : ℤ) - (τ.symm 0 : ℤ), fun a => by linarith [h_eq a 0]⟩
      obtain ⟨k, hk⟩ := h_eq_all
      have h_sum_eq : ∑ a : Fin n, (σ.symm a : ℤ) = ∑ a : Fin n, (τ.symm a : ℤ) := by
        exact Equiv.sum_comp σ.symm (fun a => (a : ℤ)) ▸ Equiv.sum_comp τ.symm (fun a => (a : ℤ)) ▸ rfl
      have h_k_zero : k = 0 := by
        simp_all [Finset.sum_add_distrib]
        cases n <;> simp_all
        exact False.elim (h_neq (Subsingleton.elim _ _))
      have h_sigma_eq_tau : σ.symm = τ.symm := by
        ext a
        specialize hk a
        aesop
      have h_sigma_eq_tau' : σ = τ := by
        simpa using congr_arg Equiv.symm h_sigma_eq_tau
      contradiction
    · grind +ring
  obtain ⟨f, hf⟩ := hswap a b hab.left
  have h_eq : ∑ j : Fin n, ((σ.symm j : ℤ) - (τ.symm j : ℤ)) * (x j - f (x j)) = 0 := by
    have h_eq : ∑ j : Fin n, ((σ.symm j : ℤ) - (τ.symm j : ℤ)) * x j = 0 := by
      convert sub_eq_zero.mpr hστ using 1
      simp [sub_mul, Finset.sum_sub_distrib, genForm]
      exact congrArg₂ _
        (by
          rw [← Equiv.sum_comp σ]
          simp)
        (by
          rw [← Equiv.sum_comp τ]
          simp)
    have h_eq_f : ∑ j : Fin n, ((σ.symm j : ℤ) - (τ.symm j : ℤ)) * f (x j) = 0 := by
      replace h_eq := congr_arg f h_eq
      simp_all [sub_mul]
    simp_all [mul_sub]
  rw [Finset.sum_eq_add (a) (b)] at h_eq
  · simp_all [sub_eq_iff_eq_add]
    have hcast : (σ.symm a : M) = (σ.symm b : M) - (τ.symm b : M) + (τ.symm a : M) :=
      mul_left_cancel₀ (sub_ne_zero_of_ne (hxinj.ne hab.1)) <| by linear_combination' h_eq
    exact hab.2 (by exact_mod_cast hcast)
  · exact hab.1
  · simp +contextual [hf, Equiv.swap_apply_def]
  · exact fun h => False.elim <| h <| Finset.mem_univ a
  · exact fun h => False.elim <| h <| Finset.mem_univ b

/-
**The Galois orbit of the base linear form is the set of all `n!` forms.**  If every
automorphism `γ` of `M` permutes the roots `x` (via some `σ`, hypothesis `hgal`) and every
permutation of the roots is realised by some automorphism (hypothesis `hsurj2`), then the orbit
of `w_id = ∑ᵢ i·x_i` under `Gal(M/L)` equals the range of `σ ↦ w_σ`.
-/
theorem orbit_genForm_eq_range {n : ℕ} {L M : Type*} [Field L] [Field M] [Algebra L M]
    (x : Fin n → M)
    (hgal : ∀ γ : M ≃ₐ[L] M, ∃ σ : Equiv.Perm (Fin n), ∀ i, γ (x i) = x (σ i))
    (hsurj2 : ∀ σ : Equiv.Perm (Fin n), ∃ γ : M ≃ₐ[L] M, ∀ i, γ (x i) = x (σ i)) :
    MulAction.orbit (M ≃ₐ[L] M) (genForm n x 1)
      = Set.range (fun σ : Equiv.Perm (Fin n) => genForm n x σ) := by
  ext y
  simp [MulAction.orbit]
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨σ, hσ⟩ := hgal γ
    use σ
    simp [genForm, hσ]
  · rintro ⟨σ, rfl⟩
    obtain ⟨γ, hγ⟩ := hsurj2 σ
    use γ
    simp [genForm, hγ]

/-- **Realising root permutations by automorphisms.**  If the permutation representation of
`p.Gal` on the roots is surjective, then every permutation `π` of the root set is induced by an
`L`-algebra automorphism `γ` of the splitting field (`γ r = π r` on roots). -/
theorem exists_algEquiv_of_galActionHom_surjective {L : Type*} [Field L] (p : L[X])
    [Fact ((p.map (algebraMap L p.SplittingField)).Splits)] [Normal L p.SplittingField]
    (hsurj : Function.Surjective (Gal.galActionHom p p.SplittingField))
    (π : Equiv.Perm (p.rootSet p.SplittingField)) :
    ∃ γ : p.SplittingField ≃ₐ[L] p.SplittingField,
      ∀ r : p.rootSet p.SplittingField, γ (r : p.SplittingField) = (π r : p.SplittingField) := by
  obtain ⟨φ, hφ⟩ := hsurj π
  obtain ⟨ϕ, hϕ⟩ := Gal.restrict_surjective (p := p) (E := p.SplittingField) φ
  refine ⟨ϕ, fun r => ?_⟩
  have h := Gal.galActionHom_restrict (p := p) (E := p.SplittingField) ϕ r
  rw [hϕ, hφ] at h
  exact h.symm

/-
**Root enumeration with Galois transport.**  Under the surjectivity hypothesis, there is
an enumeration `x : Fin n → M` (with `M` the splitting field) of the roots of the Morse family
over `M` that is injective, realises the descent identity's root hypotheses, and along which
the Galois group acts by permutations, surjectively (every permutation of the roots is realised
by an automorphism).
-/
set_option maxHeartbeats 4000000 in
theorem morse_root_enum (n : ℕ) (hn : 2 ≤ n)
    (hsurj : Function.Surjective
      (Gal.galActionHom (morseOverFrac n) (morseOverFrac n).SplittingField)) :
    ∃ x : Fin n → (morseOverFrac n).SplittingField, Function.Injective x ∧
      ((genPoly n).map
        ((algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (morseOverFrac n).SplittingField).comp toClosureFrac)).natDegree = n ∧
      ((genPoly n).map
        ((algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
          (morseOverFrac n).SplittingField).comp toClosureFrac)).roots
          = Finset.univ.val.map x ∧
      (∀ γ : (morseOverFrac n).SplittingField ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))]
          (morseOverFrac n).SplittingField, ∃ σ : Equiv.Perm (Fin n), ∀ i, γ (x i) = x (σ i)) ∧
      (∀ σ : Equiv.Perm (Fin n),
        ∃ γ : (morseOverFrac n).SplittingField ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))]
          (morseOverFrac n).SplittingField, ∀ i, γ (x i) = x (σ i)) := by
  obtain ⟨x, hx⟩ : ∃ x : Fin n → (morseOverFrac n).SplittingField,
      (map
        ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
        (genPoly n)).roots = Multiset.map x Finset.univ.val := by
        have h_card : Multiset.card (Polynomial.roots (Polynomial.map
          ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
          (genPoly n))) = n := by
          have h_card : Polynomial.natDegree (Polynomial.map
            ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
            (genPoly n)) = n := by
            rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num [genPoly]
            · rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
              linarith
            · rw [Polynomial.leadingCoeff, Polynomial.natDegree_sub_C,
                Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num [Polynomial.coeff_X,
                Polynomial.coeff_C, show n > 1 by linarith]
              aesop
          convert Polynomial.splits_iff_card_roots.mp _
          · exact h_card.symm
          · convert Polynomial.SplittingField.splits (morseOverFrac n) using 1
            unfold morseOverFrac
            aesop
        have := @ResolventConstruction.exists_fin_map_eq
        exact Exists.elim (this _ _ h_card) fun x hx => ⟨x, hx.symm⟩
  refine' ⟨x, _, _, hx, _, _⟩
  · have h_distinct_roots : Multiset.Nodup (Polynomial.roots (map
      ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
      (genPoly n))) := by
      convert Polynomial.nodup_roots _
      convert morseOverFrac_separable n hn |> Polynomial.Separable.map
      unfold morseOverFrac
      aesop
    simp_all [Function.Injective]
    rw [List.nodup_ofFn] at h_distinct_roots
    aesop
  · convert morseOverFrac_natDegree n hn using 1
    unfold morseOverFrac
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero,
      Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num [genPoly_monic n hn]
  · intro γ
    have h_root : ∀ i, γ (x i) ∈ (map
      ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
      (genPoly n)).roots := by
      intro i
      have h_root : x i ∈ (map
        ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
        (genPoly n)).roots := by
        aesop
      simp +zetaDelta at *
      rw [Polynomial.eval_map] at *
      rw [Polynomial.eval₂_eq_sum_range] at *
      exact ⟨h_root.1, by simpa [map_sum, map_mul, map_pow] using congr_arg (fun x => γ x) h_root.2⟩
    have h_unique : ∀ i, ∃ j, γ (x i) = x j := by
      intro i
      specialize h_root i
      rw [hx] at h_root
      rw [Multiset.mem_map] at h_root
      obtain ⟨j, hj, hj'⟩ := h_root
      use j
      aesop
    choose σ hσ using h_unique
    have h_inj : Function.Injective σ := by
      intro i j hij
      have := γ.injective
      simp_all
      have h_distinct : Multiset.Nodup (Multiset.ofList (List.ofFn x)) := by
        have h_distinct : Polynomial.Separable (map
          ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
          (genPoly n)) := by
          convert morseOverFrac_separable n hn |> Polynomial.Separable.map using 1
          unfold morseOverFrac
          aesop
        exact hx ▸ Polynomial.nodup_roots h_distinct
      simp_all [List.nodup_ofFn]
      have := @this (x i) (x j)
      aesop
    exact ⟨Equiv.ofBijective σ ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩, hσ⟩
  · intro σ
    obtain ⟨γ, hγ⟩ : ∃ γ : (morseOverFrac n).SplittingField
        ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (morseOverFrac n).SplittingField,
        ∀ i, γ (x i) = x (σ i) := by
      have h_root_set : ∀ i, x i ∈ Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField := by
        intro i
        have h_root : x i ∈ (map
          ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
          (genPoly n)).roots := by
          aesop
        convert h_root using 1
        ext
        simp [morseOverFrac]
        simp [Polynomial.mem_rootSet]
        simp [Polynomial.eval_map]
        simp [Polynomial.map, Polynomial.eval₂_eq_sum_range]
        intro h
        rw [Polynomial.ext_iff]
        simp [Polynomial.ext_iff]
      have h_root_set_equiv : Function.Bijective
          (fun i : Fin n => ⟨x i, h_root_set i⟩ :
            Fin n → Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField) := by
        have h_inj : Function.Injective x := by
          have h_distinct_roots : Multiset.Nodup (Polynomial.roots (Polynomial.map
            ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
            (genPoly n))) := by
            have h_distinct_roots : Polynomial.Separable (Polynomial.map
              ((algebraMap (FractionRing (AlgebraicClosure ℚ)[X]) (morseOverFrac n).SplittingField).comp toClosureFrac)
              (genPoly n)) := by
              convert morseOverFrac_separable n hn |> Polynomial.Separable.map
              unfold morseOverFrac
              aesop
            exact Polynomial.nodup_roots h_distinct_roots
          simp_all [Function.Injective]
          rw [List.nodup_ofFn] at h_distinct_roots
          aesop
        have h_card : Fintype.card (Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField) = n := by
          convert congr_arg Multiset.card hx using 1
          · convert Polynomial.card_rootSet_eq_natDegree _ _
            · convert congr_arg Multiset.card hx using 1
              convert morseOverFrac_natDegree n hn using 1
              simp
            · exact morseOverFrac_separable n hn
            · convert SplittingField.splits (morseOverFrac n) using 1
          · simp
        have h_surj : Function.Surjective
            (fun i : Fin n => ⟨x i, h_root_set i⟩ :
              Fin n → Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField) := by
          exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j hij => h_inj <| by simpa using hij,
            by aesop⟩ |>.2
        exact ⟨fun i j hij => h_inj <| by simpa using congr_arg Subtype.val hij, h_surj⟩
      obtain ⟨γ, hγ⟩ : ∃ γ : Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField
          ≃ Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField,
          ∀ i, γ (⟨x i, h_root_set i⟩) = ⟨x (σ i), h_root_set (σ i)⟩ := by
        have h_root_set_equiv : Function.Bijective
            (fun i : Fin n => ⟨x (σ i), h_root_set (σ i)⟩ :
              Fin n → Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField) := by
          exact Function.Bijective.comp h_root_set_equiv (σ.bijective)
        exact ⟨Equiv.ofBijective _ h_root_set_equiv |> Equiv.trans
          (Equiv.ofBijective _ ‹Function.Bijective fun i => ⟨x i, h_root_set i⟩ › |> Equiv.symm),
          fun i => by simp⟩
      obtain ⟨γ', hγ'⟩ : ∃ γ' : (morseOverFrac n).SplittingField
          ≃ₐ[FractionRing (Polynomial (AlgebraicClosure ℚ))] (morseOverFrac n).SplittingField,
          ∀ r : Polynomial.rootSet (morseOverFrac n) (morseOverFrac n).SplittingField,
          γ' (r : (morseOverFrac n).SplittingField) = (γ r : (morseOverFrac n).SplittingField) := by
        convert exists_algEquiv_of_galActionHom_surjective (morseOverFrac n) hsurj γ
      exact ⟨γ', fun i => by simpa [hγ] using hγ' ⟨x i, h_root_set i⟩⟩
    use γ

/-
**The resolvent is irreducible over `ℚ̄(T)` (given the full geometric Galois group).**

With `L = ℚ̄(T)` and `M` the splitting field of `morseOverFrac n`, the base-changed resolvent
`G.map toClosureFrac ∈ L[Y]` is irreducible.  Over `M`, `G` splits as `∏_σ (Y − w_σ)` with
`w_σ = ∑ᵢ i·x_(σ i)` for the (distinct) roots `x` of the Morse family (descent identity
`hG`); the Galois action (surjective onto `Sₙ` by `hsurj`) sends `w_id ↦ w_γ`, so the orbit of
`w_id` is the whole set of `n!` distinct forms, of cardinality `n! = (G.map _).natDegree`.
Apply `Monic.irreducible_of_galois_orbit_card`.
-/
theorem morseResolventFrac_irreducible (n : ℕ) (hn : 2 ≤ n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic) (hG : IsFullResolvent n (genPoly n) G)
    (hsurj : Function.Surjective
      (Gal.galActionHom (morseOverFrac n) (morseOverFrac n).SplittingField)) :
    Irreducible (G.map toClosureFrac) := by
  obtain ⟨x, hxinj, hdeg, hroots, hgal, hsurj2⟩ := morse_root_enum n hn hsurj
  -- Let `w := genForm n x (1 : Equiv.Perm (Fin n))`. Then `aeval w q = 0`.
  set w := genForm n x 1
  have hw : (aeval w) (map toClosureFrac G) = 0 := by
    specialize hG ((algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
      (morseOverFrac n).SplittingField).comp toClosureFrac) x hdeg hroots
    convert congr_arg (Polynomial.eval w) hG using 1
    · simp [Polynomial.aeval_def, Polynomial.eval_map]
      simp [Polynomial.eval₂_map]
    · simp [fullResolventProduct]
      rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ 1)]
      aesop
  convert Monic.irreducible_of_galois_orbit_card _ hw _
  · convert IsGalois.of_separable_splitting_field (morseOverFrac_separable n hn)
    infer_instance
  · exact hGmonic.map _
  · convert Nat.card_range_of_injective (genForm_perm_injective x hxinj _) using 1
    · rw [orbit_genForm_eq_range x hgal hsurj2]
    · convert fullResolventProduct_natDegree n x using 1
      · convert congr_arg Polynomial.natDegree
          (hG (algebraMap (FractionRing (Polynomial (AlgebraicClosure ℚ)))
              (morseOverFrac n).SplittingField |> RingHom.comp <| toClosureFrac) x hdeg hroots) using 1
        rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero,
          Polynomial.natDegree_map_of_leadingCoeff_ne_zero] <;> norm_num [hGmonic]
      · simp [Fintype.card_perm]
    · exact fun a b hab => by
        obtain ⟨γ, hγ⟩ := hsurj2 (Equiv.swap a b)
        exact ⟨γ, hγ⟩

/-- **Reduction: full geometric Galois group ⟹ the resolvent is absolutely irreducible.**

If the permutation representation of the geometric Galois group of `Xⁿ − X − T` over `ℚ̄(T)`
is surjective (i.e. the group is `Sₙ`), then the generic linear resolvent `G` stays
irreducible after base change to `ℚ̄`. -/
theorem abs_irreducible_of_geometric_galois_surjective (n : ℕ) (hn : 2 ≤ n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic) (hG : IsFullResolvent n (genPoly n) G)
    (hsurj : Function.Surjective
      (Gal.galActionHom (morseOverFrac n) (morseOverFrac n).SplittingField)) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) := by
  -- `GK := G.map (ℚ → ℚ̄)` is monic; by Gauss it is irreducible iff its image over `ℚ̄(T)` is.
  have hmonicGK : (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).Monic := hGmonic.map _
  rw [hmonicGK.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial (AlgebraicClosure ℚ)))]
  have heq : (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))).map
      (algebraMap (Polynomial (AlgebraicClosure ℚ))
        (FractionRing (Polynomial (AlgebraicClosure ℚ))))
      = G.map toClosureFrac := by
    rw [Polynomial.map_map]
    rfl
  rw [heq]
  exact morseResolventFrac_irreducible n hn G hGmonic hG hsurj

/-- **Geometric (absolute) irreducibility (the geometric Galois group is `Sₙ`).**

The generic linear resolvent `G` stays irreducible after base change to `ℚ̄`.  Equivalently,
the geometric Galois group of `Xⁿ − X − T` over `ℚ̄(T)` is `Sₙ`; this is the Morse-polynomial
monodromy computation (`g(X) = Xⁿ − X` has distinct critical values, so the local monodromy
generators are transpositions that generate `Sₙ`).

Decomposed into the geometric monodromy input `morse_geometric_galois_surjective` and the
algebraic reduction `abs_irreducible_of_geometric_galois_surjective`. -/
theorem fullResolvent_abs_irreducible (n : ℕ) (hn : 2 ≤ n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic) (hG : IsFullResolvent n (genPoly n) G) :
    Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) :=
  abs_irreducible_of_geometric_galois_surjective n hn G hGmonic hG
    (morse_geometric_galois_surjective n hn)

/-- **Arithmetic irreducibility (the generic Galois group is `Sₙ`).**

The generic linear resolvent `G` of the Morse family `Xⁿ − X − T` is irreducible over
`ℚ(T)`.  Equivalently, the Galois group of `Xⁿ − X − T` over `ℚ(T)` is the full symmetric
group `Sₙ`, acting transitively on the `n!` linear forms `w_σ` (which are pairwise distinct
because the coefficients `0, 1, …, n−1` are).

This is deduced from the geometric (absolute) irreducibility `fullResolvent_abs_irreducible`
by descent along the base change `ℚ[T] → ℚ̄[T]`: for a monic polynomial, irreducibility of
the base-changed polynomial implies irreducibility of the original
(`Polynomial.Monic.irreducible_of_irreducible_map`). -/
theorem fullResolvent_irreducible (n : ℕ) (hn : 2 ≤ n)
    (G : Polynomial (Polynomial ℚ)) (hGmonic : G.Monic)
    (hG : IsFullResolvent n (genPoly n) G) :
    Irreducible G :=
  hGmonic.irreducible_of_irreducible_map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ))) G
    (fullResolvent_abs_irreducible n hn G hGmonic hG)

/-
**The trivial base case `n = 1`** (`S₁` is the trivial group): a degree-`1` family and a
degree-`1! = 1` resolvent do the job.
-/
theorem resolvent_family_core_one :
    ∃ (F G : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = 1 ∧
      G.Monic ∧ G.natDegree = Nat.factorial 1 ∧ Irreducible G ∧
      Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0) := by
  use Polynomial.X - Polynomial.C Polynomial.X, Polynomial.X
  simp [specialize]
  refine' ⟨_, _, _, _⟩
  · exact Polynomial.monic_X_sub_C _
  · exact Polynomial.irreducible_X
  · exact Polynomial.irreducible_X
  · refine' Set.Finite.subset (Set.finite_singleton 0) _
    intro t ht
    contrapose! ht
    simp_all [Polynomial.Separable]
    exact isCoprime_one_right

/-- **The core of `exists_resolvent_family`**: for every `n ≥ 1` there is a Morse family
`F ∈ ℚ[T][X]` of degree `n` together with a monic degree-`n!` resolvent `G ∈ ℚ[T][Y]` which is
irreducible and absolutely irreducible, with `F(t)` separable for cofinitely many `t` and a
root of `G(t)` inside the splitting field of `F(t)` for every `t`.

This is exactly `IsInverseGalois.exists_resolvent_family` **minus** its final
"`{t | Irreducible (specialize G t)}.Infinite`" conjunct (which is then supplied by Hilbert's
Irreducibility Theorem). -/
theorem exists_resolvent_family_core (n : ℕ) (hn : 1 ≤ n) :
    ∃ (F G : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧
      G.Monic ∧ G.natDegree = n.factorial ∧ Irreducible G ∧
      Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    exact resolvent_family_core_one
  · -- n ≥ 2 : the Morse family
    obtain ⟨G, hGmonic, hGdeg, hGfr, hGroot⟩ := exists_fullResolvent n h2
    exact ⟨genPoly n, G, genPoly_monic n h2, genPoly_natDegree n h2, hGmonic, hGdeg,
      fullResolvent_irreducible n h2 G hGmonic hGfr,
      fullResolvent_abs_irreducible n h2 G hGmonic hGfr,
      genPoly_separable_cofinite n h2, hGroot⟩

end ResolventFamily

end