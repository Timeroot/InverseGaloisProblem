/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Transfer.IntegralLift

/-!
# The factorizations of a two-variable polynomial, as a finite scheme over the parameters

Fix a polynomial `F` in two variables `X` and `Y`, monic of degree `n` in `Y`, whose coefficients
lie in a ring `A` of parameters, and fix a bound `E` on the degrees in `X` of the coefficients of
its putative factors.  A factorization `F = G * H` into monic polynomials of degrees `m` and `l`
in `Y`, over an `A`-algebra `S`, is the same thing as a solution over `S` of a finite system of
polynomial equations: the unknowns are the coefficients of `G` and `H`, and the equations say that
the two sides have the same coefficients.

The ring of that system — the coordinate ring of the *scheme of factorizations* — is a quotient of
a polynomial ring over `A` in the unknown coefficients, and its key property is that it is
**integral** over `A`: the coefficients of a monic factor of a monic polynomial are integral over
the coefficients of the polynomial.  So the equations obtained by eliminating the unknowns — the
kernel of `A → (the coordinate ring)` — cut out exactly the parameter values at which a
factorization exists, provided one is allowed to look for the factorization over an algebraically
closed field.

## Main results

* `Rigidity.RET.Transfer.factorIdeal` — the ideal of `A` obtained by eliminating the unknowns.
* `Rigidity.RET.Transfer.factorIdeal_le_ker` — a factorization over `S` forces every eliminated
  equation to hold there.
* `Rigidity.RET.Transfer.exists_factorization_of_factorIdeal_le_ker` — conversely, over an
  algebraically closed field, the eliminated equations produce a factorization.
-/

open Polynomial

open scoped Polynomial.Bivariate

namespace Rigidity.RET.Transfer

attribute [local instance] Polynomial.algebra

/-! ## Generic polynomials

Two elementary constructions: a polynomial of degree at most `E` with prescribed coefficients, and
a monic polynomial of degree `d` with prescribed lower coefficients. -/

section Generic

variable {S T : Type*} [CommRing S] [CommRing T]

/-- The polynomial of degree at most `E` with prescribed coefficients. -/
noncomputable def coeffPoly (E : ℕ) (c : Fin (E + 1) → S) : S[X] :=
  ∑ j : Fin (E + 1), C (c j) * X ^ (j : ℕ)

theorem coeff_coeffPoly (E : ℕ) (c : Fin (E + 1) → S) (n : ℕ) :
    (coeffPoly E c).coeff n = if h : n < E + 1 then c ⟨n, h⟩ else 0 := by
  simp only [coeffPoly, finset_sum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨n, h⟩ : Fin (E + 1))]
    · simp
    · exact fun b _ hb => if_neg fun hh => hb (Fin.ext hh.symm)
    · simp
  · refine Finset.sum_eq_zero fun b _ => if_neg fun hh => ?_
    have := b.isLt
    omega

theorem coeffPoly_map (E : ℕ) (c : Fin (E + 1) → S) (φ : S →+* T) :
    (coeffPoly E c).map φ = coeffPoly E fun j => φ (c j) := by
  ext n
  rw [coeff_map, coeff_coeffPoly, coeff_coeffPoly]
  split_ifs with h
  · rfl
  · exact map_zero φ

/-- **A polynomial of degree at most `E` is the generic one, at its own coefficients.** -/
theorem coeffPoly_coeff (E : ℕ) (p : S[X]) (hp : p.natDegree ≤ E) :
    (coeffPoly E fun j : Fin (E + 1) => p.coeff j) = p := by
  ext n
  rw [coeff_coeffPoly]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- The monic polynomial of degree `d` with prescribed lower coefficients. -/
noncomputable def genericMonic (d : ℕ) (c : Fin d → S) : S[X] :=
  (freeMonic S d).map (MvPolynomial.aeval c).toRingHom

theorem coeff_genericMonic (d : ℕ) (c : Fin d → S) (n : ℕ) :
    (genericMonic d c).coeff n = if h : n < d then c ⟨n, h⟩ else if n = d then 1 else 0 := by
  simp only [genericMonic, coeff_map, coeff_freeMonic, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    apply_dite (MvPolynomial.aeval c), apply_ite (MvPolynomial.aeval c), MvPolynomial.aeval_X,
    map_one, map_zero]

theorem genericMonic_monic (d : ℕ) (c : Fin d → S) : (genericMonic d c).Monic :=
  (monic_freeMonic S d).map _

theorem natDegree_genericMonic [Nontrivial S] (d : ℕ) (c : Fin d → S) :
    (genericMonic d c).natDegree = d := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.2 fun n hn => ?_) ?_
  · rw [coeff_genericMonic, dif_neg (by omega), if_neg (by omega)]
  · rw [coeff_genericMonic, dif_neg (lt_irrefl d), if_pos rfl]
    exact one_ne_zero

theorem genericMonic_map (d : ℕ) (c : Fin d → S) (φ : S →+* T) :
    (genericMonic d c).map φ = genericMonic d fun i => φ (c i) := by
  ext n
  rw [coeff_map, coeff_genericMonic, coeff_genericMonic]
  split_ifs
  · rfl
  · exact map_one φ
  · exact map_zero φ

/-- **A monic polynomial of degree `d` is the generic one, at its own coefficients.** -/
theorem genericMonic_coeff (d : ℕ) (p : S[X]) (hp : p.Monic) (hd : p.natDegree = d) :
    (genericMonic d fun i : Fin d => p.coeff i) = p := by
  ext n
  rw [coeff_genericMonic]
  split_ifs with h₁ h₂
  · rfl
  · rw [← hd] at h₂
    rw [h₂, ← hp.leadingCoeff]
    rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Generic

/-! ## The scheme of factorizations -/

section Scheme

variable {A : Type*} [CommRing A]

/-- The unknowns: the coefficient of `X ^ j` in the coefficient of `Y ^ i` of one of the two
factors. -/
abbrev FactorVars (E m l : ℕ) : Type := (Fin m ⊕ Fin l) × Fin (E + 1)

/-- The ring of parameters extended by the unknown coefficients of the two factors. -/
abbrev FactorPoly (A : Type*) [CommRing A] (E m l : ℕ) := MvPolynomial (FactorVars E m l) A

/-- The generic monic factor of degree `d`, with unknown coefficients indexed through `ι`. -/
noncomputable def genFactor (A : Type*) [CommRing A] (E m l d : ℕ) (ι : Fin d → Fin m ⊕ Fin l) :
    (FactorPoly A E m l)[X][Y] :=
  genericMonic d fun i => coeffPoly E fun j => MvPolynomial.X (ι i, j)

theorem genFactor_monic (E m l d : ℕ) (ι : Fin d → Fin m ⊕ Fin l) :
    (genFactor A E m l d ι).Monic :=
  genericMonic_monic _ _

theorem coeff_coeff_genFactor (E m l d : ℕ) (ι : Fin d → Fin m ⊕ Fin l) {i j : ℕ}
    (hi : i < d) (hj : j < E + 1) :
    ((genFactor A E m l d ι).coeff i).coeff j = MvPolynomial.X (ι ⟨i, hi⟩, ⟨j, hj⟩) := by
  rw [genFactor, coeff_genericMonic, dif_pos hi, coeff_coeffPoly, dif_pos hj]

/-- The generic factorization, mapped into an arbitrary ring by a valuation of the unknowns. -/
theorem genFactor_map (E m l d : ℕ) (ι : Fin d → Fin m ⊕ Fin l) {S : Type*} [CommRing S]
    (θ : FactorPoly A E m l →+* S) :
    (genFactor A E m l d ι).map (mapRingHom θ) =
      genericMonic d fun i => coeffPoly E fun j => θ (MvPolynomial.X (ι i, j)) := by
  rw [genFactor, genericMonic_map]
  simp only [coe_mapRingHom, coeffPoly_map]

/-- The relations satisfied by the coefficients of a factorization: the two sides of
`F = G * H` have the same coefficients. -/
noncomputable def factorRel (E m l : ℕ) (F : A[X][Y]) : Ideal (FactorPoly A E m l) :=
  Ideal.span (Set.range fun p : ℕ × ℕ =>
    (((F.map (mapRingHom (MvPolynomial.C : A →+* FactorPoly A E m l)) -
      genFactor A E m l m Sum.inl * genFactor A E m l l Sum.inr).coeff p.1).coeff p.2))

/-- The coordinate ring of the scheme of factorizations of `F` into monic factors of degrees `m`
and `l`, whose coefficients have degree at most `E` in `X`. -/
abbrev FactorRing (E m l : ℕ) (F : A[X][Y]) := FactorPoly A E m l ⧸ factorRel E m l F

theorem algebraMap_factorRing (E m l : ℕ) (F : A[X][Y]) :
    algebraMap A (FactorRing E m l F) =
      (Ideal.Quotient.mk (factorRel E m l F)).comp
        (MvPolynomial.C : A →+* FactorPoly A E m l) := rfl

/-- **The generic factorization, over the coordinate ring of the scheme of factorizations.** -/
theorem map_eq_genFactor_mul (E m l : ℕ) (F : A[X][Y]) :
    F.map (mapRingHom (algebraMap A (FactorRing E m l F))) =
      (genFactor A E m l m Sum.inl).map
          (mapRingHom (Ideal.Quotient.mk (factorRel E m l F))) *
        (genFactor A E m l l Sum.inr).map
          (mapRingHom (Ideal.Quotient.mk (factorRel E m l F))) := by
  have hz : (F.map (mapRingHom (MvPolynomial.C : A →+* FactorPoly A E m l)) -
      genFactor A E m l m Sum.inl * genFactor A E m l l Sum.inr).map
      (mapRingHom (Ideal.Quotient.mk (factorRel E m l F))) = 0 := by
    ext i j
    simp only [coeff_map, coe_mapRingHom, coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(i, j), rfl⟩)
  rw [Polynomial.map_sub, Polynomial.map_mul, sub_eq_zero] at hz
  rw [← hz, Polynomial.map_map, mapRingHom_comp, algebraMap_factorRing]

end Scheme

/-! ## The two directions -/

section Directions

variable {A : Type*} [CommRing A]

/-- The equations on the parameters obtained by eliminating the coefficients of the two factors. -/
noncomputable def factorIdeal (E m l : ℕ) (F : A[X][Y]) : Ideal A :=
  RingHom.ker (algebraMap A (FactorRing E m l F))

/-- **A factorization forces the eliminated equations.**

A factorization of `F` over `S` is a valuation of the unknowns satisfying the relations, hence a
homomorphism from the coordinate ring of the scheme of factorizations to `S`, through which the
map from the parameters factors. -/
theorem factorIdeal_le_ker {S : Type*} [CommRing S] (E m l : ℕ) (F : A[X][Y]) (φ : A →+* S)
    {G H : S[X][Y]} (hG : G.Monic) (hH : H.Monic) (hGd : G.natDegree = m) (hHd : H.natDegree = l)
    (hGE : ∀ i, (G.coeff i).natDegree ≤ E) (hHE : ∀ i, (H.coeff i).natDegree ≤ E)
    (hF : F.map (mapRingHom φ) = G * H) :
    factorIdeal E m l F ≤ RingHom.ker φ := by
  classical
  set v : FactorVars E m l → S := fun t =>
    Sum.elim (fun i : Fin m => (G.coeff i).coeff t.2) (fun i : Fin l => (H.coeff i).coeff t.2) t.1
    with hv
  set θ : FactorPoly A E m l →+* S := MvPolynomial.eval₂Hom φ v with hθ
  have hθC : θ.comp (MvPolynomial.C : A →+* FactorPoly A E m l) = φ := by
    ext a
    simp [hθ]
  have hgen₁ : (genFactor A E m l m Sum.inl).map (mapRingHom θ) = G := by
    rw [genFactor_map]
    have : ∀ i : Fin m, (coeffPoly E fun j => θ (MvPolynomial.X ((Sum.inl i : Fin m ⊕ Fin l), j)))
        = G.coeff i := by
      intro i
      have : ∀ j : Fin (E + 1),
          θ (MvPolynomial.X ((Sum.inl i : Fin m ⊕ Fin l), j)) = (G.coeff i).coeff j := by
        intro j
        simp [hθ, hv]
      simp only [this]
      exact coeffPoly_coeff E _ (hGE i)
    simp only [this]
    exact genericMonic_coeff m G hG hGd
  have hgen₂ : (genFactor A E m l l Sum.inr).map (mapRingHom θ) = H := by
    rw [genFactor_map]
    have : ∀ i : Fin l, (coeffPoly E fun j => θ (MvPolynomial.X ((Sum.inr i : Fin m ⊕ Fin l), j)))
        = H.coeff i := by
      intro i
      have : ∀ j : Fin (E + 1),
          θ (MvPolynomial.X ((Sum.inr i : Fin m ⊕ Fin l), j)) = (H.coeff i).coeff j := by
        intro j
        simp [hθ, hv]
      simp only [this]
      exact coeffPoly_coeff E _ (hHE i)
    simp only [this]
    exact genericMonic_coeff l H hH hHd
  have hzero : (F.map (mapRingHom (MvPolynomial.C : A →+* FactorPoly A E m l)) -
      genFactor A E m l m Sum.inl * genFactor A E m l l Sum.inr).map (mapRingHom θ) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hgen₁, hgen₂, Polynomial.map_map,
      mapRingHom_comp, hθC, hF, sub_self]
  have hrel : factorRel E m l F ≤ RingHom.ker θ := by
    rw [factorRel, Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    have h2 := congrArg (fun q : S[X][Y] => (q.coeff p.1).coeff p.2) hzero
    simp only [coeff_map, coe_mapRingHom, coeff_zero] at h2
    simpa only [SetLike.mem_coe, RingHom.mem_ker] using h2
  let ψ : FactorRing E m l F →+* S := Ideal.Quotient.lift _ θ fun x hx => hrel hx
  have hψ : ψ.comp (algebraMap A (FactorRing E m l F)) = φ := by
    rw [algebraMap_factorRing, ← RingHom.comp_assoc, ← hθC]
    congr 1
  intro a ha
  have ha' : algebraMap A (FactorRing E m l F) a = 0 := by
    simpa only [factorIdeal, RingHom.mem_ker] using ha
  rw [RingHom.mem_ker, ← hψ, RingHom.comp_apply, ha', map_zero]

/-- **The coefficients of a monic factor of a monic two-variable polynomial are integral over the
coefficients of the polynomial.** -/
theorem isIntegral_coeff_coeff_of_dvd {B : Type*} [CommRing B] [Algebra A B]
    (F : A[X][Y]) (hF : F.Monic) (G : B[X][Y]) (hG : G.Monic)
    (hdvd : G ∣ F.map (mapRingHom (algebraMap A B))) (i j : ℕ) :
    IsIntegral A ((G.coeff i).coeff j) := by
  have h1 : IsIntegral (A[X]) (G.coeff i) := by
    refine isIntegral_coeff_of_dvd F G hF hG ?_ i
    rwa [Polynomial.algebraMap_def]
  exact h1.coeff j

private theorem isIntegral_var (E m l : ℕ) (F : A[X][Y]) (hF : F.Monic) (d : ℕ)
    (ι : Fin d → Fin m ⊕ Fin l)
    (hdvd : (genFactor A E m l d ι).map (mapRingHom (Ideal.Quotient.mk (factorRel E m l F))) ∣
      F.map (mapRingHom (algebraMap A (FactorRing E m l F))))
    (i : Fin d) (j : Fin (E + 1)) :
    IsIntegral A ((Ideal.Quotient.mk (factorRel E m l F)) (MvPolynomial.X (ι i, j))) := by
  have h2 := isIntegral_coeff_coeff_of_dvd F hF _ ((genFactor_monic E m l d ι).map _) hdvd i j
  have h3 : ((((genFactor A E m l d ι).map
        (mapRingHom (Ideal.Quotient.mk (factorRel E m l F)))).coeff i).coeff j) =
      (Ideal.Quotient.mk (factorRel E m l F)) (MvPolynomial.X (ι i, j)) := by
    rw [coeff_map, coe_mapRingHom, coeff_map,
      coeff_coeff_genFactor E m l d ι i.isLt j.isLt, Fin.eta, Fin.eta]
  rwa [h3] at h2

/-- **The coordinate ring of the scheme of factorizations is integral over the parameters.**

The coefficients of a monic factor of a monic polynomial are integral over the coefficients of the
polynomial, and being integral is inherited by the coefficients in the second variable. -/
theorem isIntegral_factorRing (E m l : ℕ) (F : A[X][Y]) (hF : F.Monic) :
    Algebra.IsIntegral A (FactorRing E m l F) := by
  have hmul := map_eq_genFactor_mul E m l F
  have hvar : ∀ t : FactorVars E m l,
      IsIntegral A ((Ideal.Quotient.mk (factorRel E m l F)) (MvPolynomial.X t)) := by
    rintro ⟨i | i, j⟩
    · exact isIntegral_var E m l F hF m Sum.inl ⟨_, hmul⟩ i j
    · exact isIntegral_var E m l F hF l Sum.inr ⟨_, hmul.trans (mul_comm _ _)⟩ i j
  constructor
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a => exact isIntegral_algebraMap
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p t hp => rw [map_mul]; exact hp.mul (hvar t)

/-- **Over an algebraically closed field, the eliminated equations produce a factorization.**

A homomorphism from the parameters which kills the eliminated equations extends, along the
integral extension, to the coordinate ring of the scheme of factorizations; the image of the
generic factorization is the factorization sought. -/
theorem exists_factorization_of_factorIdeal_le_ker {S : Type*} [Field S] [IsAlgClosed S]
    (E m l : ℕ) (F : A[X][Y]) (hF : F.Monic) (φ : A →+* S)
    (hker : factorIdeal E m l F ≤ RingHom.ker φ) :
    ∃ G H : S[X][Y], G.Monic ∧ H.Monic ∧ G.natDegree = m ∧ H.natDegree = l ∧
      F.map (mapRingHom φ) = G * H := by
  haveI := isIntegral_factorRing E m l F hF
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_isIntegral (A := A) (B := FactorRing E m l F) φ hker
  refine ⟨(genFactor A E m l m Sum.inl).map (mapRingHom (ψ.comp
      (Ideal.Quotient.mk (factorRel E m l F)))),
    (genFactor A E m l l Sum.inr).map (mapRingHom (ψ.comp
      (Ideal.Quotient.mk (factorRel E m l F)))),
    (genFactor_monic E m l m Sum.inl).map _, (genFactor_monic E m l l Sum.inr).map _, ?_, ?_, ?_⟩
  · rw [genFactor_map]
    exact natDegree_genericMonic _ _
  · rw [genFactor_map]
    exact natDegree_genericMonic _ _
  · have := congrArg (fun p : (FactorRing E m l F)[X][Y] => p.map (mapRingHom ψ))
      (map_eq_genFactor_mul E m l F)
    simp only [Polynomial.map_mul, Polynomial.map_map, mapRingHom_comp] at this
    rw [← this, ← hψ]

end Directions

end Rigidity.RET.Transfer
