/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Transfer.FactorScheme

/-!
# Generic polynomials in two variables

A polynomial in two variables, of degree at most `N` in the outer variable and at most `D` in the
inner one, is a linear expression in its `(N + 1) * (D + 1)` coefficients; if it is monic of degree
`d` in the outer variable, only the `d * (D + 1)` lower coefficients are free.  The two generic
shapes are recorded here, together with the two facts that make them useful: they commute with a
map of the coefficient ring, and they reproduce a given polynomial when fed its own coefficients.

The point of the monic shape is that it is monic of the prescribed degree *whatever* the
coefficients are, so both the degree and the leading coefficient survive a specialization of the
coefficients — which is exactly what the operations `%ₘ` and `scaleRoots` need.

## Main results

* `Rigidity.RET.Transfer.biPoly_map`, `Rigidity.RET.Transfer.biMonic_map` — the generic shapes
  commute with a map of the coefficient ring.
* `Rigidity.RET.Transfer.biPoly_coeff`, `Rigidity.RET.Transfer.biMonic_coeff` — a polynomial of
  the prescribed shape is the generic one at its own coefficients.
* `Rigidity.RET.Transfer.map_eq_zero_iff_coeff` — a polynomial in two variables dies under a map
  of the coefficient ring exactly when each of its coefficients does.
-/

open Polynomial

namespace Rigidity.RET.Transfer

section BiGeneric

variable {R T : Type*} [CommRing R] [CommRing T]

/-- The polynomial in two variables of degree at most `N` in the outer variable and at most `D` in
the inner one, with prescribed coefficients. -/
noncomputable def biPoly (N D : ℕ) (c : Fin (N + 1) → Fin (D + 1) → R) :
    Polynomial (Polynomial R) :=
  coeffPoly N fun i => coeffPoly D (c i)

/-- The polynomial in two variables monic of degree `d` in the outer variable and of degree at most
`D` in the inner one, with prescribed lower coefficients. -/
noncomputable def biMonic (d D : ℕ) (c : Fin d → Fin (D + 1) → R) :
    Polynomial (Polynomial R) :=
  genericMonic d fun i => coeffPoly D (c i)

theorem natDegree_coeffPoly_le (D : ℕ) (c : Fin (D + 1) → R) : (coeffPoly D c).natDegree ≤ D :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hn => by rw [coeff_coeffPoly, dif_neg (by omega)]

theorem biPoly_map (N D : ℕ) (c : Fin (N + 1) → Fin (D + 1) → R) (φ : R →+* T) :
    (biPoly N D c).map (mapRingHom φ) = biPoly N D fun i j => φ (c i j) := by
  simp only [biPoly, coeffPoly_map, coe_mapRingHom]

theorem biMonic_map (d D : ℕ) (c : Fin d → Fin (D + 1) → R) (φ : R →+* T) :
    (biMonic d D c).map (mapRingHom φ) = biMonic d D fun i j => φ (c i j) := by
  simp only [biMonic, genericMonic_map, coeffPoly_map, coe_mapRingHom]

/-- **A polynomial of the prescribed degrees is the generic one, at its own coefficients.** -/
theorem biPoly_coeff (N D : ℕ) (p : Polynomial (Polynomial R)) (hN : p.natDegree ≤ N)
    (hD : ∀ i, (p.coeff i).natDegree ≤ D) :
    (biPoly N D fun i j => (p.coeff i).coeff j) = p := by
  rw [biPoly, show (fun i : Fin (N + 1) => coeffPoly D fun j : Fin (D + 1) => (p.coeff i).coeff j)
    = fun i : Fin (N + 1) => p.coeff i from funext fun i => coeffPoly_coeff D _ (hD i)]
  exact coeffPoly_coeff N p hN

/-- **A polynomial monic of the prescribed degree is the generic monic one, at its own
coefficients.** -/
theorem biMonic_coeff (d D : ℕ) (p : Polynomial (Polynomial R)) (hp : p.Monic)
    (hd : p.natDegree = d) (hD : ∀ i, (p.coeff i).natDegree ≤ D) :
    (biMonic d D fun i j => (p.coeff i).coeff j) = p := by
  rw [biMonic, show (fun i : Fin d => coeffPoly D fun j : Fin (D + 1) => (p.coeff i).coeff j)
    = fun i : Fin d => p.coeff i from funext fun i => coeffPoly_coeff D _ (hD i)]
  exact genericMonic_coeff d p hp hd

theorem coeff_coeff_biPoly (N D : ℕ) (c : Fin (N + 1) → Fin (D + 1) → R) (i : Fin (N + 1))
    (j : Fin (D + 1)) : ((biPoly N D c).coeff i).coeff j = c i j := by
  simp only [biPoly, coeff_coeffPoly, i.isLt, j.isLt, dif_pos, Fin.eta]

theorem coeff_map_bi (ψ : R →+* T) (p : Polynomial (Polynomial R)) (i : ℕ) :
    (p.map (mapRingHom ψ)).coeff i = (p.coeff i).map ψ := by
  rw [coeff_map, coe_mapRingHom]

theorem biMonic_monic (d D : ℕ) (c : Fin d → Fin (D + 1) → R) : (biMonic d D c).Monic :=
  genericMonic_monic _ _

theorem natDegree_biMonic [Nontrivial R] (d D : ℕ) (c : Fin d → Fin (D + 1) → R) :
    (biMonic d D c).natDegree = d :=
  natDegree_genericMonic _ _

theorem natDegree_coeff_biMonic_le (d D : ℕ) (c : Fin d → Fin (D + 1) → R) (i : ℕ) :
    ((biMonic d D c).coeff i).natDegree ≤ D := by
  rw [biMonic, coeff_genericMonic]
  split_ifs
  · exact natDegree_coeffPoly_le _ _
  · simp
  · simp

/-- **The generic monic shape satisfies the weight bound.**

Every coefficient has degree at most `D` in the inner variable, and the coefficient in the leading
degree is a constant. -/
theorem weight_bound_biMonic [Nontrivial R] (d D : ℕ) (c : Fin d → Fin (D + 1) → R) (i : ℕ)
    (hi : (biMonic d D c).coeff i ≠ 0) :
    ((biMonic d D c).coeff i).natDegree + D * i ≤ D * (biMonic d D c).natDegree := by
  rw [natDegree_biMonic]
  have hle : i ≤ d := by
    by_contra h
    exact hi (coeff_eq_zero_of_natDegree_lt (by rw [natDegree_biMonic]; omega))
  rcases eq_or_lt_of_le hle with h | h
  · subst h
    rw [biMonic, coeff_genericMonic, dif_neg (lt_irrefl _), if_pos rfl, natDegree_one, zero_add]
  · calc ((biMonic d D c).coeff i).natDegree + D * i
        ≤ D + D * i := Nat.add_le_add_right (natDegree_coeff_biMonic_le d D c i) _
      _ = D * (i + 1) := by ring
      _ ≤ D * d := Nat.mul_le_mul_left D h

/-- **A polynomial in two variables dies under a map of the coefficient ring exactly when each of
its coefficients does.** -/
theorem map_eq_zero_iff_coeff (φ : R →+* T) (E : Polynomial (Polynomial R)) :
    E.map (mapRingHom φ) = 0 ↔ ∀ i j, φ ((E.coeff i).coeff j) = 0 := by
  constructor
  · intro h i j
    have hz : ((E.map (mapRingHom φ)).coeff i).coeff j = 0 := by rw [h, coeff_zero, coeff_zero]
    rwa [coeff_map, coe_mapRingHom, coeff_map] at hz
  · refine fun h => Polynomial.ext fun i => Polynomial.ext fun j => ?_
    rw [coeff_map, coe_mapRingHom, coeff_map, h i j, coeff_zero, coeff_zero]

/-- A bound on the degrees, in the inner variable, of the coefficients of a polynomial in two
variables. -/
noncomputable def biBound (p : Polynomial (Polynomial R)) : ℕ :=
  (Finset.range (p.natDegree + 1)).sup fun i => (p.coeff i).natDegree

theorem natDegree_coeff_le_biBound (p : Polynomial (Polynomial R)) (i : ℕ) :
    (p.coeff i).natDegree ≤ biBound p := by
  by_cases h : i < p.natDegree + 1
  · exact Finset.le_sup (f := fun i => (p.coeff i).natDegree) (Finset.mem_range.2 h)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), natDegree_zero]
    exact Nat.zero_le _

end BiGeneric

/-! ## Pushing the shapes of a presentation through a map of the coefficients

The operations `%ₘ`, `scaleRoots` and `comp` commute with a map of the coefficient ring as soon as
the polynomials they divide by, respectively scale, are monic. -/

section Push

variable {R T : Type*} [CommRing R] [CommRing T] [Nontrivial T] (ψ : R →+* T)

/-- **The shape of the equation satisfied by a scaled root.** -/
theorem push_root {P S Q : Polynomial (Polynomial R)} (hP : P.Monic) (hS : S.Monic)
    (u : Polynomial R) :
    (((S.scaleRoots u).comp Q) %ₘ P).map (mapRingHom ψ)
      = (((S.map (mapRingHom ψ)).scaleRoots (u.map ψ)).comp (Q.map (mapRingHom ψ)))
          %ₘ (P.map (mapRingHom ψ)) := by
  rw [Polynomial.map_modByMonic _ hP, Polynomial.map_comp,
    Polynomial.map_scaleRoots _ _ _ (by rw [hS.leadingCoeff, map_one]; exact one_ne_zero),
    coe_mapRingHom]

/-- **The shape of the composition law of the deck transformations.** -/
theorem push_mul {P S Q W : Polynomial (Polynomial R)} (hP : P.Monic) (hS : S.Monic)
    (u : Polynomial R) (m : ℕ) :
    ((((S.scaleRoots u).comp Q) - C u ^ m * W) %ₘ P).map (mapRingHom ψ)
      = ((((S.map (mapRingHom ψ)).scaleRoots (u.map ψ)).comp (Q.map (mapRingHom ψ)))
          - C (u.map ψ) ^ m * (W.map (mapRingHom ψ))) %ₘ (P.map (mapRingHom ψ)) := by
  rw [Polynomial.map_modByMonic _ hP, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_scaleRoots _ _ _ (by rw [hS.leadingCoeff, map_one]; exact one_ne_zero),
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, coe_mapRingHom]

/-- **The shape of the equation writing the root back in terms of the second generator.** -/
theorem push_back {P S Q : Polynomial (Polynomial R)} (hP : P.Monic) (hS : S.Monic)
    (u v : Polynomial R) (m : ℕ) :
    ((((S.scaleRoots u).comp Q) - C (u ^ m * v) * X) %ₘ P).map (mapRingHom ψ)
      = ((((S.map (mapRingHom ψ)).scaleRoots (u.map ψ)).comp (Q.map (mapRingHom ψ)))
          - C ((u.map ψ) ^ m * (v.map ψ)) * X) %ₘ (P.map (mapRingHom ψ)) := by
  rw [Polynomial.map_modByMonic _ hP, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_scaleRoots _ _ _ (by rw [hS.leadingCoeff, map_one]; exact one_ne_zero),
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, Polynomial.map_mul,
    Polynomial.map_pow]

omit [Nontrivial T] in
/-- **The shape of the identity separating two images of the root.** -/
theorem push_sep {P A B S : Polynomial (Polynomial R)} (hP : P.Monic) (u : Polynomial R) :
    ((((A - B) * S) - C u) %ₘ P).map (mapRingHom ψ)
      = ((((A.map (mapRingHom ψ)) - (B.map (mapRingHom ψ))) * (S.map (mapRingHom ψ)))
          - C (u.map ψ)) %ₘ (P.map (mapRingHom ψ)) := by
  rw [Polynomial.map_modByMonic _ hP, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_C, coe_mapRingHom]

omit [Nontrivial T] in
/-- **The shape of the Bézout identity between the equation and its derivative.** -/
theorem push_bezout (P A B : Polynomial (Polynomial R)) (u : Polynomial R) :
    ((P * A + P.derivative * B - C u)).map (mapRingHom ψ)
      = (P.map (mapRingHom ψ)) * (A.map (mapRingHom ψ))
        + (P.map (mapRingHom ψ)).derivative * (B.map (mapRingHom ψ)) - C (u.map ψ) := by
  rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_C, coe_mapRingHom, derivative_map]

omit [Nontrivial T] in
/-- **The shape of the identity locating the common degeneracy.** -/
theorem push_locus (a b c d : Polynomial R) {r : ℕ} (tt : Fin r → R) (m : ℕ) :
    ((a * b + c * d - (∏ i, (X - C (tt i))) ^ m)).map ψ
      = (a.map ψ) * (b.map ψ) + (c.map ψ) * (d.map ψ)
        - (∏ i, (X - C (ψ (tt i)))) ^ m := by
  rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

end Push

/-! ## Transfer of an identity along a specialization -/

section Transfer

variable {k K : Type*} [Field k] [Field K] [Algebra k K] {σ : Type*}

/-- **A polynomial identity in two variables satisfied by the parameters is satisfied by any
specialization retaining their identities.** -/
theorem map_eq_zero_of_specialize {x : σ → K} {y : σ → k}
    (hy : ∀ p : MvPolynomial σ k, MvPolynomial.aeval x p = 0 → MvPolynomial.aeval y p = 0)
    (E : Polynomial (Polynomial (MvPolynomial σ k)))
    (h : E.map (mapRingHom (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom) = 0) :
    E.map (mapRingHom (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom) = 0 := by
  rw [map_eq_zero_iff_coeff] at h ⊢
  exact fun i j => hy _ (h i j)

/-- **A polynomial identity in one variable satisfied by the parameters is satisfied by any
specialization retaining their identities.** -/
theorem map_eq_zero_of_specialize₁ {x : σ → K} {y : σ → k}
    (hy : ∀ p : MvPolynomial σ k, MvPolynomial.aeval x p = 0 → MvPolynomial.aeval y p = 0)
    (e : Polynomial (MvPolynomial σ k))
    (h : e.map (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom = 0) :
    e.map (MvPolynomial.aeval y : MvPolynomial σ k →ₐ[k] k).toRingHom = 0 := by
  refine Polynomial.ext fun i => ?_
  rw [coeff_map, coeff_zero]
  refine hy _ ?_
  have hz : (e.map (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] K).toRingHom).coeff i = 0 := by
    rw [h, coeff_zero]
  rwa [coeff_map] at hz

end Transfer

end Rigidity.RET.Transfer
