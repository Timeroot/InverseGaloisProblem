/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.DeckClear
import InverseGalois.Rigidity.RET.Local.PuiseuxAssembly

/-!
# Root formulas over the constant field

The automorphisms of a cover of the line are formulas in a primitive element: a polynomial
numerator over a common denominator, both with coefficients in the coordinate ring of the line.
Over the complex numbers those formulas were already packaged as a group acting on the roots of
the complexified equation.  What that packaging forgets is the algebra it came from: which element
of the cover each formula computes.

`DeckData` keeps both halves together.  It records the numerators and the denominator over the
constant field, the identities they satisfy — carrying roots to roots, the identity element, the
composition law, the separation of two automorphisms and of the equation from its derivative — and
the one extra fact that the complex packaging drops: evaluating the formula of an automorphism at
the primitive element returns that automorphism applied to the primitive element, up to the
denominator.  Extending the coefficients to the complex numbers then produces the analytic
packaging, with the numerators and denominator visible.

## Main definitions

* `Rigidity.RET.DeckData` — root formulas over the constant field, with their algebraic meaning.
* `Rigidity.RET.DeckData.toIntegralDeck` — the complexified formulas, as a group of root formulas.

## Main results

* `Rigidity.RET.map_scaledComp_of_natDegree` — the cleared substitution commutes with extension of
  the coefficients.
* `Rigidity.RET.exists_deckData` — a cover of the line has such a group of formulas.
* `Rigidity.RET.natDegree_complexEquation` — extending the coefficients preserves the degree of the
  equation.
* `Rigidity.RET.DeckData.separable_spec` — outside the exceptional parameters the complexified
  equation is separable.
-/

open Polynomial GeomAKLB

noncomputable section

namespace Rigidity.RET

/-! ### Extending the coefficients of a cleared substitution -/

/-- **The cleared substitution commutes with extension of the coefficients**, as soon as the degree
of the polynomial being substituted into is unchanged. -/
theorem map_scaledComp_of_natDegree {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (P N : Polynomial R) (d : R) (h : (P.map f).natDegree = P.natDegree) :
    (scaledComp P N d).map f = scaledComp (P.map f) (N.map f) (f d) := by
  simp only [scaledComp, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow,
    map_mul, map_pow, coeff_map, h]

/-! ### Root formulas over the constant field -/

variable {Ω : Type} [Field Ω] [Algebra (RatFunc k) Ω] [Algebra (Polynomial k) Ω]
  [IsScalarTower (Polynomial k) (RatFunc k) Ω]

/-- **A group of root formulas over the constant field, with their algebraic meaning.**

The numerators `num g` and the common denominator `den` describe the automorphism `g⁻¹` as the
formula `num g / den` in the primitive element; `bad` collects the parameters at which any of the
identities they satisfy may fail. -/
structure DeckData (α : Ω) where
  /-- the primitive element is integral over the coordinate ring. -/
  integral : IsIntegral (Polynomial k) α
  /-- the numerator of the formula of a group element. -/
  num : (Ω ≃ₐ[RatFunc k] Ω) → Polynomial (Polynomial k)
  /-- the common denominator of all the formulas. -/
  den : Polynomial k
  /-- the parameters at which the identities may fail. -/
  bad : Polynomial k
  /-- the exceptional element is not identically zero. -/
  bad_ne : bad ≠ 0
  /-- the denominator only vanishes where the exceptional element does. -/
  den_dvd : den ∣ bad
  /-- the formula of a group element computes that group element. -/
  aeval_num : ∀ g : Ω ≃ₐ[RatFunc k] Ω,
    aeval α ((num g).map (algebraMap (Polynomial k) (RatFunc k)))
      = algebraMap (RatFunc k) Ω (algebraMap (Polynomial k) (RatFunc k) den) * g⁻¹ α
  /-- the formulas carry roots of the equation to roots of the equation. -/
  dvd_root : ∀ g : Ω ≃ₐ[RatFunc k] Ω,
    minpoly (Polynomial k) α ∣ scaledComp (minpoly (Polynomial k) α) (num g) den
  /-- the formula of the identity is the identity. -/
  dvd_one : minpoly (Polynomial k) α ∣ num 1 - C den * X
  /-- composing two formulas gives the formula of the product. -/
  dvd_mul : ∀ g h : Ω ≃ₐ[RatFunc k] Ω, minpoly (Polynomial k) α ∣
    scaledComp (num g) (num h) den - C (den ^ (num g).natDegree) * num (g * h)
  /-- different group elements move a root to different places. -/
  sep : ∀ g h : Ω ≃ₐ[RatFunc k] Ω, g ≠ h → ∃ A B : Polynomial (Polynomial k),
    A * minpoly (Polynomial k) α + B * (num g - num h) = C bad
  /-- the equation is separated from its derivative. -/
  sepDeriv : ∃ A B : Polynomial (Polynomial k),
    A * minpoly (Polynomial k) α
      + B * derivative (minpoly (Polynomial k) α) = C bad

/-- **A cover of the line carries a group of root formulas over the constant field.** -/
theorem exists_deckData [Finite (Ω ≃ₐ[RatFunc k] Ω)] {α : Ω}
    (hα : IsIntegral (Polynomial k) α)
    (hgen : ∀ β : Ω, ∃ q : Polynomial (RatFunc k), aeval α q = β) :
    Nonempty (DeckData α) := by
  have hmap : (minpoly (Polynomial k) α).map (algebraMap (Polynomial k) (RatFunc k))
      = minpoly (RatFunc k) α :=
    (minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc k) hα).symm
  have hirr : Irreducible ((minpoly (Polynomial k) α).map
      (algebraMap (Polynomial k) (RatFunc k))) := by
    rw [hmap]; exact minpoly.irreducible hα.tower_top
  have hzero : aeval α ((minpoly (Polynomial k) α).map
      (algebraMap (Polynomial k) (RatFunc k))) = 0 := by
    rw [hmap]; exact minpoly.aeval _ _
  obtain ⟨num, den, bad, hbad, hdvdden, hform, hroot, hone, hmul, hsepp, As, Bs, hids⟩ :=
    exists_deck_formulas (minpoly.monic hα) hirr hirr.separable hzero hgen
  exact ⟨{ integral := hα
           num := num
           den := den
           bad := bad
           bad_ne := hbad
           den_dvd := hdvdden
           aeval_num := hform
           dvd_root := hroot
           dvd_one := hone
           dvd_mul := hmul
           sep := hsepp
           sepDeriv := ⟨As, Bs, hids⟩ }⟩

/-! ### The complexified formulas -/

section Complex

variable [Algebra k ℂ]

/-- Extending the coefficients of a polynomial over the coordinate ring of the line to the complex
numbers loses nothing. -/
theorem injective_mapRingHom :
    Function.Injective (Polynomial.mapRingHom (algebraMap k ℂ) : Polynomial k →+* Polynomial ℂ) :=
  Polynomial.map_injective _ (algebraMap k ℂ).injective

omit [Algebra (RatFunc k) Ω] [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **Extending the coefficients preserves the degree of the equation of the cover.** -/
theorem natDegree_complexEquation (α : Ω) :
    (complexEquation α).natDegree = (minpoly (Polynomial k) α).natDegree :=
  natDegree_map_eq_of_injective injective_mapRingHom _

namespace DeckData

variable {α : Ω} (D : DeckData α)

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem bad_map_ne : D.bad.map (algebraMap k ℂ) ≠ 0 :=
  fun h => D.bad_ne (Polynomial.map_injective _ (algebraMap k ℂ).injective (by simpa using h))

/-- **The exceptional parameters of the complexified formulas.** -/
def badSetC : Finset ℂ := Analytic.badSet (D.bad.map (algebraMap k ℂ))

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
theorem eval_ne_zero_of_notMem {c : Polynomial k} (hc : c ∣ D.bad) {z : ℂ}
    (hz : z ∉ (D.badSetC : Set ℂ)) : (c.map (algebraMap k ℂ)).eval z ≠ 0 :=
  Analytic.eval_ne_zero_of_notMem_badSet D.bad_map_ne (Polynomial.map_dvd _ hc) hz

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
/-- **Outside the exceptional parameters the complexified equation is separable.** -/
theorem separable_spec {z : ℂ} (hz : z ∉ (D.badSetC : Set ℂ)) :
    (Analytic.spec (complexEquation α) z).Separable := by
  obtain ⟨A, B, hAB⟩ := D.sepDeriv
  refine Analytic.separable_spec_of_bezout (A := A.map (Polynomial.mapRingHom (algebraMap k ℂ)))
    (B := B.map (Polynomial.mapRingHom (algebraMap k ℂ))) ?_
    (D.eval_ne_zero_of_notMem dvd_rfl hz)
  have h := congrArg (Polynomial.map (Polynomial.mapRingHom (algebraMap k ℂ))) hAB
  rwa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, map_C,
    ← Polynomial.derivative_map] at h

/-- **The complexified formulas, as a group of root formulas.** -/
def toIntegralDeck :
    Analytic.IntegralDeck (complexEquation α) D.badSetC (Ω ≃ₐ[RatFunc k] Ω) where
  num g := (D.num g).map (Polynomial.mapRingHom (algebraMap k ℂ))
  den := D.den.map (algebraMap k ℂ)
  den_ne _ hz := D.eval_ne_zero_of_notMem D.den_dvd hz
  dvd_root g := by
    have h := Polynomial.map_dvd (Polynomial.mapRingHom (algebraMap k ℂ)) (D.dvd_root g)
    rw [map_scaledComp_of_natDegree _ _ _ _ (natDegree_complexEquation α)] at h
    exact h
  dvd_one := by
    have h := Polynomial.map_dvd (Polynomial.mapRingHom (algebraMap k ℂ)) D.dvd_one
    rwa [Polynomial.map_sub, Polynomial.map_mul, map_C, Polynomial.map_X] at h
  dvd_mul g h := by
    have hd : ((D.num g).map (Polynomial.mapRingHom (algebraMap k ℂ))).natDegree
        = (D.num g).natDegree :=
      natDegree_map_eq_of_injective injective_mapRingHom _
    have hh := Polynomial.map_dvd (Polynomial.mapRingHom (algebraMap k ℂ)) (D.dvd_mul g h)
    rw [Polynomial.map_sub, map_scaledComp_of_natDegree _ _ _ _ hd, Polynomial.map_mul, map_C,
      map_pow] at hh
    rw [hd]
    exact hh
  sep g h hgh := by
    obtain ⟨A, B, hAB⟩ := D.sep g h hgh
    refine ⟨A.map (Polynomial.mapRingHom (algebraMap k ℂ)),
      B.map (Polynomial.mapRingHom (algebraMap k ℂ)), D.bad.map (algebraMap k ℂ),
      fun _ hz => D.eval_ne_zero_of_notMem dvd_rfl hz, ?_⟩
    have h := congrArg (Polynomial.map (Polynomial.mapRingHom (algebraMap k ℂ))) hAB
    rwa [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub,
      map_C] at h

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
@[simp] theorem num_toIntegralDeck (g : Ω ≃ₐ[RatFunc k] Ω) :
    D.toIntegralDeck.num g = (D.num g).map (Polynomial.mapRingHom (algebraMap k ℂ)) := rfl

omit [IsScalarTower (Polynomial k) (RatFunc k) Ω] in
@[simp] theorem den_toIntegralDeck :
    D.toIntegralDeck.den = D.den.map (algebraMap k ℂ) := rfl

end DeckData

end Complex

end Rigidity.RET

end
