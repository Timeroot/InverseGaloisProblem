/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNSqrtNegOne
import InverseGalois.CFT.Units.InflationDescent
import InverseGalois.CFT.Units.TowerCoboundary

/-!
# The Albert-Brauer-Hasse-Noether theorem with no condition at infinity

The Albert-Brauer-Hasse-Noether theorem for a two-cocycle with values in the units of the rational
numbers, killed by a nonzero integer, costs a hypothesis at the real place unless the extension
contains a square root of minus one.  This file removes that last hypothesis: a two-cocycle which is
a coboundary at every ramified finite place is a coboundary, whatever the extension.

A square root of minus one is adjoined.  A finite Galois extension of the rational numbers is the
splitting field of a polynomial, and multiplying that polynomial by `X ^ 2 + 1` produces a finite
Galois extension which contains both the original one and a square root of minus one.  The local
hypothesis is supplied at every place of the enlarged field, ramified or not: a place ramified over
the rational numbers in the enlarged field may well lie above an unramified place of the original
one, where the hypothesis is free, and the transport of a local coboundary up a tower carries it to
the place above.  In particular the place above two, which adjoining a square root of minus one
always ramifies, costs nothing.  The theorem over the enlarged field then trivialises the inflated
cocycle, and the trivialising one-cochain descends, because the enlarged field is Galois over the
original one and Hilbert's theorem ninety makes the one-cochain constant on the kernel of the
restriction map.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_pow_eq_one`: at an unramified finite place a
  two-cocycle with values in the units of the base field killed by a nonzero integer is a local
  coboundary.
* `InverseGalois.CFT.exists_isMulCoboundary_of_exists_sq_eq_neg_one`: the same conclusion for a
  cocycle inflated from a subextension of an extension containing a square root of minus one.
* `InverseGalois.CFT.exists_isMulCoboundary_of_forall_ramified`: **a two-cocycle with values in the
  units of the rational numbers, killed by a nonzero integer and a coboundary at every ramified
  finite place, is a coboundary.**

## Tags

number field, Albert-Brauer-Hasse-Noether, two-cocycle, coboundary, square root of minus one,
inflation, descent
-/

open IsDedekindDomain MulAction NumberField

open scoped Polynomial

namespace InverseGalois.CFT

/-! ### The places which cost nothing -/

section Unramified

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **At an unramified finite place the local component of a two-cocycle with values in the units
of the base field and killed by a nonzero integer is a coboundary.**  This is the multiplicative
reading of the corresponding statement for cocycles with values in the units of the extension. -/
theorem exists_sub_add_eq_adicUnits_of_pow_eq_one (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  set A : Gal(K/k) → Gal(K/k) → Additive Kˣ :=
    fun x y => Additive.ofMul (Units.map (algebraMap k K : k →* K) (a x y)) with hAdef
  have hApow : ∀ x y : Gal(K/k), n • A x y = 0 := by
    intro x y
    show n • Additive.ofMul (Units.map (algebraMap k K : k →* K) (a x y)) = 0
    rw [← ofMul_pow, ← map_pow, hpow, map_one]
    rfl
  have hAcocadd : ∀ x y z : Gal(K/k),
      globalUnitsAut x (A y z) + A x (y * z) = A (x * y) z + A x y := by
    intro x y z
    have hfx : globalUnitsAut x (A y z) = A y z := by
      refine Additive.toMul.injective ?_
      rw [toMul_globalUnitsAut]
      exact smul_algebraMap_units x (a y z)
    rw [hfx]
    show Additive.ofMul (Units.map (algebraMap k K : k →* K) (a y z))
        + Additive.ofMul (Units.map (algebraMap k K : k →* K) (a x (y * z)))
      = Additive.ofMul (Units.map (algebraMap k K : k →* K) (a (x * y) z))
        + Additive.ofMul (Units.map (algebraMap k K : k →* K) (a x y))
    rw [← ofMul_mul, ← ofMul_mul, ← map_mul, ← map_mul, ha]
  exact exists_sub_add_eq_adicUnits_of_nsmul_eq_zero v hunr hn hApow hAcocadd

end Unramified

/-! ### Inflation to an extension containing a square root of minus one -/

section Descent

variable {K L : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K] [Field L]
  [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] [Algebra K L] [IsScalarTower ℚ K L]

/-- **A two-cocycle with values in the units of the rational numbers, killed by a nonzero integer
and a coboundary at every ramified finite place of a subextension, is a coboundary over that
subextension as soon as the ambient extension contains a square root of minus one.**  The cocycle
is inflated to the ambient extension, where the local hypothesis holds at every finite place
because a place unramified below is free and a place ramified below is the hypothesis, and the
trivialising one-cochain obtained there descends. -/
theorem exists_isMulCoboundary_of_exists_sq_eq_neg_one {ι : L} (hι : ι ^ 2 = -1) {n : ℕ}
    (hn : n ≠ 0) {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(K/ℚ) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/ℚ) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap ℚ K : ℚ →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h : Gal(K/ℚ),
      g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K : ℚ →* K) (a g h) := by
  classical
  have hpow' : ∀ x y : Gal(L/ℚ),
      a (AlgEquiv.restrictNormalHom K x) (AlgEquiv.restrictNormalHom K y) ^ n = 1 :=
    fun x y => hpow _ _
  have ha' : ∀ x y w : Gal(L/ℚ),
      a (AlgEquiv.restrictNormalHom K y) (AlgEquiv.restrictNormalHom K w)
          * a (AlgEquiv.restrictNormalHom K x) (AlgEquiv.restrictNormalHom K (y * w))
        = a (AlgEquiv.restrictNormalHom K (x * y)) (AlgEquiv.restrictNormalHom K w)
          * a (AlgEquiv.restrictNormalHom K x) (AlgEquiv.restrictNormalHom K y) := by
    intro x y w
    rw [map_mul (AlgEquiv.restrictNormalHom K) x y, map_mul (AlgEquiv.restrictNormalHom K) y w]
    exact ha _ _ _
  have hall : ∀ w : HeightOneSpectrum (𝓞 L),
      ∃ c : ↥(stabilizer Gal(L/ℚ) w) → Additive (w.adicCompletion L)ˣ,
        ∀ s t : ↥(stabilizer Gal(L/ℚ) w),
          Additive.ofMul (adicUnitHom w (Units.map (algebraMap ℚ L : ℚ →* L)
              (a (AlgEquiv.restrictNormalHom K s.1) (AlgEquiv.restrictNormalHom K t.1))))
            = smulUnitsAut s (c t) - c (s * t) + c s := by
    intro w
    refine exists_sub_add_eq_adicUnits_restrict (k := ℚ) (F := K) (K := L) (a := a) w ?_
    by_cases hunr : Algebra.IsUnramifiedAt (𝓞 ℚ) (primeUnder (𝓞 K) w).asIdeal
    · exact exists_sub_add_eq_adicUnits_of_pow_eq_one _ hunr hn hpow ha
    · exact hram _ hunr
  obtain ⟨b, hb⟩ :=
    exists_isMulCoboundary_of_sq_eq_neg_one (K := L) hι hn hpow' ha' fun w _ => hall w
  exact exists_isMulCoboundary_of_restrictNormalHom (k := ℚ) (F := K) (K := L) ha ⟨b, hb⟩

end Descent

/-! ### The theorem with no condition at infinity -/

/-- **A two-cocycle with values in the units of the rational numbers, killed by a nonzero integer
and a coboundary at every ramified finite place, is a coboundary.**  Adjoining a square root of
minus one removes the condition at the real place, at the cost of ramifying the place above two;
the cost is nil, because the local hypothesis at a place of the enlarged field is inherited from
the place below it, which the enlargement may well leave unramified.  The trivialising one-cochain
obtained over the enlarged field descends to the original one. -/
theorem exists_isMulCoboundary_of_forall_ramified {K : Type} [Field K] [NumberField K]
    [Algebra ℚ K] [IsGalois ℚ K] {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/ℚ) → Gal(K/ℚ) → ℚˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/ℚ), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 ℚ) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(K/ℚ) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/ℚ) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap ℚ K : ℚ →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/ℚ) → Kˣ, ∀ g h : Gal(K/ℚ),
      g • b h / b (g * h) * b g = Units.map (algebraMap ℚ K : ℚ →* K) (a g h) := by
  classical
  obtain ⟨p, hpsep, hpsf⟩ := IsGalois.is_separable_splitting_field ℚ K
  haveI := hpsf
  have hp0 : p ≠ 0 := hpsep.ne_zero
  have hc0 : ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1) ≠ 0 :=
    Polynomial.X_pow_add_C_ne_zero (by norm_num) (1 : ℚ)
  obtain ⟨q, hqp, hqc⟩ : ∃ q : ℚ[X], Polynomial.Splits (p.map (algebraMap ℚ q.SplittingField)) ∧
      Polynomial.Splits (((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1).map
        (algebraMap ℚ q.SplittingField)) := by
    refine ⟨p * ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1), ?_⟩
    have hq := Polynomial.IsSplittingField.splits
      (p * ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1)).SplittingField
      (p * ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1))
    rw [Polynomial.map_mul] at hq
    exact (Polynomial.splits_mul_iff (Polynomial.map_ne_zero hp0)
      (Polynomial.map_ne_zero hc0)).mp hq
  haveI : Normal ℚ q.SplittingField := Normal.of_isSplittingField q
  haveI : IsGalois ℚ q.SplittingField := ⟨⟩
  haveI : NumberField q.SplittingField := NumberField.of_module_finite ℚ q.SplittingField
  letI : Algebra K q.SplittingField :=
    (Polynomial.IsSplittingField.lift K p hqp).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K q.SplittingField :=
    IsScalarTower.of_algebraMap_eq fun x =>
      ((Polynomial.IsSplittingField.lift K p hqp).commutes x).symm
  have hcmap : ((Polynomial.X : ℚ[X]) ^ 2 + Polynomial.C 1).map (algebraMap ℚ q.SplittingField)
      = (Polynomial.X : q.SplittingField[X]) ^ 2 + Polynomial.C 1 := by simp
  rw [hcmap] at hqc
  obtain ⟨z, hz⟩ := hqc.exists_eval_eq_zero (by
    rw [Polynomial.degree_X_pow_add_C (by norm_num) (1 : q.SplittingField)]
    simp)
  have hι : z ^ 2 = -1 := by
    have h : z ^ 2 + 1 = 0 := by simpa using hz
    linear_combination h
  exact exists_isMulCoboundary_of_exists_sq_eq_neg_one (L := q.SplittingField) hι hn hpow ha hram

end InverseGalois.CFT
