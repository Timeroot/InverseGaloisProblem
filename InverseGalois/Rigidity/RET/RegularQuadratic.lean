/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.KummerCover
import InverseGalois.Rigidity.RET.GeometricIrreducibility
import InverseGalois.Rigidity.RET.RegularCriterion
import InverseGalois.Rigidity.RET.Specialization

/-!
# The first regular realization: `ℚ(T)(√T)`

The Riemann Existence Theorem produces a regular `ℚ(T)`-extension for every finite group; for the
two-element group no such input is needed, because the extension can simply be written down.  This
file carries out that construction: `ℚ(T)(√T) = ℚ(T)[X] / (X² - T)` is a quadratic Galois extension
of `ℚ(T)` which gains no new constants, so the two-element group is a **regular** inverse Galois
group, and — through the specialization theorem — an inverse Galois group over `ℚ`.

Every step is explicit.  `X² - T` is irreducible over `ℚ(T)` (Eisenstein at the prime `T`,
`irreducible_X_pow_sub_C_X`), separable in characteristic zero, and splits in the extension it
generates, since the second root is the negative of the first; the extension is therefore Galois of
degree `2`.  Regularity is the same irreducibility statement read over `ℚ̄(T)`
(`RegularityConverse`), and `X² - T` is Eisenstein at `T` over *any* coefficient field, `ℚ̄`
included.

This is the smallest end-to-end run of the regular route to the inverse Galois problem, and the
first realization on that route that depends on no unproved geometric input.

## Main results

* `Rigidity.RET.sqrtFib` — the polynomial `X² - T` over `ℚ(T)`, with its irreducibility,
  separability, splitting and degree facts.
* `Rigidity.RET.isRegularInverseGalois_of_card_eq_two` — every group of order two is a regular
  inverse Galois group.
* `Rigidity.RET.isInverseGalois_of_card_eq_two` — every group of order two is a Galois group
  over `ℚ`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-! ### The polynomial `X² - T` -/

/-- `X² - T`, as a polynomial over the coefficient ring `ℚ[T]`. -/
def sqrtBase : (Polynomial ℚ)[X] := X ^ 2 - C Polynomial.X

theorem sqrtBase_def : sqrtBase = X ^ 2 - C Polynomial.X := rfl

/-- `X² - T`, as a polynomial over the function field `ℚ(T)`. -/
def sqrtFib : (RatFunc ℚ)[X] := X ^ 2 - C (RatFunc.X : RatFunc ℚ)

theorem sqrtFib_def : sqrtFib = X ^ 2 - C (RatFunc.X : RatFunc ℚ) := rfl

theorem sqrtFib_monic : sqrtFib.Monic := monic_X_pow_sub_C _ two_ne_zero

theorem sqrtFib_irreducible : Irreducible sqrtFib := irreducible_X_pow_sub_C_X ℚ two_ne_zero

theorem sqrtFib_ne_zero : sqrtFib ≠ 0 := sqrtFib_irreducible.ne_zero

theorem sqrtFib_natDegree : sqrtFib.natDegree = 2 := natDegree_X_pow_sub_C

theorem sqrtFib_separable : sqrtFib.Separable :=
  separable_X_pow_sub_C _ (by norm_num) RatFunc.X_ne_zero

instance : Fact (Irreducible sqrtFib) := ⟨sqrtFib_irreducible⟩

/-- The two presentations of `X² - T` agree: the one over `ℚ[T]` maps to the one over `ℚ(T)`. -/
theorem sqrtBase_map : sqrtBase.map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) = sqrtFib := by
  simp [sqrtBase, sqrtFib, Polynomial.map_sub, Polynomial.map_pow, RatFunc.algebraMap_X]

/-! ### The quadratic extension `ℚ(T)(√T)` -/

/-- The square root of `T`, the canonical generator of `ℚ(T)(√T)`. -/
def sqrtT : AdjoinRoot sqrtFib := AdjoinRoot.root sqrtFib

theorem sqrtT_def : sqrtT = AdjoinRoot.root sqrtFib := rfl

theorem sqrtT_sq : sqrtT ^ 2 = algebraMap (RatFunc ℚ) (AdjoinRoot sqrtFib) RatFunc.X := by
  have h : (aeval sqrtT) ((X : (RatFunc ℚ)[X]) ^ 2 - C (RatFunc.X : RatFunc ℚ)) = 0 := by
    rw [sqrtT_def, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  simp only [map_sub, map_pow, aeval_X, aeval_C] at h
  exact sub_eq_zero.mp h

/-- **`X² - T` splits in `ℚ(T)(√T)`**: the second root is the negative of the first. -/
theorem sqrtFib_map_eq :
    sqrtFib.map (algebraMap (RatFunc ℚ) (AdjoinRoot sqrtFib))
      = (X - C sqrtT) * (X + C sqrtT) := by
  have h : ((X : (RatFunc ℚ)[X]) ^ 2 - C (RatFunc.X : RatFunc ℚ)).map
      (algebraMap (RatFunc ℚ) (AdjoinRoot sqrtFib)) = (X - C sqrtT) * (X + C sqrtT) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← sqrtT_sq, C_pow]
    exact (sq_sub_sq _ _).trans (mul_comm _ _)
  exact h

instance : IsSplittingField (RatFunc ℚ) (AdjoinRoot sqrtFib) sqrtFib := by
  refine ⟨?_, ?_⟩
  · rw [sqrtFib_map_eq]
    refine (Polynomial.Splits.X_sub_C sqrtT).mul ?_
    simp only [← map_neg, ← sub_neg_eq_add]
    exact Polynomial.Splits.X_sub_C (-sqrtT)
  · refine top_le_iff.mp ?_
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := sqrtFib)]
    refine Algebra.adjoin_mono ?_
    rw [Set.singleton_subset_iff, Polynomial.mem_rootSet]
    refine ⟨sqrtFib_ne_zero, ?_⟩
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self

instance : FiniteDimensional (RatFunc ℚ) (AdjoinRoot sqrtFib) :=
  (AdjoinRoot.powerBasis sqrtFib_ne_zero).finite

instance : IsGalois (RatFunc ℚ) (AdjoinRoot sqrtFib) :=
  IsGalois.of_separable_splitting_field sqrtFib_separable

theorem finrank_adjoinRoot_sqrtFib :
    Module.finrank (RatFunc ℚ) (AdjoinRoot sqrtFib) = 2 := by
  rw [(AdjoinRoot.powerBasis sqrtFib_ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    sqrtFib_natDegree]

theorem card_aut_sqrtFib :
    Nat.card (AdjoinRoot sqrtFib ≃ₐ[RatFunc ℚ] AdjoinRoot sqrtFib) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, finrank_adjoinRoot_sqrtFib]

theorem minpoly_sqrtT : minpoly (RatFunc ℚ) sqrtT = sqrtFib := by
  rw [sqrtT_def, AdjoinRoot.minpoly_root sqrtFib_ne_zero, sqrtFib_monic.leadingCoeff, inv_one,
    map_one, mul_one]

theorem adjoin_sqrtT_eq_top :
    IntermediateField.adjoin (RatFunc ℚ) {sqrtT} = ⊤ := by
  refine IntermediateField.toSubalgebra_injective ?_
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (show IsAlgebraic (RatFunc ℚ) sqrtT from
        (AdjoinRoot.isIntegral_root sqrtFib_ne_zero).isAlgebraic),
    IntermediateField.top_toSubalgebra, sqrtT_def]
  exact AdjoinRoot.adjoinRoot_eq_top

/-! ### Regularity and the realization -/

/-- **`X² - T` stays irreducible over `ℚ̄(T)`.**  Eisenstein at the prime `T` of `ℚ̄[T]` needs
nothing of the coefficient field, and Gauss's lemma carries the conclusion into the fraction
field. -/
theorem sqrtBase_irreducible_map_toClosureFrac : Irreducible (sqrtBase.map toClosureFrac) := by
  have hmonic : ((X : (Polynomial (AlgebraicClosure ℚ))[X]) ^ 2
      - C (Polynomial.X : Polynomial (AlgebraicClosure ℚ))).Monic := monic_X_pow_sub_C _ two_ne_zero
  have h := (hmonic.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial (AlgebraicClosure ℚ)))).mp
    (irreducible_X_pow_sub_C_X_polynomial two_ne_zero)
  rw [sqrtBase_def, toClosureFrac, ← Polynomial.map_map]
  simpa [Polynomial.map_sub, Polynomial.map_pow] using h

/-- **Every group of order two is a regular inverse Galois group**, realized by `ℚ(T)(√T)`. -/
theorem isRegularInverseGalois_of_card_eq_two {G : Type*} [Group G] (hG : Nat.card G = 2) :
    IsRegularInverseGalois G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic G := isCyclic_of_prime_card hG
  haveI : IsCyclic (AdjoinRoot sqrtFib ≃ₐ[RatFunc ℚ] AdjoinRoot sqrtFib) :=
    isCyclic_of_prime_card card_aut_sqrtFib
  exact IsRegularInverseGalois.of_primitive_irreducible (AdjoinRoot sqrtFib) sqrtT
    adjoin_sqrtT_eq_top sqrtBase (by rw [minpoly_sqrtT, sqrtBase_map])
    sqrtBase_irreducible_map_toClosureFrac
    (mulEquivOfCyclicCardEq (by rw [card_aut_sqrtFib, hG]))

/-- **Every group of order two occurs as a Galois group over `ℚ`.**  Specializing `T` in the
regular extension `ℚ(T)(√T)` and applying Hilbert irreducibility gives, concretely, the quadratic
fields `ℚ(√t)`. -/
theorem isInverseGalois_of_card_eq_two {G : Type} [Group G] (hG : Nat.card G = 2) :
    IsInverseGalois G :=
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  (isRegularInverseGalois_of_card_eq_two hG).isInverseGalois

/-- The symmetric group on two letters is a regular inverse Galois group. -/
theorem isRegularInverseGalois_perm_fin_two : IsRegularInverseGalois (Equiv.Perm (Fin 2)) :=
  isRegularInverseGalois_of_card_eq_two (by simp [Nat.card_eq_fintype_card, Fintype.card_perm])

end Rigidity.RET
