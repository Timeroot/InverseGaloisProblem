/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.RatFuncGen
import InverseGalois.Rigidity.RET.Descent.FunctionFieldTower

/-!
# Normality over `ℚ(T)` of a geometric extension of `ℚ̄(T)`

A field `Ω` containing `ℚ̄(T)` and generated over it by the roots of a polynomial `M` with
coefficients in `ℚ(T)` is normal over `ℚ(T)`, even though it is infinite over `ℚ(T)`: it is the
splitting field over `ℚ(T)` of `M` together with the minimal polynomials of all the constants.
Both kinds of piece are honest finite splitting fields, hence normal, and a compositum of normal
extensions is normal; the pieces exhaust `Ω` because a field containing the constants and `T`
contains all of `ℚ̄(T)` (`Rigidity.RET.ratFunc_mem_subfield`).

This is what lets the arithmetic Galois closure of a geometric cover be moved around by
`ℚ(T)`-automorphisms: without normality there are `ℚ(T)`-embeddings of `Ω` that leave it, and the
conjugates of the geometric cover inside `Ω` cannot be reached by automorphisms.

## Main definitions

* `Rigidity.RET.Descent.constHom` — the constants `ℚ̄` inside a field over `ℚ̄(T)`.
* `Rigidity.RET.Descent.constPoly` — the `ℚ(T)`-polynomial cutting out the conjugates of a
  constant.
* `Rigidity.RET.Descent.normalPiece` — the finite normal pieces whose compositum is everything.

## Main results

* `Rigidity.RET.Descent.algebraMap_ratFunc_closure_X` — the variable of `ℚ(T)` is the variable of
  `ℚ̄(T)`.
* `Rigidity.RET.Descent.normal_of_adjoin_rootSet` — the normality criterion.
* `Rigidity.RET.Descent.normal_ratFunc_closure` — `ℚ̄(T)` itself is normal over `ℚ(T)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace Rigidity.RET.Descent

set_option synthInstance.maxHeartbeats 200000 in
/-- The action of `ℚ(T)` on `ℚ̄(T)`.  Naming it short-circuits the generic search, which otherwise
unfolds both fields of rational functions down to their polynomial rings at every use. -/
instance (priority := high) smulRatFuncClosure :
    SMul (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) := inferInstance

/-- The variable of `ℚ(T)` maps to the variable of `ℚ̄(T)` under the coefficient extension. -/
theorem algebraMap_ratFunc_closure_X :
    algebraMap (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X (K := ℚ), algebraMap_ratFunc_closure_comp, Polynomial.map_X,
    RatFunc.algebraMap_X]

/-- The constants of the geometric base field, viewed inside a field over `ℚ̄(T)`. -/
def constHom (Ω : Type*) [Field Ω] [Algebra (RatFunc (AlgebraicClosure ℚ)) Ω] :
    AlgebraicClosure ℚ →+* Ω :=
  (algebraMap (RatFunc (AlgebraicClosure ℚ)) Ω).comp
    (algebraMap (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)))

/-- The `ℚ(T)`-polynomial whose roots are the `ℚ`-conjugates of a constant. -/
def constPoly (a : AlgebraicClosure ℚ) : (RatFunc ℚ)[X] :=
  (minpoly ℚ a).map (algebraMap ℚ (RatFunc ℚ))

theorem constPoly_ne_zero (a : AlgebraicClosure ℚ) : constPoly a ≠ 0 :=
  (Polynomial.map_ne_zero_iff (algebraMap ℚ (RatFunc ℚ)).injective).2
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a))

section

variable {Ω : Type*} [Field Ω] [Algebra (RatFunc ℚ) Ω]
  [Algebra (RatFunc (AlgebraicClosure ℚ)) Ω]

/-- The two routes `ℚ → ℚ(T) → Ω` and `ℚ → ℚ̄ → Ω` agree: a ring homomorphism out of `ℚ` is
unique. -/
theorem comp_algebraMap_rat :
    (algebraMap (RatFunc ℚ) Ω).comp (algebraMap ℚ (RatFunc ℚ))
      = (constHom Ω).comp (algebraMap ℚ (AlgebraicClosure ℚ)) :=
  Subsingleton.elim _ _

/-- The conjugates of a constant already lie in `Ω`: the polynomial `constPoly a` splits there,
because it splits over the algebraically closed field of constants. -/
theorem constPoly_splits (a : AlgebraicClosure ℚ) :
    ((constPoly a).map (algebraMap (RatFunc ℚ) Ω)).Splits := by
  have h : (((minpoly ℚ a).map (algebraMap ℚ (AlgebraicClosure ℚ))).map (constHom Ω)).Splits :=
    (IsAlgClosed.splits _).map _
  rw [Polynomial.map_map] at h
  rw [constPoly, Polynomial.map_map, comp_algebraMap_rat]
  exact h

/-- A constant is a root of its conjugate polynomial. -/
theorem constHom_mem_rootSet (a : AlgebraicClosure ℚ) :
    constHom Ω a ∈ (constPoly a).rootSet Ω := by
  refine Polynomial.mem_rootSet'.2 ⟨?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff (algebraMap (RatFunc ℚ) Ω).injective).2 (constPoly_ne_zero a)
  · rw [aeval_def, constPoly, eval₂_map, comp_algebraMap_rat, ← Polynomial.hom_eval₂,
      ← aeval_def, minpoly.aeval, map_zero]

variable (M : (RatFunc ℚ)[X])

set_option maxHeartbeats 400000 in
/-- The finite normal pieces of `Ω` over `ℚ(T)`: the splitting field of `M`, and the splitting
field of the conjugates of each constant. -/
def normalPiece :
    Option (AlgebraicClosure ℚ) → IntermediateField (RatFunc ℚ) Ω
  | none => IntermediateField.adjoin (RatFunc ℚ) (M.rootSet Ω)
  | some a => IntermediateField.adjoin (RatFunc ℚ) ((constPoly a).rootSet Ω)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Each piece is normal: it is a splitting field of a single polynomial. -/
theorem normal_normalPiece (hsplit : (M.map (algebraMap (RatFunc ℚ) Ω)).Splits)
    (i : Option (AlgebraicClosure ℚ)) : Normal (RatFunc ℚ) (normalPiece (Ω := Ω) M i) := by
  cases i with
  | none =>
      haveI : IsSplittingField (RatFunc ℚ) (normalPiece (Ω := Ω) M none) M :=
        adjoin_rootSet_isSplittingField hsplit
      exact Normal.of_isSplittingField M
  | some a =>
      haveI : IsSplittingField (RatFunc ℚ) (normalPiece (Ω := Ω) M (some a)) (constPoly a) :=
        adjoin_rootSet_isSplittingField (constPoly_splits a)
      exact Normal.of_isSplittingField (constPoly a)

variable [IsScalarTower (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) Ω]

/-- The pieces exhaust `Ω`: their compositum contains every constant and the variable, hence all
of `ℚ̄(T)`, and it contains the roots of `M`, which generate `Ω` over `ℚ̄(T)`. -/
theorem iSup_normalPiece_eq_top
    (htop : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) (M.rootSet Ω) = ⊤) :
    (⨆ i, normalPiece (Ω := Ω) M i) = ⊤ := by
  have hconst : ∀ f : RatFunc (AlgebraicClosure ℚ),
      algebraMap (RatFunc (AlgebraicClosure ℚ)) Ω f
        ∈ (⨆ i, normalPiece (Ω := Ω) M i).toSubfield := by
    refine fun f => Rigidity.RET.ratFunc_mem_subfield _ _ (fun c => ?_) ?_ f
    · exact (le_iSup (normalPiece (Ω := Ω) M) (some c) :
        normalPiece (Ω := Ω) M (some c) ≤ _)
        (IntermediateField.subset_adjoin _ _ (constHom_mem_rootSet c))
    · have hX : algebraMap (RatFunc (AlgebraicClosure ℚ)) Ω RatFunc.X
          = algebraMap (RatFunc ℚ) Ω RatFunc.X := by
        rw [← algebraMap_ratFunc_closure_X, ← IsScalarTower.algebraMap_apply]
      rw [hX]
      exact (⨆ i, normalPiece (Ω := Ω) M i).algebraMap_mem _
  have hroots : M.rootSet Ω ⊆ ((⨆ i, normalPiece (Ω := Ω) M i : IntermediateField _ Ω) : Set Ω) :=
    fun x hx => (le_iSup (normalPiece (Ω := Ω) M) none :
      normalPiece (Ω := Ω) M none ≤ _) (IntermediateField.subset_adjoin _ _ hx)
  have hle : (⊤ : IntermediateField (RatFunc (AlgebraicClosure ℚ)) Ω)
      ≤ (⨆ i, normalPiece (Ω := Ω) M i).toSubfield.toIntermediateField hconst := by
    rw [← htop]
    exact IntermediateField.adjoin_le_iff.2 hroots
  refine eq_top_iff.2 fun x _ => ?_
  exact hle (IntermediateField.mem_top (x := x))

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **A field over `ℚ̄(T)` generated by the roots of a `ℚ(T)`-polynomial is normal over `ℚ(T)`.**

The extension is infinite over `ℚ(T)`, but it is the compositum of the finite normal extensions
generated by the roots of `M` and by the conjugates of the constants. -/
theorem normal_of_adjoin_rootSet (hsplit : (M.map (algebraMap (RatFunc ℚ) Ω)).Splits)
    (htop : IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ)) (M.rootSet Ω) = ⊤) :
    Normal (RatFunc ℚ) Ω := by
  haveI : ∀ i, Normal (RatFunc ℚ) (normalPiece (Ω := Ω) M i) := normal_normalPiece M hsplit
  have hn : Normal (RatFunc ℚ) (⨆ i, normalPiece (Ω := Ω) M i : IntermediateField _ Ω) :=
    inferInstance
  rw [iSup_normalPiece_eq_top M htop] at hn
  exact Normal.of_algEquiv IntermediateField.topEquiv

end

/-- **`ℚ̄(T)` is normal over `ℚ(T)`**: it is generated over itself by the roots of `X`, so the
criterion applies with `M = X`. -/
instance normal_ratFunc_closure :
    Normal (RatFunc ℚ) (RatFunc (AlgebraicClosure ℚ)) := by
  refine normal_of_adjoin_rootSet (Ω := RatFunc (AlgebraicClosure ℚ)) Polynomial.X ?_ ?_
  · rw [Polynomial.map_X]
    exact Polynomial.Splits.of_degree_eq_one Polynomial.degree_X
  · refine eq_top_iff.2 fun x _ => ?_
    simpa using (IntermediateField.adjoin (RatFunc (AlgebraicClosure ℚ))
      ((Polynomial.X : (RatFunc ℚ)[X]).rootSet (RatFunc (AlgebraicClosure ℚ)))).algebraMap_mem x

end Rigidity.RET.Descent
