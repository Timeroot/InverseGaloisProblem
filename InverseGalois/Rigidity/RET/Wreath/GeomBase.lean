/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.Conjugates
import InverseGalois.Rigidity.RET.TamePi1
import InverseGalois.Rigidity.RET.Descent.RegularityInf

/-!
# The geometric constant field inside `ℚ̄(T)`, and the regularity dictionary

Every field occurring in the wreath-product construction is realised as an intermediate field of
the fixed algebraic closure `QTbar = ℚ̄(T)` of `QT = ℚ(T)`.  Degrees, however, are governed by the
*geometric* picture, in which the constant field is enlarged from `ℚ` to `ℚ̄`: an extension
`V / ℚ(T)` and its constant-field extension `V · ℚ̄(T)` have the same degree exactly when `V` meets
the geometric base trivially.  To speak about that at all one first has to put a copy of `ℚ̄(T)`
inside `QTbar`, and that is what this file does.

The copy is produced by the universal property of an algebraically closed field: `ℚ̄(T)` is
algebraic over `ℚ(T)` (its coefficient field is), so `IsAlgClosed.lift` extends the identity of
`ℚ(T)` to an embedding `geomEmbed : ℚ̄(T) → QTbar` over `ℚ(T)`.  Its image, viewed as an
intermediate field of `QTbar / ℚ(T)`, is the **geometric base** `geomBase`.  Two features of it are
used constantly: it contains the base `ℚ(T)`, and it contains *every* element of `QTbar` that is
algebraic over `ℚ`, because the constants `ℚ̄` already sit inside it and an algebraically closed
field admits no proper algebraic extension.

Since `QTbar` is a bare `Type`, a finite Galois extension of `ℚ̄(T)` realised inside it is literally
a cover of the line in the sense of `Rigidity.RET.LineCover`, and `lineCoverOf` performs that
repackaging.

The payload is the regularity dictionary.  The hard half of it is the linear-disjointness theorem
`Descent.regularity_inf_of_embedding`, which computes the intersection of a finite Galois
`ℚ(T)`-model with the geometric base as the image of the model's constant-field base
`constFieldBase`.  Applied to the inclusion of an intermediate field `V` of `QTbar` it says
`V ⊓ geomBase = (constFieldBase V).map V.val`; combining this with the elementary observation that
`constFieldBase V` is trivial precisely when `V` has no constants beyond `ℚ` — which uses that `ℚ`
is relatively algebraically closed in `ℚ(T)` — turns the geometric statement "`V` and `ℚ̄(T)` are
linearly disjoint" into the arithmetic statement "`V / ℚ(T)` is regular".

## Main results

* `Rigidity.RET.Wreath.geomEmbed` — the embedding of `ℚ̄(T)` into the fixed algebraic closure
  `QTbar` of `ℚ(T)`, over `ℚ(T)`.
* `Rigidity.RET.Wreath.geomBase` — its image, the geometric base, as an intermediate field of
  `QTbar / ℚ(T)`.
* `Rigidity.RET.Wreath.mem_geomBase_of_isAlgebraic` — every element of `QTbar` algebraic over `ℚ`
  lies in the geometric base.
* `Rigidity.RET.Wreath.lineCoverOf` — a finite Galois intermediate field of `QTbar / ℚ̄(T)`, read as
  a cover of the line.
* `Rigidity.RET.Wreath.constFieldBase_eq_bot_iff` — the constant-field base of an extension of
  `ℚ(T)` is trivial exactly when the extension has no constants beyond `ℚ`.
* `Rigidity.RET.Wreath.inf_geomBase_eq_map` — the intersection of a finite Galois intermediate
  field with the geometric base is the image of its constant-field base.
* `Rigidity.RET.Wreath.inf_geomBase_eq_bot_iff` — a finite Galois intermediate field meets the
  geometric base trivially exactly when it is regular over `ℚ(T)`.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB (k)

/-! ## The geometric base field `ℚ̄(T)` inside `QTbar` -/

/-- **The geometric function field `ℚ̄(T)` embeds into `QTbar` over `ℚ(T)`.**  Extending the
coefficients along `ℚ → ℚ̄` makes `ℚ̄(T)` an algebraic extension of `ℚ(T)`, and `QTbar` is an
algebraically closed field containing `ℚ(T)`, so the identity of `ℚ(T)` extends to it. -/
noncomputable def geomEmbed : RatFunc k →ₐ[QT] QTbar :=
  letI : Algebra.IsAlgebraic QT (RatFunc k) := Descent.isAlgebraic_ratFunc_closure
  IsAlgClosed.lift

/-- **`QTbar` is an algebra over the geometric function field `ℚ̄(T)`**, through `geomEmbed`. -/
noncomputable instance instAlgebraGeomQTbar : Algebra (RatFunc k) QTbar :=
  geomEmbed.toRingHom.toAlgebra

/-- The structure map of `QTbar` over `ℚ̄(T)` is the chosen embedding. -/
theorem algebraMap_geom_eq (u : RatFunc k) : algebraMap (RatFunc k) QTbar u = geomEmbed u := rfl

/-- **`ℚ(T) → ℚ̄(T) → QTbar` is a scalar tower**, because `geomEmbed` is a `ℚ(T)`-algebra map.

The `ℚ(T)`-action on `ℚ̄(T)` is pinned to the coefficient-extension algebra structure
`Descent.instAlgRatFuncClosure`: a bare `SMul QT (RatFunc k)` is otherwise found through the
`RatFunc` localisation model instead, which is a different term. -/
instance instTowerGeomQTbar :
    @IsScalarTower QT (RatFunc k) QTbar Descent.instAlgRatFuncClosure.toSMul
      instAlgebraGeomQTbar.toSMul (AlgebraicClosure.instAlgebra (RatFunc ℚ)).toSMul :=
  IsScalarTower.of_algebraMap_eq fun x => (geomEmbed.commutes x).symm

/-- **`QTbar` is an algebra over the algebraically closed constant field `ℚ̄`**, through the
inclusion of `ℚ̄` in `ℚ̄(T)` followed by `geomEmbed`. -/
noncomputable instance instAlgebraConstQTbar : Algebra k QTbar :=
  ((algebraMap (RatFunc k) QTbar).comp (algebraMap k (RatFunc k))).toAlgebra

/-- **`ℚ̄ → ℚ̄(T) → QTbar` is a scalar tower**, by construction of the `ℚ̄`-algebra structure. -/
instance instTowerConstGeomQTbar : IsScalarTower k (RatFunc k) QTbar :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- **The rational structure of an intermediate field of `QTbar / ℚ(T)` is compatible with its
`ℚ(T)`-structure.**  Both actions of a rational number are multiplication by its image, and the
structure map preserves rational numbers. -/
instance instTowerRatQTsub (V : IntermediateField QT QTbar) : IsScalarTower ℚ QT ↥V :=
  Rigidity.RET.isScalarTower_rat_ratFunc ↥V

/-- The **geometric base**: the copy of `ℚ̄(T)` inside `QTbar`, read as an intermediate field of
`QTbar / ℚ(T)`. -/
def geomBase : IntermediateField QT QTbar :=
  (⊥ : IntermediateField (RatFunc k) QTbar).restrictScalars QT

/-- An element of `QTbar` lies in the geometric base exactly when it comes from `ℚ̄(T)`. -/
theorem mem_geomBase_iff {x : QTbar} :
    x ∈ geomBase ↔ ∃ u : RatFunc k, algebraMap (RatFunc k) QTbar u = x :=
  IntermediateField.mem_bot

/-- **The geometric base contains the base field `ℚ(T)`**: the embedding of `ℚ̄(T)` is a
`ℚ(T)`-algebra map. -/
theorem algebraMap_mem_geomBase (q : QT) : algebraMap QT QTbar q ∈ geomBase :=
  mem_geomBase_iff.2 ⟨algebraMap QT (RatFunc k) q, geomEmbed.commutes q⟩

/-- **Every element of `QTbar` algebraic over `ℚ` lies in the geometric base.**  The constants `ℚ̄`
sit inside the geometric base and are algebraically closed, so an element algebraic over `ℚ` — hence
over `ℚ̄` — already generates the trivial extension of `ℚ̄` and is therefore a constant. -/
theorem mem_geomBase_of_isAlgebraic {x : QTbar} (hx : IsAlgebraic ℚ x) : x ∈ geomBase := by
  haveI : IsScalarTower ℚ k QTbar := Rigidity.RET.isScalarTower_rat k QTbar
  have hxk : IsAlgebraic k x := hx.tower_top k
  have hAdj : IntermediateField.adjoin k ({x} : Set QTbar) = ⊥ := by
    haveI : Algebra.IsAlgebraic k (IntermediateField.adjoin k ({x} : Set QTbar)) :=
      (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic (F := k) (E := QTbar)).2
        fun z hz => (Set.mem_singleton_iff.1 hz) ▸ hxk
    exact IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hmem : x ∈ IntermediateField.adjoin k ({x} : Set QTbar) :=
    IntermediateField.subset_adjoin _ _ rfl
  rw [hAdj, IntermediateField.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact mem_geomBase_iff.2 ⟨algebraMap k (RatFunc k) c, hc⟩

/-- **The relative algebraic closure of `ℚ` in `QTbar` is contained in the geometric base.**  Set
form of `mem_geomBase_of_isAlgebraic`. -/
theorem algebraicClosure_rat_subset_geomBase :
    (algebraicClosure ℚ QTbar : Set QTbar) ⊆ (geomBase : Set QTbar) := fun _ hx =>
  mem_geomBase_of_isAlgebraic (mem_algebraicClosure_iff'.1 hx).isAlgebraic

/-! ## Intermediate fields over `ℚ̄(T)` as covers of the line -/

/-- **A finite Galois intermediate field of `QTbar / ℚ̄(T)` is a cover of the line.**  It is a finite
Galois extension of `ℚ̄(T)` living in `Type`, which is exactly the data of a `LineCover`; the
integral model is the composite `ℚ̄[X] → ℚ̄(T) → W`. -/
@[reducible] noncomputable def lineCoverOf (W : IntermediateField (RatFunc k) QTbar)
    [FiniteDimensional (RatFunc k) ↥W] [IsGalois (RatFunc k) ↥W] : LineCover :=
  LineCover.of ↥W

@[simp] theorem lineCoverOf_M (W : IntermediateField (RatFunc k) QTbar)
    [FiniteDimensional (RatFunc k) ↥W] [IsGalois (RatFunc k) ↥W] :
    (lineCoverOf W).M = ↥W := rfl

/-! ## The regularity dictionary -/

/-- **The constant-field base of an extension of `ℚ(T)` is trivial exactly when the extension has no
constants beyond `ℚ`.**  If the constants are all rational they already lie in `ℚ(T)`, so they
generate nothing new; conversely a constant lying in the image of `ℚ(T)` comes from an element of
`ℚ(T)` algebraic over `ℚ`, and `ℚ` is relatively algebraically closed in `ℚ(T)`
(`Rigidity.RET.regular_ratFunc`), so that element is rational. -/
theorem constFieldBase_eq_bot_iff (Ω : Type) [Field Ω] [Algebra QT Ω] [CharZero Ω]
    [IsScalarTower ℚ QT Ω] :
    constFieldBase Ω = ⊥ ↔ algebraicClosure ℚ Ω = ⊥ := by
  constructor
  · intro h
    refine bot_unique fun x hx => ?_
    have hxb : x ∈ (⊥ : IntermediateField QT Ω) := by
      have hmem := const_le_constFieldBase Ω hx
      rw [IntermediateField.mem_restrictScalars, h] at hmem
      exact hmem
    rw [IntermediateField.mem_bot] at hxb
    obtain ⟨r, hr⟩ := hxb
    have hxint : IsIntegral ℚ x := mem_algebraicClosure_iff'.1 hx
    have hrint : IsIntegral ℚ r := by
      refine ⟨minpoly ℚ x, minpoly.monic hxint, ?_⟩
      have key : algebraMap QT Ω (Polynomial.aeval r (minpoly ℚ x)) = 0 := by
        rw [← Polynomial.aeval_algebraMap_apply, hr]
        exact minpoly.aeval ℚ x
      have hz := (map_eq_zero_iff _ (algebraMap QT Ω).injective).1 key
      rwa [Polynomial.aeval_def] at hz
    have hrmem : r ∈ algebraicClosure ℚ QT := mem_algebraicClosure_iff'.2 hrint
    rw [Rigidity.RET.regular_ratFunc, IntermediateField.mem_bot] at hrmem
    obtain ⟨q, hq⟩ := hrmem
    rw [IntermediateField.mem_bot]
    exact ⟨q, by rw [IsScalarTower.algebraMap_apply ℚ QT Ω, hq, hr]⟩
  · intro h
    refine bot_unique ?_
    rw [constFieldBase, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, h, IntermediateField.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    rw [SetLike.mem_coe, IntermediateField.mem_bot]
    exact ⟨algebraMap ℚ QT q, by rw [← IsScalarTower.algebraMap_apply, hq]⟩

/-- **The intersection of a finite Galois intermediate field with the geometric base is the image of
its constant-field base.**  This is the linear-disjointness leaf
`Descent.regularity_inf_of_embedding`, applied to the inclusion of `V` into `QTbar`; the field range
of that inclusion is `V` itself. -/
theorem inf_geomBase_eq_map (V : IntermediateField QT QTbar)
    [FiniteDimensional QT ↥V] [IsGalois QT ↥V] :
    V ⊓ geomBase = (constFieldBase ↥V).map V.val := by
  have h := Descent.regularity_inf_of_embedding (Ω := ↥V) (Ombar := QTbar) V.val
  rw [IntermediateField.fieldRange_val] at h
  simpa only [geomBase] using h

/-- **A finite Galois intermediate field meets the geometric base trivially exactly when it is
regular over `ℚ(T)`.**  The intersection is the image of the constant-field base
(`inf_geomBase_eq_map`), the image map is injective, and the constant-field base is trivial exactly
when there are no constants beyond `ℚ` (`constFieldBase_eq_bot_iff`). -/
theorem inf_geomBase_eq_bot_iff (V : IntermediateField QT QTbar)
    [FiniteDimensional QT ↥V] [IsGalois QT ↥V] :
    V ⊓ geomBase = ⊥ ↔ algebraicClosure ℚ ↥V = ⊥ := by
  rw [inf_geomBase_eq_map V, ← constFieldBase_eq_bot_iff ↥V]
  constructor
  · intro h
    refine IntermediateField.map_injective V.val ?_
    rw [h, IntermediateField.map_bot]
  · intro h
    rw [h, IntermediateField.map_bot]

end Rigidity.RET.Wreath
