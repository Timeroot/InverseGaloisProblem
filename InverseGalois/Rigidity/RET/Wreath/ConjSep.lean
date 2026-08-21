/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.ConjPrimitive
import InverseGalois.Rigidity.RET.Wreath.GeomBase

/-!
# Conjugates of a primitive element of a regular extension

The independence of the radicands attached to the conjugates of a primitive element rests on two
facts about those conjugates, read inside `ℚ̄(T)`: each of them is transcendental over the field of
constants `ℚ̄`, and no two of them differ by a constant.

Both are consequences of regularity.  A regular extension of `ℚ(T)` meets the algebraic numbers
only in the rationals, so an algebraic difference of two conjugates is in fact a rational
difference, and rational differences are excluded by the counting argument that an automorphism of
finite order cannot shift an element by a nonzero constant.  Likewise transcendence over `ℚ`
upgrades to transcendence over `ℚ̄` because `ℚ̄ / ℚ` is algebraic.

## Main results

* `Rigidity.RET.Wreath.transcendental_const_of_rat` — transcendence over the rationals implies
  transcendence over the algebraic numbers.
* `Rigidity.RET.Wreath.mem_range_rat_of_isAlgebraic` — an algebraic element of a regular extension
  is rational.
* `Rigidity.RET.Wreath.sub_conj_sub_const_ne_zero_geom` — two distinct conjugates of a primitive
  element of a regular extension never differ by an algebraic constant.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

/-- The rationals, the algebraic numbers and `ℚ̄(T)`'s algebraic closure form a tower: in
characteristic zero there is only one ring homomorphism out of the rationals. -/
instance instTowerRatConstQTbar : IsScalarTower ℚ k QTbar :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- **Transcendence over the rationals upgrades to transcendence over the algebraic numbers**,
because the algebraic numbers are algebraic over the rationals. -/
theorem transcendental_const_of_rat {x : QTbar} (hx : Transcendental ℚ x) : Transcendental k x :=
  hx.extendScalars k

/-- **An algebraic constant of `ℚ̄(T)` is algebraic over the rationals.** -/
theorem isAlgebraic_algebraMap_const (a : k) : IsAlgebraic ℚ (algebraMap k QTbar a) :=
  (isAlgebraic_algHom_iff (ratAlgHom (algebraMap k QTbar)) (algebraMap k QTbar).injective).mpr
    (Algebra.IsAlgebraic.isAlgebraic a)

/-- **An element of a regular extension of `ℚ(T)` that is algebraic over the rationals is
rational.**  Regularity says exactly that the relative algebraic closure of the rationals in the
extension is as small as possible. -/
theorem mem_range_rat_of_isAlgebraic {E : IntermediateField QT QTbar}
    (hreg : algebraicClosure ℚ ↥E = ⊥) {x : ↥E} (hx : IsAlgebraic ℚ x) :
    ∃ q : ℚ, algebraMap ℚ ↥E q = x := by
  have hmem : x ∈ algebraicClosure ℚ ↥E := mem_algebraicClosure_iff.mpr hx
  rw [hreg] at hmem
  exact IntermediateField.mem_bot.mp hmem

/-- **Two distinct conjugates of a primitive element of a regular extension never differ by an
algebraic constant.**  Their difference lies in the extension, so if it were an algebraic constant
it would be a rational one, and an automorphism of finite order cannot shift an element by a
nonzero rational amount. -/
theorem sub_conj_sub_const_ne_zero_geom {E : IntermediateField QT QTbar}
    [FiniteDimensional QT ↥E] (hreg : algebraicClosure ℚ ↥E = ⊥) {θ : ↥E}
    (hprim : IntermediateField.adjoin QT {θ} = ⊤) {g h : ↥E ≃ₐ[QT] ↥E} (hgh : g ≠ h) (a : k) :
    ((g θ : ↥E) : QTbar) - ((h θ : ↥E) : QTbar) - algebraMap k QTbar a ≠ 0 := by
  intro hzero
  set x : ↥E := g θ - h θ with hxd
  have hx : ((x : ↥E) : QTbar) = algebraMap k QTbar a := by
    rw [hxd]
    push_cast
    linear_combination hzero
  have halgx : IsAlgebraic ℚ x := by
    by_contra hcon
    have htr : Transcendental ℚ ((x : ↥E) : QTbar) :=
      transcendental_ringHom (IntermediateField.val E).toRingHom hcon
    rw [hx] at htr
    exact htr (isAlgebraic_algebraMap_const a)
  obtain ⟨q, hq⟩ := mem_range_rat_of_isAlgebraic hreg halgx
  refine sub_conj_sub_const_ne_zero (k := ℚ) hprim hgh q ?_
  rw [hq, hxd]
  ring

end Rigidity.RET.Wreath
