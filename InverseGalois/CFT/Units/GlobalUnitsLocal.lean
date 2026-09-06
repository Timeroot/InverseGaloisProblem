/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.IdeleLocalVanish

/-!
# The units of a number field, read at one place through the ideles

A unit of a number field becomes an idele, and an idele has a component at every place.  Reading
the diagonal that way at a single place is the embedding of the units of the field into the units
of the completion there, and the whole passage is transparent: the diagonal is defined
componentwise, the ideles sit inside the product of all the local unit groups by inclusion, the
finite half of that product is a projection, and evaluating a section at an index is evaluation.

Tensoring with coefficients changes nothing, because a map of representations tensored with the
coefficients acts on a pure tensor factorwise.  So **the units of a number field tensored with
coefficients, restricted to the decomposition subgroup of a place and evaluated there, is the
embedding into the completion tensored with the identity** — a map which the comparison of a
decomposition subgroup with a completion knows how to annihilate.

That identification is what turns the local theory into a global statement.  A class of the first
cohomology of the units tensored with coefficients of finite rank over a prime field maps to a
class of the ideles, and a class of the ideles which vanishes in every decomposition subgroup is
zero; so **a class of the units whose image at every place vanishes dies in the ideles.**

## Main definitions

* `InverseGalois.CFT.globalUnitsInfiniteLocalHom`, `InverseGalois.CFT.globalUnitsAdicLocalHom`: the
  twisted units of a number field read in the decomposition subgroup of a place and evaluated
  there.

## Main results

* `InverseGalois.CFT.globalUnitsInfiniteLocalHom_apply`,
  `InverseGalois.CFT.globalUnitsAdicLocalHom_apply`: **that reading is the embedding of the units
  into the completion, tensored with the identity of the coefficients.**
* `InverseGalois.CFT.tateMap_globalUnitsToIdele_eq_zero`: **a class of the first cohomology of the
  twisted units all of whose local classes vanish dies in the ideles.**

## Tags

number field, idele, decomposition group, completion, Tate cohomology, local-global
-/

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate

open scoped TensorProduct

noncomputable section

/-! ### The units read at one place -/

section Hom

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k))

/-- **The twisted units of a number field read in the decomposition subgroup of an infinite place
and evaluated there.** -/
def globalUnitsInfiniteLocalHom (w : InfinitePlace K) :
    resObj (stabilizer Gal(K/k) w) (tensorObj (globalUnitsRep k K) W) ⟶
      tensorObj (orbitStabRep w (fun g : ↥(stabilizer Gal(K/k) w) => g.2)
        (infiniteRingFamily (k := k) (K := K)).unitsFamily)
        (resObj (stabilizer Gal(K/k) w) W) :=
  resHom _ (tensorHomLeft W (globalUnitsToIdele k K)) ≫ ideleInfiniteLocalHom k K W w

/-- **The twisted units of a number field read in the decomposition subgroup of a finite place and
evaluated there.** -/
def globalUnitsAdicLocalHom (v : HeightOneSpectrum (𝓞 K)) :
    resObj (stabilizer Gal(K/k) v) (tensorObj (globalUnitsRep k K) W) ⟶
      tensorObj (orbitStabRep v (fun g : ↥(stabilizer Gal(K/k) v) => g.2)
        (adicRingFamily (k := k) (K := K)).unitsFamily)
        (resObj (stabilizer Gal(K/k) v) W) :=
  resHom _ (tensorHomLeft W (globalUnitsToIdele k K)) ≫ ideleAdicLocalHom k K W v

omit [NumberField k] in
/-- Reading the twisted units at an infinite place sends a pure tensor to the local unit tensored
with the same coefficient. -/
theorem globalUnitsInfiniteLocalHom_tmul (w : InfinitePlace K) (a : Additive Kˣ) (x : ↥W.V) :
    (globalUnitsInfiniteLocalHom k K W w).hom.hom (a ⊗ₜ[ℤ] x)
      = Additive.ofMul (infiniteUnitHom w a.toMul) ⊗ₜ[ℤ] x := rfl

omit [NumberField k] in
/-- Reading the twisted units at a finite place sends a pure tensor to the local unit tensored with
the same coefficient. -/
theorem globalUnitsAdicLocalHom_tmul (v : HeightOneSpectrum (𝓞 K)) (a : Additive Kˣ) (x : ↥W.V) :
    (globalUnitsAdicLocalHom k K W v).hom.hom (a ⊗ₜ[ℤ] x)
      = Additive.ofMul (adicUnitHom v a.toMul) ⊗ₜ[ℤ] x := rfl

omit [NumberField k] in
/-- **Reading the twisted units in the decomposition subgroup of an infinite place is the embedding
of the units into the completion there, tensored with the identity of the coefficients.** -/
theorem globalUnitsInfiniteLocalHom_apply (w : InfinitePlace K)
    (t : ↥(tensorObj (globalUnitsRep k K) W).V) :
    (globalUnitsInfiniteLocalHom k K W w).hom.hom t
      = TensorProduct.map (MonoidHom.toAdditive (infiniteUnitHom w)).toIntLinearMap
        (LinearMap.id : ↥W.V →ₗ[ℤ] ↥W.V) t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero, _root_.map_zero]
  | tmul a x => exact globalUnitsInfiniteLocalHom_tmul k K W w a x
  | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb]

omit [NumberField k] in
/-- **Reading the twisted units in the decomposition subgroup of a finite place is the embedding of
the units into the completion there, tensored with the identity of the coefficients.** -/
theorem globalUnitsAdicLocalHom_apply (v : HeightOneSpectrum (𝓞 K))
    (t : ↥(tensorObj (globalUnitsRep k K) W).V) :
    (globalUnitsAdicLocalHom k K W v).hom.hom t
      = TensorProduct.map (MonoidHom.toAdditive (adicUnitHom v)).toIntLinearMap
        (LinearMap.id : ↥W.V →ₗ[ℤ] ↥W.V) t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [_root_.map_zero, _root_.map_zero]
  | tmul a x => exact globalUnitsAdicLocalHom_tmul k K W v a x
  | add a b ha hb => rw [_root_.map_add, _root_.map_add, ha, hb]

end Hom

/-! ### A class of the units trivial at every place -/

section Main

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (W : Rep ℤ Gal(K/k)) {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))

include e in
/-- **A class of the first cohomology of the twisted units of a number field all of whose local
classes vanish dies in the ideles.**  Restriction to a decomposition subgroup commutes with the
diagonal, so the local hypotheses are exactly the local hypotheses of the detection theorem for the
ideles. -/
theorem tateMap_globalUnitsToIdele_eq_zero
    (x : groupCohomology (tensorObj (globalUnitsRep k K) W) 1)
    (h₁ : ∀ w : InfinitePlace K, tateMap (globalUnitsInfiniteLocalHom k K W w) 1
      (tateRes (stabilizer Gal(K/k) w) (tensorObj (globalUnitsRep k K) W) 1 x) = 0)
    (h₂ : ∀ v : HeightOneSpectrum (𝓞 K), tateMap (globalUnitsAdicLocalHom k K W v) 1
      (tateRes (stabilizer Gal(K/k) v) (tensorObj (globalUnitsRep k K) W) 1 x) = 0) :
    tateMap (tensorHomLeft W (globalUnitsToIdele k K)) 1 x = 0 := by
  refine eq_zero_of_forall_local_idele W e _ (fun w => ?_) (fun v => ?_)
  · rw [tateRes_naturality, tateMap_comp_apply]
    exact h₁ w
  · rw [tateRes_naturality, tateMap_comp_apply]
    exact h₂ v

end Main

end

end InverseGalois.CFT
