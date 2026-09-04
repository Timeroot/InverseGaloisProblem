/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicFamily
import InverseGalois.CFT.TateCohomology.RestrictNatural
import InverseGalois.CFT.Units.DecompositionInvariant
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.PlaceIdele

/-!
# The units of a completion as a module of the decomposition group

An idele supported at a single finite place is moved by a Galois automorphism to an idele supported
at the image place, so the ideles supported at one place are stable exactly under the automorphisms
fixing it.  On that subgroup the embedding is equivariant: the automorphism acts on the ideles by
permuting the components and on the units of the completion by the action of the decomposition
group, and the two agree because the transport of the family at a fixed place **is** that action.

The embedding is therefore a map of representations of the decomposition group, from the units of
the completion there to the ideles read on that subgroup, and composing with the passage to classes
it lands in the idele class group.  Reading the component at the place is equivariant for the same
reason, and it recovers the unit an idele supported there was built from: **the units of the
completion are a retract of the ideles for the decomposition group**, so the embedding stays
injective after any functor is applied to it.

## Main definitions

* `InverseGalois.CFT.decompositionPlaceIdele`: **the units of the completion at a finite place, as
  a subrepresentation of the ideles for the decomposition group there.**
* `InverseGalois.CFT.decompositionPlaceIdeleClass`: the same, followed by the passage to idele
  classes.
* `InverseGalois.CFT.decompositionPlaceProj`: the component at a finite place, as a map of
  representations of the decomposition group there.

## Main results

* `InverseGalois.CFT.ideleAut_adicPlaceIdele`: **an automorphism fixing a finite place carries the
  idele supported there attached to a unit to the one attached to the transported unit.**
* `InverseGalois.CFT.adicPlaceIdele_injective`: the embedding is injective.
* `InverseGalois.CFT.decompositionPlaceIdele_comp_proj`: **the units of the completion at a finite
  place are a retract of the ideles for the decomposition group there.**

## Tags

number field, idele, decomposition group, completion, place, Galois representation
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField

noncomputable section

section Equivariance

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  (w : HeightOneSpectrum (𝓞 K))

omit [NumberField k] in
variable (k) in
/-- **An automorphism fixing a finite place permutes the finite components of an idele supported
there trivially**, leaving an idele supported at the same place whose component is the transported
unit. -/
theorem familyAut_fullPlaceIdele_snd (σ : Gal(K/k)) (hσ : σ • w = w)
    (u : Additive (w.adicCompletion K)ˣ) :
    (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ (fullPlaceIdele K w u).2
      = (fullPlaceIdele K w
          ((adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ u)).2 := by
  funext x
  by_cases hx : x = w
  · rw [hx, FamilyAction.familyAut_apply_eq_transport _ hσ, fullPlaceIdele_snd_self,
      fullPlaceIdele_snd_self]
  · rw [FamilyAction.familyAut_apply_eq_transport _ (smul_inv_smul σ x),
      fullPlaceIdele_snd_of_ne (fun h => hx (by rw [← smul_inv_smul σ x, h]; exact hσ)),
      map_zero, fullPlaceIdele_snd_of_ne hx]

omit [NumberField k] in
variable (k) in
/-- **A Galois automorphism fixing a finite place carries the idele supported there attached to a
unit to the one attached to the transported unit.** -/
theorem fullIdeleAut_fullPlaceIdele (σ : Gal(K/k)) (hσ : σ • w = w)
    (u : Additive (w.adicCompletion K)ˣ) :
    fullIdeleAut (k := k) σ (fullPlaceIdele K w u)
      = fullPlaceIdele K w ((adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ u) := by
  have h0 : ∀ a : Additive (w.adicCompletion K)ˣ, (fullPlaceIdele K w a).1 = 0 :=
    fun a => funext fun y => fullPlaceIdele_fst w a y
  rw [fullIdeleAut, prodAut_apply]
  refine Prod.ext ?_ (familyAut_fullPlaceIdele_snd k w σ hσ u)
  rw [h0 u, h0 _, map_zero]

omit [NumberField k] in
variable (k) in
/-- **An automorphism fixing a finite place carries the idele supported there attached to a unit to
the one attached to the transported unit.** -/
theorem ideleAut_adicPlaceIdele (σ : Gal(K/k)) (hσ : σ • w = w)
    (u : Additive (w.adicCompletion K)ˣ) :
    ideleAut (k := k) σ (adicPlaceIdele K w u)
      = adicPlaceIdele K w ((adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ u) :=
  Subtype.ext <| by
    rw [coe_ideleAut, coe_adicPlaceIdele, coe_adicPlaceIdele, fullIdeleAut_fullPlaceIdele k w σ hσ]

omit [NumberField k] in
variable (k) in
/-- **The embedding of the units of a completion into the ideles is equivariant for the
decomposition group there.** -/
theorem ideleAut_adicPlaceIdele_stabilizer (σ : ↥(stabilizer Gal(K/k) w))
    (u : Additive (w.adicCompletion K)ˣ) :
    ideleAut (k := k) (σ : Gal(K/k)) (adicPlaceIdele K w u)
      = adicPlaceIdele K w (smulUnitsAut σ u) := by
  rw [ideleAut_adicPlaceIdele k w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) u,
    transport_adicUnitsFamily w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) u]

/-- **The embedding of the units of a completion into the ideles is injective**: the component at
the place recovers the unit. -/
theorem adicPlaceIdele_injective :
    Function.Injective (adicPlaceIdele K w) := fun a b hab => by
  have h : ((adicPlaceIdele K w a : ↥(idele K)) : FullIdele K).2 w
      = ((adicPlaceIdele K w b : ↥(idele K)) : FullIdele K).2 w := by rw [hab]
  rwa [coe_adicPlaceIdele, coe_adicPlaceIdele, fullPlaceIdele_snd_self,
    fullPlaceIdele_snd_self] at h

/-! ### Reading the component at the place -/

/-- The component at a finite place of an idele. -/
def placeComponent : ↥(idele K) →+ Additive (w.adicCompletion K)ˣ where
  toFun x := (x : FullIdele K).2 w
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem placeComponent_apply (x : ↥(idele K)) :
    placeComponent w x = (x : FullIdele K).2 w := rfl

/-- The component at a finite place of the idele supported there attached to a unit is that
unit. -/
@[simp]
theorem placeComponent_adicPlaceIdele (u : Additive (w.adicCompletion K)ˣ) :
    placeComponent w (adicPlaceIdele K w u) = u := by
  rw [placeComponent_apply, coe_adicPlaceIdele, fullPlaceIdele_snd_self]

/-- The component at a finite place of an idele supported at another one is trivial. -/
@[simp]
theorem placeComponent_adicPlaceIdele_of_ne {v : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (u : Additive (v.adicCompletion K)ˣ) : placeComponent w (adicPlaceIdele K v u) = 0 := by
  rw [placeComponent_apply, coe_adicPlaceIdele, fullPlaceIdele_snd_of_ne h]

/-- The component at a finite place of a principal idele is the image of the unit in the completion
there. -/
@[simp]
theorem placeComponent_ideleDiag (a : Additive Kˣ) :
    placeComponent w (ideleDiag K a) = Additive.ofMul (adicUnitHom w a.toMul) := rfl

omit [NumberField k] in
variable (k) in
/-- **An automorphism fixing a finite place moves the component of an idele there by the transport
of the family at that place.** -/
theorem placeComponent_ideleAut (σ : Gal(K/k)) (hσ : σ • w = w) (x : ↥(idele K)) :
    placeComponent w (ideleAut (k := k) σ x)
      = (adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ (placeComponent w x) := by
  rw [placeComponent_apply, coe_ideleAut, fullIdeleAut, prodAut_apply]
  show (adicRingFamily (k := k) (K := K)).unitsFamily.familyAut σ ((x : FullIdele K).2) w
    = (adicRingFamily (k := k) (K := K)).unitsFamily.transport hσ (placeComponent w x)
  rw [FamilyAction.familyAut_apply_eq_transport _ hσ, placeComponent_apply]

omit [NumberField k] in
variable (k) in
/-- **Reading the component at a finite place is equivariant for the decomposition group there.** -/
theorem placeComponent_ideleAut_stabilizer (σ : ↥(stabilizer Gal(K/k) w)) (x : ↥(idele K)) :
    placeComponent w (ideleAut (k := k) (σ : Gal(K/k)) x)
      = smulUnitsAut σ (placeComponent w x) := by
  rw [placeComponent_ideleAut k w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) x,
    transport_adicUnitsFamily w (σ : Gal(K/k)) (mem_stabilizer_iff.mp σ.2) _]

end Equivariance

/-! ### The map of representations -/

section Rep

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
/-- **The units of the completion at a finite place, as a subrepresentation of the ideles for the
decomposition group there.** -/
def decompositionPlaceIdele :
    decompositionUnitsRep k w ⟶ Tate.resObj (stabilizer Gal(K/k) w) (ideleRep k K) where
  hom := ModuleCat.ofHom (adicPlaceIdele K w).toIntLinearMap
  comm σ := by
    ext u
    exact (ideleAut_adicPlaceIdele_stabilizer k w σ u).symm

variable (k) in
/-- The units of the completion at a finite place, mapped to the idele class group and read on the
decomposition group there. -/
def decompositionPlaceIdeleClass :
    decompositionUnitsRep k w ⟶ Tate.resObj (stabilizer Gal(K/k) w) (ideleClassRep k K) :=
  decompositionPlaceIdele k w ≫ Tate.resHom _ (ideleToIdeleClass k K)

omit [NumberField k] [IsGalois k K] in
variable (k) in
@[simp]
theorem decompositionPlaceIdele_hom (u : Additive (w.adicCompletion K)ˣ) :
    (decompositionPlaceIdele k w).hom.hom u = adicPlaceIdele K w u := rfl

omit [NumberField k] [IsGalois k K] in
variable (k) in
@[simp]
theorem decompositionPlaceIdeleClass_hom (u : Additive (w.adicCompletion K)ˣ) :
    (decompositionPlaceIdeleClass k w).hom.hom u
      = QuotientAddGroup.mk' (ideleDiag K).range (adicPlaceIdele K w u) := rfl

variable (k) in
/-- **The component at a finite place, as a map of representations of the decomposition group
there.** -/
def decompositionPlaceProj :
    Tate.resObj (stabilizer Gal(K/k) w) (ideleRep k K) ⟶ decompositionUnitsRep k w where
  hom := ModuleCat.ofHom (placeComponent w).toIntLinearMap
  comm σ := by
    ext x
    exact placeComponent_ideleAut_stabilizer k w σ x

omit [NumberField k] [IsGalois k K] in
variable (k) in
@[simp]
theorem decompositionPlaceProj_hom (x : ↥(idele K)) :
    (decompositionPlaceProj k w).hom.hom x = placeComponent w x := rfl

omit [NumberField k] [IsGalois k K] in
variable (k) in
/-- **The units of the completion at a finite place are a retract of the ideles for the
decomposition group there.** -/
theorem decompositionPlaceIdele_comp_proj :
    decompositionPlaceIdele k w ≫ decompositionPlaceProj k w = 𝟙 _ := by
  ext u
  exact placeComponent_adicPlaceIdele w u

end Rep

end

end InverseGalois.CFT
