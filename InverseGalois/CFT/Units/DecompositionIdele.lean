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
it lands in the idele class group.  Since a component of an idele supported at one place recovers
the unit it was built from, the embedding is injective, and so is the map it induces on any
functor of the underlying module.

## Main definitions

* `InverseGalois.CFT.decompositionPlaceIdele`: **the units of the completion at a finite place, as
  a subrepresentation of the ideles for the decomposition group there.**
* `InverseGalois.CFT.decompositionPlaceIdeleClass`: the same, followed by the passage to idele
  classes.

## Main results

* `InverseGalois.CFT.ideleAut_adicPlaceIdele`: **an automorphism fixing a finite place carries the
  idele supported there attached to a unit to the one attached to the transported unit.**
* `InverseGalois.CFT.adicPlaceIdele_injective`: the embedding is injective.

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

end Rep

end

end InverseGalois.CFT
