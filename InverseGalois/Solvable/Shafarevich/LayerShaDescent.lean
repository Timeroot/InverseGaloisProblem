/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.ComapIso
import InverseGalois.CFT.Profinite.H2Congr
import InverseGalois.CFT.Profinite.ShaRestrict
import InverseGalois.CFT.Units.CyclotomicLevel
import InverseGalois.Solvable.Shafarevich.LayerShaLevel

/-!
# The shrinking over an arbitrary number field

The shrinking which annihilates an everywhere locally trivial class with coefficients in a layer was
carried out over a base containing a primitive root of unity of the prime order in play.  That
hypothesis is not needed: adjoining a primitive root of unity to the base cuts out a finite Galois
subextension of degree dividing the prime minus one, and a class of the prime order which dies over
a subextension of degree prime to it dies outright.

The descent is the following circuit.  A class over the base is read over the subextension, where it
is still everywhere locally trivial because a decomposition subgroup over the subextension lands in
one over the base.  The shrinking over the subextension kills it there, and killing commutes with
the map of the coefficients which the shrinking induces, so the shrunken class over the base dies
over the subextension.  Dying over a subextension is dying on the subgroup which fixes it, and a
class of the prime order dying on a subgroup of index prime to that order is trivial.

The number of letters the shrinking starts from is announced before any class is chosen, and it is
inherited unchanged from the shrinking over the subextension: the descent changes the base, not the
count.

## Main results

* `InverseGalois.Shafarevich.hasShrinkableSha_of_intermediate`: a shrinking over a finite Galois
  subextension whose fixing subgroup has index prime to the prime order descends to the base.
* `InverseGalois.Shafarevich.hasShrinkableSha_decompositionSubgroups`: **every everywhere locally
  trivial class with coefficients in a layer dies under a shrinking**, over an arbitrary number
  field.

## Tags

Shafarevich's theorem, embedding problem, locally trivial class, roots of unity, restriction
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

section Main

variable (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U] [TopologicalSpace U]
  [DiscreteTopology U] (n : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ)
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {φ : Gal(Ω/k) →* U}

omit [DiscreteTopology U] in
/-- **A shrinking over a finite Galois subextension descends to the base**, as soon as the subgroup
which fixes the subextension has index prime to the prime order in play.  The class over the base is
read over the subextension, where it is still everywhere locally trivial; the shrinking there kills
it; killing commutes with the map of the coefficients; and a class of the prime order dying on a
subgroup of index prime to that order is trivial. -/
theorem hasShrinkableSha_of_intermediate (F : IntermediateField k Ω) [FiniteDimensional k ↥F]
    [IsGalois k ↥F] (hcop : Nat.Coprime ℓ F.fixingSubgroup.index)
    (h : HasShrinkableSha ℓ U n S j (φ.comp (galSubHom F)) (decompositionSubgroups ↥F Ω)) :
    HasShrinkableSha ℓ U n S j φ (decompositionSubgroups k Ω) := by
  classical
  haveI : Finite (Gal(Ω/k) ⧸ F.fixingSubgroup) :=
    Finite.of_equiv _ (quotientFixingSubgroupEquiv F).symm.toEquiv
  letI : Fintype (Gal(Ω/k) ⧸ F.fixingSubgroup) := Fintype.ofFinite _
  obtain ⟨N, hN⟩ := h
  letI := galLayerAction ℓ U N S j φ
  letI := galLayerAction ℓ U N S j (φ.comp (galSubHom F))
  letI := galLayerAction ℓ U n S j φ
  letI := galLayerAction ℓ U n S j (φ.comp (galSubHom F))
  refine ⟨N, fun ε hε => ?_⟩
  -- the two actions over the subextension are the actions over the base, read through the inclusion
  have hπN : ∀ (g : Gal(Ω/↥F)) (m : ↥(layerSub ℓ (Generic U N S) j)),
      g • m = galSubHom F g • m := fun _ _ => rfl
  have hπn : ∀ (g : Gal(Ω/↥F)) (m : ↥(layerSub ℓ (Generic U n S) j)),
      g • m = galSubHom F g • m := fun _ _ => rfl
  -- the class stays everywhere locally trivial when read over the subextension
  have hεF := comapH2_mem_sha2 hπN (isSmoothHom_galSubHom F) (continuous_galSubHom F)
    (decompositionSubgroups_le_galSubHom F) hε
  obtain ⟨α, hα, hsurj, hone⟩ := hN _ hεF
  refine ⟨α, hα, hsurj, ?_⟩
  -- the shrunken class has prime order and dies on the subgroup which fixes the subextension
  refine eq_one_of_resH2_eq_one_of_coprime F.fixingSubgroup
    (hasOpenNormalCore_of_isOpen F.fixingSubgroup F.fixingSubgroup_isOpen) hcop
    (smoothH2_pow_eq_one (fun m => layerSub_pow_eq_one ℓ (Generic U n S) j m) _)
    (resH2_fixingSubgroup_eq_one F hπn ?_)
  rw [← coeffH2_comapH2 hπN hπn (isSmoothHom_galSubHom F)
    (layerSubMap_smul_comm (φ.comp (galSubHom F)) (fun _ _ => rfl) (fun _ _ => rfl) hα)
    (layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα) ε]
  exact hone

/-- **Every everywhere locally trivial class with coefficients in a layer dies under a shrinking**,
over an arbitrary number field.  The subextension generated by a primitive root of unity of the
prime order carries that root of unity and has degree dividing the prime minus one, so the shrinking
over it descends. -/
theorem hasShrinkableSha_decompositionSubgroups (hS : IsPGroup ℓ S) (hsmφ : IsSmoothHom φ) :
    HasShrinkableSha ℓ U n S j φ (decompositionSubgroups k Ω) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine hasShrinkableSha_of_intermediate ℓ U n S j (cycLevel k Ω ℓ)
    (coprime_index_fixingSubgroup_cycLevel k Ω ℓ Fact.out) ?_
  exact hasShrinkableSha_of_isPrimitiveRoot ℓ U n S j hS
    (isSmoothHom_comp (isSmoothHom_galSubHom (cycLevel k Ω ℓ)) hsmφ)
    (cycLevelRootBase_spec k Ω ℓ)

end Main

end InverseGalois.Shafarevich
