/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.DecompositionField
import InverseGalois.CFT.Units.DecompositionFundamental
import InverseGalois.CFT.Units.DecompositionSubgroup
import InverseGalois.CFT.Units.IdeleClassH2Full
import InverseGalois.CFT.Units.StablePlaceIdele

/-!
# The units of a completion inside the idele classes, on the decomposition group

A finite place of the top field of a Galois extension of number fields is fixed by its
decomposition group and by nothing more, and the decomposition group is the Galois group of the
extension over the decomposition field.  Over that field the place is fixed by the whole group, so
the statement proved there — a two-cocycle with values in the units of the completion whose ideles
bound in the idele classes already bounds — transports to the decomposition group by nothing more
than renaming the group, the actions on the completion and on the idele classes being the ones
attached to the underlying automorphisms of the top field either way.

The consequence is an injectivity statement, and counting turns it into an isomorphism: the second
cohomology of the decomposition group with values in the units of the completion has exactly as
many elements as the group, by local reciprocity, while the second cohomology of the idele classes
restricted to the same group has at most that many.  An injection between them is therefore a
bijection, and along the way the order of the second cohomology of the idele classes on a
decomposition group is pinned to the local degree.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_placeComponent_stabilizer`: **a two-cocycle of the
  decomposition group at a finite place with values in the units of the completion there whose
  ideles bound in the idele class group is a coboundary.**
* `InverseGalois.CFT.injective_map_H2_decompositionPlaceIdeleClass`: **the second cohomology of the
  decomposition group at a finite place with values in the units of the completion injects into the
  second cohomology of the idele class group.**
* `InverseGalois.CFT.bijective_map_H2_decompositionPlaceIdeleClass`: **that injection is a
  bijection.**
* `InverseGalois.CFT.natCard_H2_ideleClassRepRes_stabilizer`: the second cohomology of the idele
  class group restricted to a decomposition group has exactly as many elements as the group.

## Tags

number field, idele class group, decomposition group, decomposition field, second cohomology,
local fundamental class, Albert-Brauer-Hasse-Noether
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField Tate groupCohomology

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

omit [IsGalois k K] in
/-- **The Galois group of the extension over the decomposition field fixes the place.** -/
theorem smul_eq_self_decompositionField (σ : Gal(K/↥(decompositionField k w))) : σ • w = w := by
  have h := ((decompositionFieldEquiv k w).symm σ).2
  rw [mem_stabilizer_iff] at h
  have h2 : decompositionFieldEquiv k w ((decompositionFieldEquiv k w).symm σ) • w
      = ((decompositionFieldEquiv k w).symm σ : Gal(K/k)) • w := rfl
  rw [MulEquiv.apply_symm_apply] at h2
  rw [h2, h]

variable (k) in
/-- **A two-cocycle of the decomposition group at a finite place with values in the units of the
completion there whose ideles bound in the idele class group is a coboundary.**  The decomposition
group is the Galois group of the extension over the decomposition field, and over that field the
place is fixed by the whole group. -/
theorem exists_sub_add_eq_placeComponent_stabilizer
    {x : ↥(stabilizer Gal(K/k) w) → ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ}
    (hx : ∀ g h j : ↥(stabilizer Gal(K/k) w),
      smulUnitsAut g (x h j) + x g (h * j) = x (g * h) j + x g h)
    {V : ↥(stabilizer Gal(K/k) w) → IdeleClass K}
    (hV : ∀ g h : ↥(stabilizer Gal(K/k) w),
      QuotientAddGroup.mk (adicPlaceIdele K w (x g h))
        = ideleClassAut (k := k) (g : Gal(K/k)) (V h) - V (g * h) + V g) :
    ∃ c : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
      ∀ g h : ↥(stabilizer Gal(K/k) w),
        x g h = smulUnitsAut g (c h) - c (g * h) + c g := by
  have hs : ∀ (σ : Gal(K/↥(decompositionField k w))) (u : Additive (w.adicCompletion K)ˣ),
      smulUnitsAut
          (stablePlaceStabilizerHom ↥(decompositionField k w) w
            (smul_eq_self_decompositionField w) σ) u
        = smulUnitsAut ((decompositionFieldEquiv k w).symm σ) u := fun _ _ => rfl
  have hic : ∀ (σ : Gal(K/↥(decompositionField k w))) (z : IdeleClass K),
      ideleClassAut (k := ↥(decompositionField k w)) σ z
        = ideleClassAut (k := k) (((decompositionFieldEquiv k w).symm σ : Gal(K/k))) z :=
    fun _ _ => rfl
  obtain ⟨c, hc⟩ := exists_sub_add_eq_placeComponent ↥(decompositionField k w) w
    (smul_eq_self_decompositionField w)
    (x := fun g h => x ((decompositionFieldEquiv k w).symm g)
      ((decompositionFieldEquiv k w).symm h))
    (V := fun g => V ((decompositionFieldEquiv k w).symm g))
    (fun g h j => by
      dsimp only
      rw [hs, map_mul, map_mul]
      exact hx _ _ _)
    (fun g h => by
      dsimp only
      rw [hic, map_mul]
      exact hV _ _)
  refine ⟨fun g => c (decompositionFieldEquiv k w g), fun g h => ?_⟩
  have hgh := hc (decompositionFieldEquiv k w g) (decompositionFieldEquiv k w h)
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, ← map_mul] at hgh
  exact hgh

variable (k) in
/-- **The second cohomology of the decomposition group at a finite place with values in the units
of the completion injects into the second cohomology of the idele class group.** -/
theorem injective_map_H2_decompositionPlaceIdeleClass :
    Function.Injective ((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).map
      (decompositionPlaceIdeleClass k w)).hom := by
  refine injective_map_H2_of_forall_mem_coboundaries₂ _ fun z hz hcob => ?_
  obtain ⟨V, hVeq⟩ := hcob
  obtain ⟨c, hc⟩ := exists_sub_add_eq_placeComponent_stabilizer k w
    (x := fun g h => z (g, h)) (V := V)
    (fun g h j => ((mem_cocycles₂_iff _).1 hz g h j).symm)
    (fun g h => (congrFun hVeq (g, h)).symm)
  exact ⟨c, funext fun p => (hc p.1 p.2).symm⟩

variable (k) in
/-- The second cohomology of a decomposition group at a finite place with values in the units of
the completion there has exactly as many elements as the group. -/
theorem natCard_H2_decompositionUnits :
    Nat.card ↥(H2 (decompositionUnitsRep k w)) = Nat.card ↥(stabilizer Gal(K/k) w) := by
  rw [natCard_stabilizer_eq_finrank k w, ← natCard_tateModule_decompositionUnits k w]
  exact Nat.card_congr
    (Multiplicative.toAdd (α := ↥(tateModule (decompositionUnitsRep k w) 2))).symm

variable (k) in
/-- **The second cohomology of the decomposition group at a finite place with values in the units
of the completion is isomorphic to the second cohomology of the idele class group there.**  The
injection has a source of exactly the order of the group and a target of at most that order, so it
is onto as well. -/
theorem bijective_map_H2_decompositionPlaceIdeleClass :
    Function.Bijective ((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).map
      (decompositionPlaceIdeleClass k w)).hom := by
  obtain ⟨hfin, hle⟩ := finite_and_card_H2_res_subgroup (k := k) (K := K)
    (stabilizer Gal(K/k) w)
  have hinj := injective_map_H2_decompositionPlaceIdeleClass k w
  haveI : Finite ↥((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).obj
      (Tate.resObj (stabilizer Gal(K/k) w) (ideleClassRep k K))) := hfin
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, le_antisymm ?_ ?_⟩
  · exact Nat.card_le_card_of_injective _ hinj
  · have h1 : Nat.card ↥((groupCohomology.functor ℤ ↥(stabilizer Gal(K/k) w) 2).obj
        (Tate.resObj (stabilizer Gal(K/k) w) (ideleClassRep k K)))
        ≤ Nat.card ↥(stabilizer Gal(K/k) w) := hle
    exact h1.trans (natCard_H2_decompositionUnits k w).ge

variable (k) in
/-- **The second cohomology of the idele class group restricted to a decomposition group at a
finite place has exactly as many elements as the group.** -/
theorem natCard_H2_ideleClassRepRes_stabilizer :
    Nat.card ↥(H2 (ideleClassRepRes k K (stabilizer Gal(K/k) w)))
      = Nat.card ↥(stabilizer Gal(K/k) w) := by
  rw [← natCard_H2_decompositionUnits k w]
  exact (Nat.card_eq_of_bijective _ (bijective_map_H2_decompositionPlaceIdeleClass k w)).symm

end

end InverseGalois.CFT
