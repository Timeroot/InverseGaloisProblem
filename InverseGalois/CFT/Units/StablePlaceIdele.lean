/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.MapInjective
import InverseGalois.CFT.Units.ABHNOnePlace
import InverseGalois.CFT.Units.DecompositionIdele
import InverseGalois.CFT.Units.IdeleClassSES
import InverseGalois.CFT.Units.InfinitePlaceIdele

/-!
# A cocycle of the units of a completion which bounds in the idele classes

Let a finite place of the top field of a Galois extension of number fields be fixed by the whole
Galois group, so that the group is its own decomposition group there.  The units of the completion
at that place then carry an action of the whole group, and they sit inside the ideles as the ideles
supported at the place.

A two-cocycle of the group with values in those units becomes, through that embedding, a
two-cocycle of the idele classes, and the question is whether a cocycle which bounds downstairs
already bounds upstairs.  It does, and the reason is the theorem of Albert, Brauer, Hasse and
Noether with one place left out: a one-cochain of the idele classes witnessing the bound lifts to
the ideles, and the failure of the lift to bound the cocycle is a two-cocycle of the units of the
top field which, read at any place other than the distinguished one, is the coboundary of the
component of the lift there.  The invariants of that cocycle therefore vanish away from the
distinguished place, the product formula makes the last one vanish too, and the cocycle of the
units of the top field is a coboundary.  Correcting the lift by it produces a one-cochain of the
ideles whose coboundary is the given cocycle on the nose, and reading the component at the place
finishes the argument.

Packaged as a statement about representations, this says that the second cohomology of the units of
the completion injects into that of the idele classes, which is the step that identifies the local
fundamental class at the place with the restriction of the global one.

## Main definitions

* `InverseGalois.CFT.stablePlaceStabilizerHom`: the Galois group of an extension fixing a finite
  place, read inside the decomposition group there.
* `InverseGalois.CFT.stablePlaceUnitsRep`: **the units of the completion at a finite place fixed by
  the whole Galois group, as a representation of that group.**
* `InverseGalois.CFT.stablePlaceIdele`, `InverseGalois.CFT.stablePlaceProj`,
  `InverseGalois.CFT.stablePlaceIdeleClass`: the embedding into the ideles, the component at the
  place, and the composite into the idele classes.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_placeComponent`: **a two-cocycle with values in the units of
  the completion at a finite place fixed by the whole Galois group whose ideles bound in the idele
  class group is a coboundary.**
* `InverseGalois.CFT.injective_map_H2_stablePlaceIdeleClass`: **the second cohomology of the units
  of the completion at such a place injects into that of the idele class group.**
* `InverseGalois.CFT.stablePlaceIdele_comp_proj`: the units of the completion at such a place are a
  retract of the ideles.

## Tags

number field, idele, idele class group, finite place, completion, decomposition group,
two-cocycle, coboundary, Albert-Brauer-Hasse-Noether
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

noncomputable section

section Stable

variable {F K : Type} [Field F] [Field K] [NumberField K] [Algebra F K]
  (w : HeightOneSpectrum (𝓞 K))

variable (F) in
/-- **The Galois group of an extension fixing a finite place, read inside the decomposition group
there.** -/
def stablePlaceStabilizerHom (hw : ∀ σ : Gal(K/F), σ • w = w) :
    Gal(K/F) →* ↥(stabilizer Gal(K/F) w) where
  toFun σ := ⟨σ, mem_stabilizer_iff.mpr (hw σ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] in
variable (F) in
@[simp]
theorem coe_stablePlaceStabilizerHom (hw : ∀ σ : Gal(K/F), σ • w = w) (σ : Gal(K/F)) :
    (stablePlaceStabilizerHom F w hw σ : Gal(K/F)) = σ := rfl

variable (F) in
/-- The embedding of the units of a completion into the ideles is equivariant for a Galois group
fixing the place. -/
theorem ideleAut_adicPlaceIdele_stable (hw : ∀ σ : Gal(K/F), σ • w = w) (σ : Gal(K/F))
    (u : Additive (w.adicCompletion K)ˣ) :
    ideleAut (k := F) σ (adicPlaceIdele K w u)
      = adicPlaceIdele K w (smulUnitsAut (stablePlaceStabilizerHom F w hw σ) u) :=
  ideleAut_adicPlaceIdele_stabilizer F w (stablePlaceStabilizerHom F w hw σ) u

variable (F) in
/-- Reading the component at a finite place is equivariant for a Galois group fixing the place. -/
theorem placeComponent_ideleAut_stable (hw : ∀ σ : Gal(K/F), σ • w = w) (σ : Gal(K/F))
    (y : ↥(idele K)) :
    placeComponent w (ideleAut (k := F) σ y)
      = smulUnitsAut (stablePlaceStabilizerHom F w hw σ) (placeComponent w y) :=
  placeComponent_ideleAut_stabilizer F w (stablePlaceStabilizerHom F w hw σ) y

end Stable

/-! ### Descending a bound from the idele classes -/

section Coboundary

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsGalois F K] (w : HeightOneSpectrum (𝓞 K))

variable (F) in
/-- **A two-cocycle with values in the units of the completion at a finite place fixed by the whole
Galois group whose ideles bound in the idele class group is a coboundary.**  A lift of the bounding
one-cochain to the ideles fails to bound the cocycle by a two-cocycle of the units of the top
field, which is a coboundary at every place but the given one, hence a coboundary; correcting the
lift by it and reading the component at the place gives the bound. -/
theorem exists_sub_add_eq_placeComponent (hw : ∀ σ : Gal(K/F), σ • w = w)
    {x : Gal(K/F) → Gal(K/F) → Additive (w.adicCompletion K)ˣ}
    (hx : ∀ g h j : Gal(K/F),
      smulUnitsAut (stablePlaceStabilizerHom F w hw g) (x h j) + x g (h * j)
        = x (g * h) j + x g h)
    {V : Gal(K/F) → IdeleClass K}
    (hV : ∀ g h : Gal(K/F),
      QuotientAddGroup.mk (adicPlaceIdele K w (x g h))
        = ideleClassAut (k := F) g (V h) - V (g * h) + V g) :
    ∃ c : Gal(K/F) → Additive (w.adicCompletion K)ˣ, ∀ g h : Gal(K/F),
      x g h = smulUnitsAut (stablePlaceStabilizerHom F w hw g) (c h) - c (g * h) + c g := by
  classical
  have hV' : ∀ g h : Gal(K/F), QuotientAddGroup.mk' (ideleDiag K).range
      (adicPlaceIdele K w (x g h))
      = ideleClassAut (k := F) g (V h) - V (g * h) + V g := hV
  have hcm : ∀ (σ : Gal(K/F)) (y : ↥(idele K)),
      QuotientAddGroup.mk' (ideleDiag K).range (ideleAut (k := F) σ y)
        = ideleClassAut (k := F) σ (QuotientAddGroup.mk' (ideleDiag K).range y) :=
    fun σ y => (ideleClassAut_mk σ y).symm
  -- a lift to the ideles of the negative of the bounding one-cochain
  choose v hv using fun g : Gal(K/F) => QuotientAddGroup.mk_surjective (-V g)
  have hv' : ∀ g : Gal(K/F),
      QuotientAddGroup.mk' (ideleDiag K).range (v g) = -V g := hv
  -- the failure of the lift to bound is a principal idele
  have hmem : ∀ g h : Gal(K/F), ∃ y : Additive Kˣ, ideleDiag K y
      = adicPlaceIdele K w (x g h) + (ideleAut (k := F) g (v h) - v (g * h) + v g) := by
    intro g h
    have hz : QuotientAddGroup.mk' (ideleDiag K).range (adicPlaceIdele K w (x g h)
        + (ideleAut (k := F) g (v h) - v (g * h) + v g)) = 0 := by
      rw [map_add, map_add, map_sub, hV' g h, hcm g (v h), hv' h, hv' (g * h), hv' g, map_neg]
      abel
    exact AddMonoidHom.mem_range.1 ((QuotientAddGroup.eq_zero_iff _).1 hz)
  choose a ha using hmem
  -- the ideles supported at the place form a two-cocycle
  have hP : ∀ g h j : Gal(K/F),
      ideleAut (k := F) g (adicPlaceIdele K w (x h j)) + adicPlaceIdele K w (x g (h * j))
        = adicPlaceIdele K w (x (g * h) j) + adicPlaceIdele K w (x g h) := by
    intro g h j
    rw [ideleAut_adicPlaceIdele_stable F w hw g, ← map_add (adicPlaceIdele K w),
      ← map_add (adicPlaceIdele K w), hx g h j]
  -- so does the coboundary of the lift
  have hD : ∀ g h j : Gal(K/F),
      ideleAut (k := F) g (ideleAut (k := F) h (v j) - v (h * j) + v h)
          + (ideleAut (k := F) g (v (h * j)) - v (g * (h * j)) + v g)
        = ideleAut (k := F) (g * h) (v j) - v (g * h * j) + v (g * h)
          + (ideleAut (k := F) g (v h) - v (g * h) + v g) := by
    intro g h j
    rw [map_add, map_sub, ← ideleAut_mul, mul_assoc]
    abel
  -- hence so does their difference, a two-cocycle of the units of the top field
  have ha3 : ∀ g h j : Gal(K/F),
      globalUnitsAut (k := F) g (a h j) + a g (h * j) = a (g * h) j + a g h := by
    intro g h j
    refine ideleDiag_injective K ?_
    rw [map_add, map_add, ← ideleAut_ideleDiag]
    simp only [ha]
    rw [map_add]
    conv_lhs => rw [add_add_add_comm]
    conv_rhs => rw [add_add_add_comm]
    rw [hP g h j, hD g h j]
  -- it is a coboundary at every infinite place
  have hinf : ∀ u : InfinitePlace K,
      ∃ c : ↥(stabilizer Gal(K/F) u) → Additive u.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/F) u),
        Additive.ofMul (infiniteUnitHom u (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
    intro u
    refine ⟨fun s => infinitePlaceComponent u (v (s : Gal(K/F))), fun s t => ?_⟩
    have hc := congrArg (infinitePlaceComponent u) (ha (s : Gal(K/F)) (t : Gal(K/F)))
    rw [infinitePlaceComponent_ideleDiag, map_add, map_add, map_sub,
      infinitePlaceComponent_adicPlaceIdele, zero_add,
      infinitePlaceComponent_ideleAut_stabilizer u s] at hc
    exact hc
  -- and at every finite place but the given one
  have hfin : ∀ W : HeightOneSpectrum (𝓞 K), primeUnder (𝓞 F) W ≠ primeUnder (𝓞 F) w →
      ∃ c : ↥(stabilizer Gal(K/F) W) → Additive (W.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/F) W),
        Additive.ofMul (adicUnitHom W (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
    intro W hW
    have hWne : W ≠ w := fun hWw => hW (by rw [hWw])
    refine ⟨fun s => placeComponent W (v (s : Gal(K/F))), fun s t => ?_⟩
    have hc := congrArg (placeComponent W) (ha (s : Gal(K/F)) (t : Gal(K/F)))
    rw [placeComponent_ideleDiag, map_add, map_add, map_sub,
      placeComponent_adicPlaceIdele_of_ne W hWne, zero_add,
      placeComponent_ideleAut_stabilizer F W s] at hc
    exact hc
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits_of_forall_ne w ha3 hinf hfin
  -- correcting the lift by the resulting one-cochain bounds the ideles at the place exactly
  obtain ⟨U, hU⟩ : ∃ U : Gal(K/F) → ↥(idele K), ∀ g h : Gal(K/F),
      adicPlaceIdele K w (x g h) = ideleAut (k := F) g (U h) - U (g * h) + U g := by
    have e : ∀ A₁ A₂ B₁ B₂ C₁ C₂ : ↥(idele K),
        A₁ - A₂ - (B₁ - B₂) + (C₁ - C₂) = A₁ - B₁ + C₁ - (A₂ - B₂ + C₂) := by
      intro A₁ A₂ B₁ B₂ C₁ C₂
      abel
    refine ⟨fun g => ideleDiag K (b g) - v g, fun g h => ?_⟩
    have h1 : ideleDiag K (a g h)
        = ideleAut (k := F) g (ideleDiag K (b h)) - ideleDiag K (b (g * h))
          + ideleDiag K (b g) := by
      rw [hb g h, map_add, map_sub, ← ideleAut_ideleDiag]
    rw [ha g h] at h1
    have h2 : adicPlaceIdele K w (x g h)
        = ideleAut (k := F) g (ideleDiag K (b h)) - ideleDiag K (b (g * h))
            + ideleDiag K (b g) - (ideleAut (k := F) g (v h) - v (g * h) + v g) := by
      rw [← h1]; abel
    rw [h2, map_sub]
    exact (e _ _ _ _ _ _).symm
  refine ⟨fun g => placeComponent w (U g), fun g h => ?_⟩
  have hc := congrArg (placeComponent w) (hU g h)
  rw [placeComponent_adicPlaceIdele, map_add, map_sub,
    placeComponent_ideleAut_stable F w hw g] at hc
  exact hc

end Coboundary

/-! ### Injectivity on second cohomology -/

section Rep

open CategoryTheory groupCohomology

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [IsGalois F K] (w : HeightOneSpectrum (𝓞 K)) (hw : ∀ σ : Gal(K/F), σ • w = w)

variable (F) in
/-- **The units of the completion at a finite place fixed by the whole Galois group, as a
representation of that group.** -/
abbrev stablePlaceUnitsRep : Rep ℤ Gal(K/F) :=
  repOfAddAut ((smulUnitsAut (G := ↥(stabilizer Gal(K/F) w)) (R := w.adicCompletion K)).comp
    (stablePlaceStabilizerHom F w hw))

variable (F) in
/-- **The units of the completion at a finite place fixed by the whole Galois group, as a
subrepresentation of the ideles.** -/
def stablePlaceIdele : stablePlaceUnitsRep F w hw ⟶ ideleRep F K where
  hom := ModuleCat.ofHom (adicPlaceIdele K w).toIntLinearMap
  comm σ := by
    ext u
    exact (ideleAut_adicPlaceIdele_stable F w hw σ u).symm

variable (F) in
/-- **The component at a finite place fixed by the whole Galois group, as a map of
representations.** -/
def stablePlaceProj : ideleRep F K ⟶ stablePlaceUnitsRep F w hw where
  hom := ModuleCat.ofHom (placeComponent w).toIntLinearMap
  comm σ := by
    ext y
    exact placeComponent_ideleAut_stable F w hw σ y

omit [NumberField F] [IsGalois F K] in
variable (F) in
/-- The units of the completion at a finite place fixed by the whole Galois group are a retract of
the ideles. -/
theorem stablePlaceIdele_comp_proj :
    stablePlaceIdele F w hw ≫ stablePlaceProj F w hw = 𝟙 _ := by
  ext u
  exact placeComponent_adicPlaceIdele w u

variable (F) in
/-- The units of the completion at a finite place fixed by the whole Galois group, mapped to the
idele class group. -/
def stablePlaceIdeleClass : stablePlaceUnitsRep F w hw ⟶ ideleClassRep F K :=
  stablePlaceIdele F w hw ≫ ideleToIdeleClass F K

omit [NumberField F] [IsGalois F K] in
variable (F) in
@[simp]
theorem stablePlaceIdeleClass_hom (u : Additive (w.adicCompletion K)ˣ) :
    (stablePlaceIdeleClass F w hw).hom.hom u
      = QuotientAddGroup.mk' (ideleDiag K).range (adicPlaceIdele K w u) := rfl

variable (F) in
/-- **The second cohomology of the units of the completion at a finite place fixed by the whole
Galois group injects into the second cohomology of the idele class group.**  A two-cocycle whose
class dies downstairs is bounded there by a one-cochain, and the theorem of Albert, Brauer, Hasse
and Noether with the place left out turns that bound into one upstairs. -/
theorem injective_map_H2_stablePlaceIdeleClass :
    Function.Injective
      ((groupCohomology.functor ℤ Gal(K/F) 2).map (stablePlaceIdeleClass F w hw)).hom := by
  refine injective_map_H2_of_forall_mem_coboundaries₂ _ fun z hz hcob => ?_
  obtain ⟨V, hVeq⟩ := hcob
  obtain ⟨c, hc⟩ := exists_sub_add_eq_placeComponent F w hw (x := fun g h => z (g, h)) (V := V)
    (fun g h j => ((mem_cocycles₂_iff _).1 hz g h j).symm)
    (fun g h => (congrFun hVeq (g, h)).symm)
  exact ⟨c, funext fun p => (hc p.1 p.2).symm⟩

end Rep

end

end InverseGalois.CFT
