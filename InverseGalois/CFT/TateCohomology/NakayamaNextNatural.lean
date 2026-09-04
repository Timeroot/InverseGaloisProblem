/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TorsionErrorLong

/-!
# The obstruction of Tate and Nakayama, along a map of representations

The comparison of Tate and Nakayama is natural in the representation: a map of representations
carrying a class in degree two to a class in degree two carries the comparison of the first to the
comparison of the second.  The map that *leaves* the comparison in the long exact sequence is the
map induced by the inclusion of the tensor product into the extension attached to the class, read
through the two identifications of the shift, and it is natural for the same reason -- the
identifications are natural, and the two extensions are compared by the very map that made the
comparison natural.

What this buys is the only form in which the obstruction can be computed.  The obstruction attached
to a representation is a map out of the complete cohomology of that representation tensored with
the coefficients, and it is not computable directly; but a class that comes from another
representation carrying a class in degree two above it has an obstruction that is the image of the
obstruction computed there.  **So the values the obstruction takes on the classes coming from a
second representation are exactly the image of the values the obstruction of that second
representation takes.**  For a number field the second representation is the units of a completion,
carrying the localised fundamental class, and the obstruction there is a purely local object.

The identification of the target of the obstruction with the vectors killed by a prime is an
isomorphism, so it may be stripped off a spanning statement without loss: **the spanning condition
that the everywhere locally trivial classes call for holds for the obstruction exactly when it
holds for the map the obstruction is built from**, where naturality is available.

## Main results

* `InverseGalois.CFT.Tate.tateNakayamaIso_naturality`,
  `InverseGalois.CFT.Tate.tateNakayamaIso_symm_naturality`: **the two identifications following the
  connecting map are natural in the representation.**
* `InverseGalois.CFT.Tate.tateNakayamaNextMap_naturality`: **the map leaving the comparison of Tate
  and Nakayama commutes with a map of representations carrying one cocycle of the shift to a
  cohomologous one.**
* `InverseGalois.CFT.Tate.exists_cocycleTensorHom_comp_tateNakayamaTwoNextMap`: **the map leaving
  the comparison attached to a class in degree two commutes with a map of representations**, the
  class on the target being the image of the class on the source.
* `InverseGalois.CFT.Tate.exists_map_range_tateNakayamaTwoNextMap`: **the values the map leaving the
  comparison takes on the classes coming from a second representation are exactly the image of the
  values it takes on that second representation.**
* `InverseGalois.CFT.Tate.map_tateNakayamaPTorsionErrorRight_eq_range_iff`: **the obstruction of
  Tate and Nakayama at a prime takes on a set of classes every value it takes at all exactly when
  the map it is built from does**, the identification of the target being an isomorphism.
* `InverseGalois.CFT.Tate.map_resTateNakayamaPTorsionErrorRight_eq_range_iff`: the same over a
  subgroup of the group.

## Tags

Tate cohomology, Tate–Nakayama, naturality, obstruction, fundamental class, cocycle
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### The two identifications following the connecting map -/

section Iso

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (M : Rep k G)

/-- **The two identifications that follow the connecting map are natural in the representation**:
the shift of a tensor product is the tensor product of the shift naturally, and the complete
cohomology of a shift in a degree is the complete cohomology of the representation one degree
higher, naturally. -/
theorem tateNakayamaIso_naturality (n : ℤ)
    (z : ↥(tateModule (tensorObj (shiftObj A) M) (n + 1))) :
    tateMap (tensorHomLeft M φ) (n + 1 + 1) (tateNakayamaIso A M n z)
      = tateNakayamaIso B M n (tateMap (tensorHomLeft M (shiftHom φ)) (n + 1) z) := by
  show tateMap (tensorHomLeft M φ) (n + 1 + 1) (tateShiftEquiv (tensorObj A M) (n + 1)
      (tateMap (shiftTensorIso A M).hom (n + 1) z))
    = tateShiftEquiv (tensorObj B M) (n + 1) (tateMap (shiftTensorIso B M).hom (n + 1)
      (tateMap (tensorHomLeft M (shiftHom φ)) (n + 1) z))
  rw [tateShiftEquiv_naturality, tateMap_comp_apply, ← shiftTensorIso_naturality,
    tateMap_comp_apply]

/-- **The two identifications that follow the connecting map are natural in the representation**,
read backwards. -/
theorem tateNakayamaIso_symm_naturality (n : ℤ)
    (x : ↥(tateModule (tensorObj A M) (n + 1 + 1))) :
    tateMap (tensorHomLeft M (shiftHom φ)) (n + 1) ((tateNakayamaIso A M n).symm x)
      = (tateNakayamaIso B M n).symm (tateMap (tensorHomLeft M φ) (n + 1 + 1) x) := by
  refine (LinearEquiv.eq_symm_apply _).2 ?_
  rw [← tateNakayamaIso_naturality, LinearEquiv.apply_symm_apply]

end Iso

/-! ### The map leaving the comparison -/

section Next

variable {k G : Type u} [CommRing k] [Group G] [Finite G] {A B : Rep k G} (φ : A ⟶ B)
  (b : groupCohomology.cocycles₁ (shiftObj A)) (c : groupCohomology.cocycles₁ (shiftObj B))
  (y : ↥(shiftObj B).V) (M : Rep k G)
  (hy : ∀ τ : G, (shiftHom φ).hom.hom (b τ) = c τ + ((shiftObj B).ρ τ y - y))

include hy in
/-- **The map leaving the comparison of Tate and Nakayama commutes with a map of representations
carrying one cocycle of the shift to a cohomologous one**, the comparison of the two tensored
extensions being the one that made the comparison of Tate and Nakayama natural. -/
theorem tateNakayamaNextMap_naturality (n : ℤ)
    (x : ↥(tateModule (tensorObj A M) (n + 1 + 1))) :
    tateMap (cocycleTensorHom (shiftHom φ) b c y M hy) (n + 1)
        (tateNakayamaNextMap A b M n x)
      = tateNakayamaNextMap B c M n (tateMap (tensorHomLeft M φ) (n + 1 + 1) x) := by
  show tateMap (cocycleTensorHom (shiftHom φ) b c y M hy) (n + 1)
      (tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1) ((tateNakayamaIso A M n).symm x))
    = tateMap (cocycleTensorSeq (shiftObj B) c M).f (n + 1)
      ((tateNakayamaIso B M n).symm (tateMap (tensorHomLeft M φ) (n + 1 + 1) x))
  have h1 : tateMap (cocycleTensorHom (shiftHom φ) b c y M hy) (n + 1)
        (tateMap (cocycleTensorSeq (shiftObj A) b M).f (n + 1) ((tateNakayamaIso A M n).symm x))
      = tateMap ((cocycleTensorSeq (shiftObj A) b M).f ≫
          cocycleTensorHom (shiftHom φ) b c y M hy) (n + 1) ((tateNakayamaIso A M n).symm x) :=
    tateMap_comp_apply _ _ _ _
  have h2 : (cocycleTensorSeq (shiftObj A) b M).f ≫ cocycleTensorHom (shiftHom φ) b c y M hy
      = tensorHomLeft M (shiftHom φ) ≫ (cocycleTensorSeq (shiftObj B) c M).f :=
    (cocycleTensorSeqHom (shiftHom φ) b c y M hy).comm₁₂.symm
  have h3 : tateMap (tensorHomLeft M (shiftHom φ) ≫ (cocycleTensorSeq (shiftObj B) c M).f)
        (n + 1) ((tateNakayamaIso A M n).symm x)
      = tateMap (cocycleTensorSeq (shiftObj B) c M).f (n + 1)
        (tateMap (tensorHomLeft M (shiftHom φ)) (n + 1) ((tateNakayamaIso A M n).symm x)) :=
    (tateMap_comp_apply _ _ _ _).symm
  refine h1.trans ?_
  rw [h2]
  refine h3.trans ?_
  exact congrArg (fun z => tateMap (cocycleTensorSeq (shiftObj B) c M).f (n + 1) z)
    (tateNakayamaIso_symm_naturality φ M n x)

end Next

/-! ### A class in degree two -/

section DegreeTwo

variable {G : Type} [Group G] [Finite G] {A B : Rep ℤ G} (φ : A ⟶ B) (α : tateModule A 2)
  (M : Rep ℤ G)

include φ in
/-- **The map leaving the comparison of Tate and Nakayama attached to a class in degree two commutes
with a map of representations**, the class on the target being the image of the class on the source:
the two tensored extensions are compared by a map of representations, and that map carries the one
map to the other. -/
theorem exists_cocycleTensorHom_comp_tateNakayamaTwoNextMap :
    ∃ ψ : cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M
        ⟶ cocycleTensorObj (shiftObj B) (tateTwoCocycle B (tateMap φ 2 α)) M,
      ∀ n : ℤ, (tateMap ψ (n + 1)).hom ∘ₗ tateNakayamaTwoNextMap A α M n
        = tateNakayamaTwoNextMap B (tateMap φ 2 α) M n ∘ₗ
          (tateMap (tensorHomLeft M φ) (n + 1 + 1)).hom := by
  obtain ⟨y, hy⟩ := exists_shiftHom_tateTwoCocycle φ α
  exact ⟨cocycleTensorHom (shiftHom φ) (tateTwoCocycle A α)
      (tateTwoCocycle B (tateMap φ 2 α)) y M hy,
    fun n => LinearMap.ext fun x => tateNakayamaNextMap_naturality φ (tateTwoCocycle A α)
      (tateTwoCocycle B (tateMap φ 2 α)) y M hy n x⟩

include φ in
/-- **The values the map leaving the comparison of Tate and Nakayama takes on the classes coming
from a second representation are exactly the image of the values it takes on that second
representation.**  This is the only shape in which the values of the obstruction on a subgroup are
accessible: the second representation may be a local one, where they are computable. -/
theorem exists_map_range_tateNakayamaTwoNextMap :
    ∃ ψ : cocycleTensorObj (shiftObj A) (tateTwoCocycle A α) M
        ⟶ cocycleTensorObj (shiftObj B) (tateTwoCocycle B (tateMap φ 2 α)) M,
      ∀ n : ℤ,
        Submodule.map (tateNakayamaTwoNextMap B (tateMap φ 2 α) M n)
            (LinearMap.range (tateMap (tensorHomLeft M φ) (n + 1 + 1)).hom)
          = Submodule.map (tateMap ψ (n + 1)).hom
            (LinearMap.range (tateNakayamaTwoNextMap A α M n)) := by
  obtain ⟨ψ, hψ⟩ := exists_cocycleTensorHom_comp_tateNakayamaTwoNextMap φ α M
  exact ⟨ψ, fun n => by rw [← LinearMap.range_comp, ← LinearMap.range_comp, hψ n]⟩

end DegreeTwo

/-! ### The obstruction at a prime -/

section Error

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)
  (hT : ∀ q : ℕ, q.Prime → ∀ P : Sylow q G, IsTateClassTwo (P : Subgroup G) A α)

include hW hT

/-- **The obstruction of Tate and Nakayama at a prime takes on a set of classes every value it takes
at all exactly when the map it is built from does.**  The identification of the target of the
obstruction with the vectors of the representation killed by the prime is an isomorphism, so it may
be stripped off a spanning statement without loss. -/
theorem map_tateNakayamaPTorsionErrorRight_eq_range_iff (n : ℤ)
    (V : Submodule ℤ ↥(tateModule (tensorObj A W) (n + 1 + 1))) :
    Submodule.map (tateNakayamaPTorsionErrorRight A α W hW hT n) V
        = LinearMap.range (tateNakayamaPTorsionErrorRight A α W hW hT n)
      ↔ Submodule.map (tateNakayamaTwoNextMap A α W n) V
        = LinearMap.range (tateNakayamaTwoNextMap A α W n) := by
  have hinj : Function.Injective
      ⇑(cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap :=
    (cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).injective
  constructor
  · intro h
    refine Submodule.map_injective_of_injective hinj ?_
    rw [← Submodule.map_comp, ← LinearMap.range_comp]
    exact h
  · intro h
    show Submodule.map ((cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap ∘ₗ
        tateNakayamaTwoNextMap A α W n) V
      = LinearMap.range ((cocycleTensorObjPTorsionEquiv A α W hW hT (n + 1)).toLinearMap ∘ₗ
        tateNakayamaTwoNextMap A α W n)
    rw [Submodule.map_comp, LinearMap.range_comp, h]

end Error

/-! ### The obstruction at a prime over a subgroup -/

section Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (A : Rep ℤ G)
  (α : tateModule A 2)
  (h1 : ∀ S : Subgroup G, Limits.IsZero (tateModule (resObj S A) 1))
  (hfin : ∀ S : Subgroup G, Finite ↥(tateModule (resObj S A) 2))
  (hcard : ∀ S : Subgroup G, Nat.card ↥(tateModule (resObj S A) 2) ≤ Nat.card ↥S)
  (hα : ∀ m : ℤ, m • α = 0 → (Nat.card G : ℤ) ∣ m)
  (H : Subgroup G) (W : Rep ℤ G) (hW : ∀ w : ↥W.V, p • w = 0)

/-- **The obstruction of Tate and Nakayama at a prime, read over a subgroup, takes on a set of
classes every value it takes at all exactly when the map it is built from does.** -/
theorem map_resTateNakayamaPTorsionErrorRight_eq_range_iff (n : ℤ)
    (V : Submodule ℤ ↥(tateModule (tensorObj (resObj H A) (resObj H W)) (n + 1 + 1))) :
    Submodule.map (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n) V
        = LinearMap.range (resTateNakayamaPTorsionErrorRight A α h1 hfin hcard hα H W hW n)
      ↔ Submodule.map (tateNakayamaTwoNextMap (resObj H A) (tateRes H A 2 α) (resObj H W) n) V
        = LinearMap.range
          (tateNakayamaTwoNextMap (resObj H A) (tateRes H A 2 α) (resObj H W) n) :=
  map_tateNakayamaPTorsionErrorRight_eq_range_iff (resObj H A) (tateRes H A 2 α) (resObj H W) hW
    (isTateClassTwo_sylow_resObj A α h1 hfin hcard hα H) n V

end Subgroup

end

end InverseGalois.CFT.Tate
