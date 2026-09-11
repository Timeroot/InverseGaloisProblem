/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LevelCover

/-!
# The covering, asked of the operator group alone

The covering a rung consumes is stated on the semidirect product of the generic operator group with
the operator group, because that is the group the count on first homology is run in.  What global
duality over a number field produces, though, is a class of the first homology of the *level*, that
is of the operator group by itself: the level is the finite Galois extension the coefficients are
already defined over, and the generic group is a bookkeeping device with no arithmetic in it.

The two are reconciled by the second factor.  The inclusion of the operator group into the
semidirect product is a section of the projection onto it, and the coefficients are inflated along
that projection, so the inclusion carries the coefficients back to themselves.  In homology the
inclusion is therefore a section of the projection as well, and pushing a homology class of the
operator group into the semidirect product loses nothing: the projection brings it back.

Since the projection is natural in an equivariant homomorphism of generic operator groups, a
shrinking which kills the pushed-forward class kills the class one started with.  So a covering by
the homology of the operator group is a covering by the homology of the semidirect product, and the
arithmetic side only ever has to produce the former.

## Main definitions

* `InverseGalois.Shafarevich.semidirectInrHom` — the coefficients inflated from the second factor,
  read back on the second factor.
* `InverseGalois.Shafarevich.HasOperatorShaTateCover` — every everywhere locally trivial class of
  the layer comes from a first homology class of the operator group, compatibly with shrinking.

## Main results

* `InverseGalois.Shafarevich.map_rightHom_map_inr` — **the inclusion of the second factor is a
  section of the projection, in homology.**
* `InverseGalois.Shafarevich.hasShaTateCover_of_hasOperatorShaTateCover` — **a covering by the
  homology of the operator group is a covering by the homology of the semidirect product.**

## Tags

group homology, semidirect product, generic operator group, Poitou-Tate, Shafarevich's theorem
-/

namespace InverseGalois.Shafarevich

open CategoryTheory InverseGalois.CFT

/-! ### The second factor as a section -/

section Section

variable {k : Type} [CommRing k] {N U : Type} [Group N] [Group U] (φ : U →* MulAut N)
  (B : Rep k U)

/-- **The coefficients inflated from the second factor, read back on the second factor, are the
coefficients one started with.**  The morphism recording that is the identity. -/
def semidirectInrHom :
    B ⟶ (Action.res _ (SemidirectProduct.inr : U →* N ⋊[φ] U)).obj (inflate φ B) :=
  𝟙 B

@[simp]
theorem semidirectInrHom_hom : (semidirectInrHom φ B).hom = 𝟙 _ := rfl

/-- The projection onto the second factor undoes its inclusion. -/
theorem rightHom_comp_inr :
    (SemidirectProduct.rightHom (φ := φ)).comp (SemidirectProduct.inr : U →* N ⋊[φ] U)
      = MonoidHom.id U :=
  MonoidHom.ext fun _ => rfl

/-- **The inclusion of the second factor is a section of the projection, in homology.** -/
theorem map_rightHom_map_inr (n : ℕ) (x : groupHomology B n) :
    groupHomology.map (SemidirectProduct.rightHom (φ := φ)) (𝟙 (inflate φ B)) n
        (groupHomology.map (SemidirectProduct.inr : U →* N ⋊[φ] U) (semidirectInrHom φ B) n x)
      = x := by
  have h := map_comp_of_eq (SemidirectProduct.inr : U →* N ⋊[φ] U)
    (SemidirectProduct.rightHom (φ := φ)) (semidirectInrHom φ B) (𝟙 (inflate φ B))
    (rightHom_comp_inr φ) (𝟙 B) (by simp) n
  rw [← ModuleCat.comp_apply, ← h, groupHomology.map_id]
  rfl

end Section

/-! ### A shrinking sees the class of the operator group -/

section Operator

variable {U : Type} [Group U] {S : Type} [Group S] {m n : ℕ}
  {α : Generic U m S →* Generic U n S} {ℓ j : ℕ} {T : Rep (ZMod ℓ) U}

/-- **A shrinking which kills the class pushed into the semidirect product kills the class of the
operator group it was pushed from.**  Both are seen by the projection onto the operator group, which
is natural in the shrinking and undoes the pushing. -/
theorem map_operatorTensorRep_eq_zero_of_map_operatorSemidirect_eq_zero (hα : IsOperatorHom α)
    (x : groupHomology.H1 (genericLayerTensor U m S ℓ j T))
    (h : groupHomology.map (operatorSemidirect hα) (operatorInflateRep hα ℓ j T) 1
        (groupHomology.map (SemidirectProduct.inr : U →* Generic U m S ⋊[genericAut U m S] U)
          (semidirectInrHom (genericAut U m S) (genericLayerTensor U m S ℓ j T)) 1 x) = 0) :
    groupHomology.map (B := genericLayerTensor U n S ℓ j T) (MonoidHom.id U)
      (operatorTensorRep hα ℓ j T) 1 x = 0 := by
  have hsec : groupHomology.map (SemidirectProduct.rightHom (φ := genericAut U m S))
      (𝟙 (genericInflate U m S ℓ j T)) 1
      (groupHomology.map (SemidirectProduct.inr : U →* Generic U m S ⋊[genericAut U m S] U)
        (semidirectInrHom (genericAut U m S) (genericLayerTensor U m S ℓ j T)) 1 x) = x :=
    map_rightHom_map_inr (genericAut U m S) (genericLayerTensor U m S ℓ j T) 1 x
  have hnat := ConcreteCategory.congr_hom (map_rightHom_naturality hα ℓ j T)
    (groupHomology.map (SemidirectProduct.inr : U →* Generic U m S ⋊[genericAut U m S] U)
      (semidirectInrHom (genericAut U m S) (genericLayerTensor U m S ℓ j T)) 1 x)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, hsec, h, map_zero] at hnat
  exact hnat

end Operator

/-! ### The covering on the operator group -/

/-- **Every everywhere locally trivial class of the second cohomology with coefficients in a layer
comes from a first homology class of the operator group, compatibly with shrinking.**

This is the covering in the shape the arithmetic supplies it: the homology is that of the level
alone, with coefficients in the layer tensored with a fixed module, and no bookkeeping group
appears. -/
def HasOperatorShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U] [Finite U]
    [TopologicalSpace U] (N : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ) {k Ω : Type*} [Field k]
    [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k)))
    (W : Rep (ZMod ℓ) U) : Prop :=
  letI := galLayerAction ℓ U N S j φ
  ∀ ε ∈ sha2 ↥(layerSub ℓ (Generic U N S) j) T,
    ∃ x : groupHomology.H1 (genericLayerTensor U N S ℓ j W),
      ∀ (n : ℕ) (α : Generic U N S →* Generic U n S) (hα : IsOperatorHom α),
        groupHomology.map (B := genericLayerTensor U n S ℓ j W) (MonoidHom.id U)
            (operatorTensorRep hα ℓ j W) 1 x = 0 →
          letI := galLayerAction ℓ U n S j φ
          coeffH2 (layerSubMap ℓ α j)
            (layerSubMap_smul_comm φ (fun _ _ => rfl) (fun _ _ => rfl) hα) ε = 1

/-- **A covering by the homology of the operator group is a covering by the homology of the
semidirect product.**  Push the class along the inclusion of the second factor; a shrinking which
kills it there kills it on the operator group, and there the covering already applies. -/
theorem hasShaTateCover_of_hasOperatorShaTateCover (ℓ : ℕ) [Fact ℓ.Prime] (U : Type) [Group U]
    [Finite U] [TopologicalSpace U] (N : ℕ) (S : Type) [Group S] [Finite S] (j : ℕ)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (φ : Gal(Ω/k) →* U)
    (T : Set (Subgroup Gal(Ω/k))) (W : Rep (ZMod ℓ) U)
    (h : HasOperatorShaTateCover ℓ U N S j φ T W) :
    HasShaTateCover ℓ U N S j φ T W := by
  intro ε hε
  obtain ⟨x, hx⟩ := h ε hε
  refine ⟨groupHomology.map (SemidirectProduct.inr :
      U →* Generic U N S ⋊[genericAut U N S] U)
    (semidirectInrHom (genericAut U N S) (genericLayerTensor U N S ℓ j W)) 1 x,
    fun n α hα hkill => ?_⟩
  exact hx n α hα (map_operatorTensorRep_eq_zero_of_map_operatorSemidirect_eq_zero hα x hkill)

end InverseGalois.Shafarevich
