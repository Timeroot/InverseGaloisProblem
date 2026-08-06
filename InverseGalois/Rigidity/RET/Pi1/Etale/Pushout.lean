import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import InverseGalois.Rigidity.RET.Pi1.Etale.Limits
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# Pushouts in the category of finite étale algebras

The Galois category of finite étale covers of `Spec K` is `(FiniteEtaleAlgCat K)ᵒᵖ`.  Its
**pullbacks** — fibre products of covers — are the **pushouts** of the corresponding `K`-algebras,
namely the relative tensor products.  For these to exist in the category the finite étale
`K`-algebras must be closed under the pushout `B ⊗[A] C` of a span `B ⟵ A ⟶ C`.

This file records:

* `pushoutCocone` / `pushoutCoconeIsColimit` — the relative tensor product `B ⊗[A] C` is the pushout
  of the span of structure maps `B ⟵ A ⟶ C` in `CommAlgCat K`;
* closure of `isFiniteEtale K` under pushouts (colimits of shape `WalkingSpan`), obtained by
  identifying the colimit of an arbitrary span of finite étale algebras with such a tensor product;
* the derived `HasPullbacks (FiniteEtaleAlgCat K)ᵒᵖ` — the `PreGaloisCategory` pullback field.
-/

open CategoryTheory Limits
open scoped TensorProduct

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

section Pushout
variable (A B C : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] [Algebra A B] [Algebra A C]
  [IsScalarTower K A B] [IsScalarTower K A C]

/-- Pushout cocone in `CommAlgCat K` over the span `B ⟵ A ⟶ C` of algebra structure maps,
with point `B ⊗[A] C`. -/
noncomputable def pushoutCocone :
    PushoutCocone (CommAlgCat.ofHom (IsScalarTower.toAlgHom K A B))
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom K A C)) :=
  PushoutCocone.mk
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[A] C))
    (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight :
        C →ₐ[A] B ⊗[A] C).restrictScalars K))
    (by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      show (algebraMap A B a) ⊗ₜ[A] (1 : C) = (1 : B) ⊗ₜ[A] (algebraMap A C a)
      rw [← Algebra.TensorProduct.algebraMap_apply (R := A) (S := A) (A := B) (B := C) a,
          ← Algebra.TensorProduct.algebraMap_apply' (R := A) (A := B) (B := C) a])

/-- The `pushoutCocone` is a colimit: `B ⊗[A] C` is the pushout of `B ⟵ A ⟶ C`. -/
noncomputable def pushoutCoconeIsColimit : IsColimit (pushoutCocone (K := K) A B C) :=
  PushoutCocone.isColimitAux' _ fun s => by
    -- install the `A`-algebra structure on `s.pt` via `A → B → s.pt`
    letI : Algebra A s.pt := (s.inl.hom.toRingHom.comp (algebraMap A B)).toAlgebra
    haveI : IsScalarTower K A s.pt := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      show algebraMap K s.pt x = s.inl.hom (algebraMap A B (algebraMap K A x))
      rw [← IsScalarTower.algebraMap_apply K A B x, AlgHom.commutes]
    -- the cocone-compatibility, read on underlying elements of `A`
    have key : ∀ a : A, s.inl.hom (algebraMap A B a) = s.inr.hom (algebraMap A C a) := by
      intro a
      have h2 := congrArg CommAlgCat.Hom.hom s.condition
      rw [CommAlgCat.hom_comp, CommAlgCat.hom_comp] at h2
      have h3 := DFunLike.congr_fun h2 a
      simpa using h3
    -- `s.inl` / `s.inr` as `A`-algebra homs into `s.pt`
    let f' : B →ₐ[A] s.pt :=
      { s.inl.hom with commutes' := fun a => rfl }
    let g' : C →ₐ[A] s.pt :=
      { s.inr.hom with commutes' := fun a => (key a).symm }
    let φ : B ⊗[A] C →ₐ[A] s.pt := Algebra.TensorProduct.productMap f' g'
    let ψ : B ⊗[A] C →ₐ[K] s.pt :=
      { φ.toRingHom with
        commutes' := fun k => by
          show φ (algebraMap K (B ⊗[A] C) k) = algebraMap K s.pt k
          rw [IsScalarTower.algebraMap_apply K A (B ⊗[A] C) k, φ.commutes,
              ← IsScalarTower.algebraMap_apply K A s.pt k] }
    let l : CommAlgCat.of K (B ⊗[A] C) ⟶ s.pt := CommAlgCat.ofHom ψ
    refine ⟨l, ?_, ?_, ?_⟩
    · apply CommAlgCat.hom_ext; apply AlgHom.ext; intro b
      simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply]
      show (Algebra.TensorProduct.productMap f' g') (b ⊗ₜ[A] 1) = s.inl.hom b
      rw [Algebra.TensorProduct.productMap_left_apply]; rfl
    · apply CommAlgCat.hom_ext; apply AlgHom.ext; intro c
      simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply]
      show (Algebra.TensorProduct.productMap f' g') (1 ⊗ₜ[A] c) = s.inr.hom c
      rw [Algebra.TensorProduct.productMap_right_apply]; rfl
    · intro m hinl hinr
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      have hb : ∀ b : B, m.hom (b ⊗ₜ[A] 1) = s.inl.hom b := by
        intro b
        have := congrArg (fun t : CommAlgCat.of K B ⟶ s.pt => t.hom b) hinl
        simpa using this
      have hc : ∀ c : C, m.hom (1 ⊗ₜ[A] c) = s.inr.hom c := by
        intro c
        have := congrArg (fun t : CommAlgCat.of K C ⟶ s.pt => t.hom c) hinr
        simpa using this
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b c =>
          have hsplit : (b ⊗ₜ[A] c : B ⊗[A] C) = (b ⊗ₜ[A] 1) * (1 ⊗ₜ[A] c) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          show m.hom (b ⊗ₜ[A] c) = (Algebra.TensorProduct.productMap f' g') (b ⊗ₜ[A] c)
          rw [Algebra.TensorProduct.productMap_apply_tmul, hsplit, map_mul, hb, hc]
          rfl
      | add x y hx hy =>
          rw [map_add, map_add, hx, hy]

end Pushout

/-- **Finite étale algebras are closed under pushouts.**  The colimit of a span `B ⟵ A ⟶ C` of
finite étale `K`-algebras is again finite étale: it is the relative tensor product `B ⊗[A] C`
(`pushoutCoconeIsColimit`), which is étale over `A` by base change of `B / A` and étale over `K` by
composition through `A`.  (In the opposite category this is closure under pullbacks: the fibre
product of two finite étale covers of `Spec K` is again one.) -/
instance : (isFiniteEtale K).IsClosedUnderColimitsOfShape WalkingSpan := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  letI : Algebra (F.obj WalkingSpan.zero : Type u) (F.obj WalkingSpan.left : Type u) :=
    (F.map WalkingSpan.Hom.fst).hom.toRingHom.toAlgebra
  letI : Algebra (F.obj WalkingSpan.zero : Type u) (F.obj WalkingSpan.right : Type u) :=
    (F.map WalkingSpan.Hom.snd).hom.toRingHom.toAlgebra
  haveI : IsScalarTower K (F.obj WalkingSpan.zero : Type u) (F.obj WalkingSpan.left : Type u) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap K (F.obj WalkingSpan.left : Type u) x
      = (F.map WalkingSpan.Hom.fst).hom (algebraMap K (F.obj WalkingSpan.zero : Type u) x)
    rw [AlgHom.commutes]
  haveI : IsScalarTower K (F.obj WalkingSpan.zero : Type u) (F.obj WalkingSpan.right : Type u) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap K (F.obj WalkingSpan.right : Type u) x
      = (F.map WalkingSpan.Hom.snd).hom (algebraMap K (F.obj WalkingSpan.zero : Type u) x)
    rw [AlgHom.commutes]
  haveI : Algebra.Etale K (F.obj WalkingSpan.zero : Type u) := hF WalkingSpan.zero
  haveI : Algebra.Etale K (F.obj WalkingSpan.left : Type u) := hF WalkingSpan.left
  haveI : Algebra.Etale K (F.obj WalkingSpan.right : Type u) := hF WalkingSpan.right
  -- the pushout `B ⊗[A] C` is finite étale over `K`
  haveI : Algebra.Etale K ((F.obj WalkingSpan.left : Type u) ⊗[(F.obj WalkingSpan.zero : Type u)]
      (F.obj WalkingSpan.right : Type u)) := by
    haveI : Algebra.Etale (F.obj WalkingSpan.zero : Type u) (F.obj WalkingSpan.right : Type u) :=
      etale_of_isScalarTower (K := K) _ _
    haveI : Algebra.Etale (F.obj WalkingSpan.left : Type u)
        ((F.obj WalkingSpan.left : Type u) ⊗[(F.obj WalkingSpan.zero : Type u)]
          (F.obj WalkingSpan.right : Type u)) :=
      Algebra.Etale.baseChange _ _ _
    exact Algebra.Etale.comp K (F.obj WalkingSpan.left : Type u) _
  -- identify `colimit F` with the pushout point via `diagramIsoSpan`
  have hpc : IsColimit (pushoutCocone (K := K) (F.obj WalkingSpan.zero : Type u)
      (F.obj WalkingSpan.left : Type u) (F.obj WalkingSpan.right : Type u)) :=
    pushoutCoconeIsColimit _ _ _
  have hcF : IsColimit ((Cocones.precompose (diagramIsoSpan F).hom).obj
      (pushoutCocone (K := K) (F.obj WalkingSpan.zero : Type u)
        (F.obj WalkingSpan.left : Type u) (F.obj WalkingSpan.right : Type u))) :=
    (IsColimit.precomposeHomEquiv (diagramIsoSpan F) _).symm hpc
  have iso : colimit F ≅ (pushoutCocone (K := K) (F.obj WalkingSpan.zero : Type u)
      (F.obj WalkingSpan.left : Type u) (F.obj WalkingSpan.right : Type u)).pt :=
    (colimit.isColimit F).coconePointUniqueUpToIso hcF
  exact ObjectProperty.prop_of_iso (isFiniteEtale K) iso.symm ‹_›

/-- **`FiniteEtaleAlgCat K` has pushouts.**  These are the relative tensor products; in the opposite
Galois category they are the pullbacks (fibre products of covers). -/
instance : HasPushouts (FiniteEtaleAlgCat K) :=
  hasColimitsOfShape_of_closedUnderColimits _ _

/-- **The Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` has pullbacks** (`PreGaloisCategory` pullback
field): the fibre product of finite étale covers of `Spec K`, dual to the pushout / relative tensor
product of `K`-algebras. -/
instance : HasPullbacks (FiniteEtaleAlgCat K)ᵒᵖ := hasPullbacks_opposite

end Rigidity.RET.Etale
