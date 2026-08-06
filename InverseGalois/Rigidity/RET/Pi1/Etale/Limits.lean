import InverseGalois.Rigidity.RET.Pi1.Etale.Category
import InverseGalois.Rigidity.RET.Pi1.Etale.Closure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# Finite products in the category of finite étale algebras

The Galois category of finite étale covers of `Spec K` is `(FiniteEtaleAlgCat K)ᵒᵖ`.  Its finite
**coproducts** — the disjoint unions of covers — are the finite **products** of the corresponding
`K`-algebras, and its **terminal** object (the base cover) is `K` itself.  For these to exist in the
category, the finite étale `K`-algebras must be closed under finite products (a special case of which,
the empty product, is the terminal `K`-algebra).

This file records:

* `Algebra.Etale.pi` — a finite product `∀ j, A j` of finite étale `K`-algebras is finite étale;
* iso-closure of the property `isFiniteEtale K`;
* the identification of the categorical product in `CommAlgCat K` of a finite discrete diagram of
  finite étale algebras as the `Pi`-algebra, hence closure of `isFiniteEtale K` under finite discrete
  limits and `HasFiniteProducts (FiniteEtaleAlgCat K)`;
* the derived `HasFiniteCoproducts` and `HasTerminal` on the opposite (Galois) category — the
  `PreGaloisCategory` fields G1 and G2.
-/

open CategoryTheory Limits

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

/-- Curry an algebra map out of a product indexed by a sigma type: reindex
`(∀ p : Σ j, I j, M p.1 p.2)` into the iterated product `∀ j, ∀ i, M j i`.  Its underlying function
is `Equiv.piCurry`, hence it is bijective. -/
noncomputable def piCurryAlgHom {J : Type u} (I : J → Type u) (M : ∀ j, I j → Type u)
    [∀ j i, CommRing (M j i)] [∀ j i, Algebra K (M j i)] :
    (∀ p : Σ j, I j, M p.1 p.2) →ₐ[K] ∀ j, ∀ i, M j i :=
  Pi.algHom K _ fun j => Pi.algHom K _ fun i =>
    Pi.evalAlgHom K (fun p : Σ j, I j => M p.1 p.2) ⟨j, i⟩

/-- **Sigma re-currying isomorphism.**  A product of products, `∀ j, ∀ i, M j i`, is the product over
the disjoint union of indices `∀ p : Σ j, I j, M p.1 p.2`, as `K`-algebras.  This is `Equiv.piCurry`
promoted to an `AlgEquiv`; it turns a "product of finite products of fields" into a single finite
product of fields, feeding `Algebra.Etale.iff_exists_algEquiv_prod`. -/
noncomputable def piCurryAlgEquiv {J : Type u} (I : J → Type u) (M : ∀ j, I j → Type u)
    [∀ j i, CommRing (M j i)] [∀ j i, Algebra K (M j i)] :
    (∀ p : Σ j, I j, M p.1 p.2) ≃ₐ[K] ∀ j, ∀ i, M j i :=
  AlgEquiv.ofBijective (piCurryAlgHom I M) (Equiv.piCurry (fun j i => M j i)).bijective

/-- **Finite étale algebras are closed under finite products.**  If each `A j` is finite étale over a
field `K` and `J` is finite, then `∀ j, A j` is finite étale.  (In the opposite category this is
closure under finite coproducts: a disjoint union of finitely many finite étale covers of `Spec K` is
again one.) -/
instance Algebra.Etale.pi {J : Type u} [Finite J] (A : J → Type u)
    [∀ j, CommRing (A j)] [∀ j, Algebra K (A j)] [∀ j, Algebra.Etale K (A j)] :
    Algebra.Etale K (∀ j, A j) := by
  choose I finI M finM algM eA hM using
    fun j => (Algebra.Etale.iff_exists_algEquiv_prod K (A j)).mp inferInstance
  letI : ∀ j, Finite (I j) := finI
  letI : ∀ j i, Field (M j i) := finM
  letI : ∀ j i, Algebra K (M j i) := algM
  refine (Algebra.Etale.iff_exists_algEquiv_prod K (∀ j, A j)).mpr
    ⟨Σ j, I j, inferInstance, fun p => M p.1 p.2, inferInstance, inferInstance,
      (AlgEquiv.piCongrRight eA).trans (piCurryAlgEquiv I M).symm, ?_⟩
  rintro ⟨j, i⟩
  exact ⟨(hM j i).1, (hM j i).2⟩

/-- The property of being a finite étale `K`-algebra is closed under isomorphism in `CommAlgCat K`
(étaleness transports along algebra isomorphisms, `Algebra.Etale.of_equiv`). -/
instance : (isFiniteEtale K).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    haveI : Algebra.Etale K X := hX
    exact Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)

/-- The product cone over a discrete diagram `F : Discrete J ⥤ CommAlgCat K`, with apex the
`Pi`-algebra `∀ j, F.obj ⟨j⟩` and projections the evaluation algebra maps. -/
noncomputable def piCone {J : Type u} (F : Discrete J ⥤ CommAlgCat.{u} K) : Cone F where
  pt := CommAlgCat.of K (∀ j, (F.obj ⟨j⟩ : Type u))
  π := Discrete.natTrans fun j =>
    CommAlgCat.ofHom (Pi.evalAlgHom K (fun j => (F.obj ⟨j⟩ : Type u)) j.as)

/-- The `Pi`-algebra cone is a limit: it exhibits `∀ j, F.obj ⟨j⟩` as the categorical product of a
finite discrete diagram in `CommAlgCat K`. -/
noncomputable def piConeIsLimit {J : Type u} (F : Discrete J ⥤ CommAlgCat.{u} K) :
    IsLimit (piCone F) where
  lift s := CommAlgCat.ofHom (Pi.algHom K _ fun j => (s.π.app ⟨j⟩).hom)
  fac s j := by
    obtain ⟨j⟩ := j
    ext x
    rfl
  uniq s m hm := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    funext j
    have h := congrArg (fun g : s.pt ⟶ F.obj ⟨j⟩ => g.hom x) (hm ⟨j⟩)
    simpa using h

/-- Finite étale `K`-algebras are closed under finite discrete limits (finite products): the
categorical product of finitely many finite étale algebras is again finite étale (`Algebra.Etale.pi`,
transported along the identification of the product with the `Pi`-algebra). -/
instance (J : Type u) [Finite J] :
    (isFiniteEtale K).IsClosedUnderLimitsOfShape (Discrete J) := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  haveI : ∀ j : J, Algebra.Etale K (F.obj ⟨j⟩ : Type u) := fun j => hF ⟨j⟩
  have hpi : isFiniteEtale K (piCone F).pt := Algebra.Etale.pi _
  exact ObjectProperty.prop_of_iso (isFiniteEtale K)
    (((limit.isLimit F).conePointUniqueUpToIso (piConeIsLimit F)).symm) hpi

/-- Closure under finite discrete limits indexed by `Fin n` (a `Type 0` shape).  Transported from
the universe-`u` instance above along `Discrete (ULift (Fin n)) ≌ Discrete (Fin n)`, so that the
`Fin n`-indexed products demanded by `HasFiniteProducts` land in the subcategory. -/
instance (n : ℕ) : (isFiniteEtale K).IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
  ObjectProperty.IsClosedUnderLimitsOfShape.of_equivalence
    (J := Discrete (ULift.{u} (Fin n))) (Discrete.equivalence Equiv.ulift)

/-- **`FiniteEtaleAlgCat K` has finite products.**  These are the `Pi`-algebras; in the opposite
Galois category they are the finite coproducts (disjoint unions of covers). -/
instance : HasFiniteProducts (FiniteEtaleAlgCat K) := ⟨fun _ => inferInstance⟩

/-- **The Galois category `(FiniteEtaleAlgCat K)ᵒᵖ` has finite coproducts** (`PreGaloisCategory`
field G2): the disjoint union of finitely many finite étale covers of `Spec K`, dual to the finite
product of `K`-algebras. -/
instance : HasFiniteCoproducts (FiniteEtaleAlgCat K)ᵒᵖ := inferInstance

end Rigidity.RET.Etale
