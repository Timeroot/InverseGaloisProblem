import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Pi

open scoped TensorProduct

/-!
# Closure properties of finite étale algebras over a field

The Galois category of finite étale covers of `Spec K` is the *opposite* of the category of finite
étale `K`-algebras.  Its finite **coproducts** are therefore **products** of `K`-algebras, and its
**terminal** object is the coordinate ring `K` of the base point.  For these to live in the category
at all, the class of finite étale `K`-algebras must be closed under finite products (and contain `K`).

This file records the binary-product closure as a genuine instance:

* `Algebra.Etale.prod` — a binary product `A × B` of finite étale `K`-algebras is finite étale.
  (The base field `K` is étale over itself already by inference.)

The proof goes through the structural characterisation `Algebra.Etale.iff_exists_algEquiv_prod`: a
finite étale `K`-algebra is a finite product of finite separable field extensions, and a product of
two such is again one, indexed by the disjoint union.  The gluing isomorphism
`((∀ i, P i) × (∀ j, Q j)) ≃ₐ[K] ∀ k : I ⊕ J, Sum.elim P Q k` is provided by `prodPiSumAlgEquiv`.
-/

namespace Rigidity.RET.Etale

universe u

variable {K : Type u} [Field K]

/-- Componentwise `Field` structure on a family indexed by a disjoint union.  Made an instance so
that the canonical `CommRing`/`Semiring` structure on `Sum.elim P Q k` — used throughout — always
factors through *this* one `Field`, avoiding a ring-structure diamond. -/
private instance sumElimField {I J : Type u} (P : I → Type u) (Q : J → Type u)
    [∀ i, Field (P i)] [∀ j, Field (Q j)] : ∀ k, Field (Sum.elim P Q k) :=
  fun k => Sum.rec (fun i => inferInstanceAs (Field (P i)))
                   (fun j => inferInstanceAs (Field (Q j))) k

/-- Componentwise `Algebra` structure on a family indexed by a disjoint union, relative to the
`Field`-derived ring structure of `sumElimField`. -/
private instance sumElimAlgebra {I J : Type u} (P : I → Type u) (Q : J → Type u)
    [∀ i, Field (P i)] [∀ j, Field (Q j)] [∀ i, Algebra K (P i)] [∀ j, Algebra K (Q j)] :
    ∀ k, Algebra K (Sum.elim P Q k) :=
  fun k => Sum.rec (fun i => inferInstanceAs (Algebra K (P i)))
                   (fun j => inferInstanceAs (Algebra K (Q j))) k

/-- The evaluation-based algebra map
`(∀ k : I ⊕ J, N k) →ₐ[K] (∀ i, N (Sum.inl i)) × (∀ j, N (Sum.inr j))` that reindexes a dependent
product over a disjoint union into a pair of products over each summand.  Its underlying function is
`Equiv.sumPiEquivProdPi`, hence it is bijective. -/
noncomputable def sumPiToProdPiAlgHom {I J : Type u} (N : I ⊕ J → Type u)
    [∀ k, CommRing (N k)] [∀ k, Algebra K (N k)] :
    (∀ k, N k) →ₐ[K] (∀ i, N (Sum.inl i)) × (∀ j, N (Sum.inr j)) :=
  (Pi.algHom K _ fun i => Pi.evalAlgHom K N (Sum.inl i)).prod
    (Pi.algHom K _ fun j => Pi.evalAlgHom K N (Sum.inr j))

/-- **Gluing isomorphism.**  A pair of dependent products over `I` and `J` is, as a `K`-algebra, the
dependent product over the disjoint union `I ⊕ J`.  This is `Equiv.sumPiEquivProdPi` promoted to an
`AlgEquiv`; it turns a binary product of "products of field factors" into a single product of field
factors, which is what feeds `Algebra.Etale.iff_exists_algEquiv_prod`. -/
noncomputable def prodPiSumAlgEquiv {I J : Type u} (P : I → Type u) (Q : J → Type u)
    [∀ i, Field (P i)] [∀ i, Algebra K (P i)] [∀ j, Field (Q j)] [∀ j, Algebra K (Q j)] :
    ((∀ i, P i) × (∀ j, Q j)) ≃ₐ[K] ∀ k : I ⊕ J, Sum.elim P Q k :=
  (AlgEquiv.ofBijective (sumPiToProdPiAlgHom (Sum.elim P Q))
    ((Equiv.sumPiEquivProdPi (Sum.elim P Q)).bijective)).symm

/-- **Finite étale algebras are closed under binary products.**  If `A` and `B` are finite étale over
a field `K`, so is `A × B`.  (In the opposite category this is closure under binary coproducts: the
disjoint union of two finite étale covers of `Spec K` is again one.) -/
instance Algebra.Etale.prod {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra.Etale K A] [Algebra.Etale K B] : Algebra.Etale K (A × B) := by
  obtain ⟨I, _, P, _, _, eA, hP⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  obtain ⟨J, _, Q, _, _, eB, hQ⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  refine (Algebra.Etale.iff_exists_algEquiv_prod K (A × B)).mpr
    ⟨I ⊕ J, inferInstance, Sum.elim P Q, inferInstance, inferInstance,
      (eA.prodCongr eB).trans (prodPiSumAlgEquiv P Q), ?_⟩
  rintro (i | j)
  · exact ⟨(hP i).1, (hP i).2⟩
  · exact ⟨(hQ j).1, (hQ j).2⟩

/-- A finite étale algebra over a field is finite-dimensional: it is a finite product of finite
separable field extensions (`iff_exists_algEquiv_prod`), and a finite product of finite modules is
finite. -/
theorem etale_moduleFinite (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B] :
    Module.Finite K B := by
  obtain ⟨I, _, Ai, _, _, e, hAi⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp inferInstance
  haveI : Fintype I := Fintype.ofFinite I
  haveI : ∀ i, Module.Finite K (Ai i) := fun i => (hAi i).1
  haveI : Module.Finite K (∀ i, Ai i) := Module.Finite.pi
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- **Étale algebras over a field descend the base along an intermediate étale algebra.**  If `A` and
`B` are finite étale over a field `K` and `A → B` is a `K`-algebra map (so `K → A → B` is a scalar
tower), then `B` is étale over `A`.  Formal étaleness cancels on the left
(`FormallyEtale.of_restrictScalars`, since `A` is unramified over `K`); finite presentation over `A`
holds because `B` is module-finite over the Noetherian ring `A`.  This is the algebraic engine behind
pushouts of covers: it lets a pushout `B ⊗_A C` be handled by base change of `B/A` along `C`. -/
theorem etale_of_isScalarTower (A B : Type u) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [Algebra.Etale K A] [Algebra.Etale K B] :
    Algebra.Etale A B where
  formallyEtale := Algebra.FormallyEtale.of_restrictScalars (R := K)
  finitePresentation := by
    haveI : Module.Finite K B := etale_moduleFinite B
    haveI : Module.Finite A B := Module.Finite.of_restrictScalars_finite K A B
    haveI : Module.Finite K A := etale_moduleFinite A
    haveI : IsNoetherianRing A := IsNoetherianRing.of_finite K A
    exact (Algebra.FinitePresentation.of_finiteType (R := A) (A := B)).mp inferInstance

/-- **Finite étale algebras are closed under tensor products.**  If `A` and `B` are finite étale over
a field `K`, so is `A ⊗[K] B`.  (In the opposite category this is closure under fibre products /
pullbacks: the fibre product of two finite étale covers of `Spec K` over `Spec K` is again one.)  The
tensor product `A ⊗[K] B` is étale over `A` by base change of `B / K`, and `A` is étale over `K`, so
it is étale over `K` by composition. -/
instance Algebra.Etale.tensorProduct {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] [Algebra.Etale K A] [Algebra.Etale K B] : Algebra.Etale K (A ⊗[K] B) :=
  Algebra.Etale.comp K A (A ⊗[K] B)

end Rigidity.RET.Etale
