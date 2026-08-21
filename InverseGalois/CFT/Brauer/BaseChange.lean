import Mathlib
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.TensorSimple

/-!
# Base change of central simple algebras and the relative Brauer group

Let `L / K` be an extension of fields and let `A` be a finite-dimensional central simple
`K`-algebra. Then `L ⊗[K] A` is a finite-dimensional central simple `L`-algebra, and the
assignment `⟦A⟧ ↦ ⟦L ⊗[K] A⟧` is a homomorphism of Brauer groups `BrauerGroup K →* BrauerGroup L`.
Its kernel is the relative Brauer group `Br(L / K)`, consisting of the classes that are split
by `L`.

Centrality of `L ⊗[K] A` over `L` is deduced from `TensorSimple.exists_one_tmul`: after commuting
the two factors, an element of `A ⊗[K] L` that centralizes the image of `A` is of the form
`1 ⊗ₜ l`. Simplicity is `IsSimpleRing.tensorProduct_of_isCentral` transported along
`Algebra.TensorProduct.comm`, `L` being a simple ring. Compatibility with tensor products and
with matrix algebras rests on the associativity isomorphism `Algebra.TensorProduct.assoc`, which
is available over a base field intermediate between `K` and the tensor factors.

Since the group structure on `BrauerGroup` is stated for algebras whose carrier lives in the
universe of the base field, the Brauer-group-level statements keep `K` and `L` in the same
universe.

## Main definitions

* `CSA.baseChange`: the base change `L ⊗[K] A` of a finite-dimensional central simple algebra.
* `BrauerGroup.baseChangeHom`: base change as a homomorphism of Brauer groups.
* `BrauerGroup.relative`: the relative Brauer group `Br(L / K)`, the kernel of base change.
* `Algebra.TensorProduct.baseChangeTensor`, `Algebra.TensorProduct.baseChangeMatrix`,
  `Algebra.TensorProduct.baseChangeTower`: the algebra isomorphisms underlying the compatibility
  of base change with tensor products, matrix algebras and towers of fields.

## Main results

* `Algebra.IsCentral.baseChange`, `IsSimpleRing.baseChange`: `L ⊗[K] A` is a central simple
  `L`-algebra.
* `CSA.baseChange_tensor`, `CSA.baseChange_one`, `IsBrauerEquivalent.baseChange`: base change is
  multiplicative, unital, and compatible with Brauer equivalence.
* `BrauerGroup.mem_relative_iff`, `BrauerGroup.mk_mem_relative_of_algEquiv_matrix`: criteria for
  membership in the relative Brauer group.
* `BrauerGroup.baseChangeHom_self`, `BrauerGroup.baseChangeHom_comp`: functoriality of base change
  in the field.

## Tags

Brauer group, central simple algebra, base change, splitting field
-/

universe u v

open scoped TensorProduct

section Central

variable (K L A : Type*) [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

/-- Extending scalars along a field extension preserves centrality. -/
instance Algebra.IsCentral.baseChange [Algebra.IsCentral K A] :
    Algebra.IsCentral L (L ⊗[K] A) where
  out x hx := by
    rw [Algebra.mem_bot]
    rw [Subalgebra.mem_center_iff] at hx
    set e := Algebra.TensorProduct.comm K L A with he
    have hcomm : ∀ a : A, (a ⊗ₜ[K] (1 : L)) * e x = e x * (a ⊗ₜ[K] (1 : L)) := by
      intro a
      have h := congrArg e (hx ((1 : L) ⊗ₜ[K] a))
      simpa [he] using h
    obtain ⟨l, hl⟩ := TensorSimple.exists_one_tmul (Module.Free.chooseBasis K L) hcomm
    refine ⟨l, ?_⟩
    have hx' : x = e.symm ((1 : A) ⊗ₜ[K] l) := by rw [← hl, he]; simp
    rw [hx', he]
    simp [Algebra.TensorProduct.algebraMap_apply]

/-- Extending scalars along a field extension preserves simplicity of a central algebra. -/
instance IsSimpleRing.baseChange [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (L ⊗[K] A) :=
  IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm K L A).symm.toRingEquiv
    (IsSimpleRing.tensorProduct_of_isCentral (K := K) (A := A) (B := L))

end Central

section Equivs

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable (A B : Type*) [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- Base change turns a tensor product over `K` into a tensor product over `L`. -/
noncomputable def Algebra.TensorProduct.baseChangeTensor :
    L ⊗[K] (A ⊗[K] B) ≃ₐ[L] (L ⊗[K] A) ⊗[L] (L ⊗[K] B) :=
  (Algebra.TensorProduct.assoc K K L L A B).symm.trans <|
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L L (L ⊗[K] A)).symm
      AlgEquiv.refl).trans (Algebra.TensorProduct.assoc K L L (L ⊗[K] A) L B)

/-- `matrixEquivTensor`, upgraded to an isomorphism of `L`-algebras when the coefficient ring is
an `L`-algebra. -/
noncomputable def matrixEquivTensorBase (n : Type*) [Fintype n] [DecidableEq n] (C : Type*)
    [Ring C] [Algebra K C] [Algebra L C] [IsScalarTower K L C] :
    Matrix n n C ≃ₐ[L] C ⊗[K] Matrix n n K :=
  { matrixEquivTensor n K C with
    commutes' := fun l => by
      have h : (matrixEquivTensor n K C).symm (algebraMap L C l ⊗ₜ[K] (1 : Matrix n n K)) =
          algebraMap L (Matrix n n C) l := by
        rw [matrixEquivTensor_apply_symm]
        ext i j
        by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
      have hsymm := (matrixEquivTensor n K C).apply_symm_apply
        (algebraMap L C l ⊗ₜ[K] (1 : Matrix n n K))
      rw [h] at hsymm
      rw [Algebra.TensorProduct.algebraMap_apply]
      exact hsymm }

/-- Base change commutes with passing to matrix algebras. -/
noncomputable def Algebra.TensorProduct.baseChangeMatrix (n : Type*) [Fintype n] [DecidableEq n] :
    L ⊗[K] Matrix n n A ≃ₐ[L] Matrix n n (L ⊗[K] A) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n K A)).trans <|
    (Algebra.TensorProduct.assoc K K L L A (Matrix n n K)).symm.trans
      (matrixEquivTensorBase K L n (L ⊗[K] A)).symm

end Equivs

section CSA

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

/-- The base change of a finite-dimensional central simple `K`-algebra along a field extension
`L / K`, as a finite-dimensional central simple `L`-algebra. -/
noncomputable def CSA.baseChange (A : CSA.{u, v} K) : CSA.{u, max u v} L where
  toAlgCat := AlgCat.of L (L ⊗[K] A)

@[simp]
theorem CSA.coe_baseChange (A : CSA.{u, v} K) :
    (A.baseChange L : Type max u v) = (L ⊗[K] A) := rfl

/-- Base change is multiplicative: it takes a tensor product over `K` to a tensor product
over `L`. -/
theorem CSA.baseChange_tensor (A B : CSA.{u, v} K) :
    IsBrauerEquivalent ((CSA.tensor A B).baseChange L)
      (CSA.tensor (A.baseChange L) (B.baseChange L)) :=
  IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.baseChangeTensor K L A B)

/-- Base change takes the base field to the base field. -/
theorem CSA.baseChange_one : IsBrauerEquivalent ((CSA.one K).baseChange L) (CSA.one L) :=
  IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.rid K L L)

/-- Base change respects Brauer equivalence. -/
theorem IsBrauerEquivalent.baseChange {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (A.baseChange L) (B.baseChange L) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(Algebra.TensorProduct.baseChangeMatrix K L A (Fin n)).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl e).trans
      (Algebra.TensorProduct.baseChangeMatrix K L B (Fin m))⟩⟩

end CSA

namespace BrauerGroup

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

/-- Base change along a field extension `L / K`, as a homomorphism of Brauer groups. -/
noncomputable def baseChangeHom : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun := Quotient.map (CSA.baseChange L) fun _ _ h => h.baseChange L
  map_one' := Quotient.sound (CSA.baseChange_one L)
  map_mul' := by
    refine Quotient.ind fun A => Quotient.ind fun B => ?_
    exact Quotient.sound (CSA.baseChange_tensor L A B)

@[simp]
theorem baseChangeHom_mk (A : CSA.{u, u} K) :
    baseChangeHom L (⟦A⟧ : BrauerGroup K) = ⟦A.baseChange L⟧ := rfl

end BrauerGroup

namespace BrauerGroup

/-- The relative Brauer group `Br(L / K)`: the classes of central simple `K`-algebras that are
split by the extension `L / K`. -/
noncomputable def relative (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Subgroup (BrauerGroup.{u, u} K) := (baseChangeHom L).ker

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

/-- A class lies in the relative Brauer group exactly when the base-changed algebra is trivial
in the Brauer group of `L`. -/
theorem mem_relative_iff (A : CSA.{u, u} K) :
    (⟦A⟧ : BrauerGroup K) ∈ relative K L ↔ ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧
      Nonempty (Matrix (Fin n) (Fin n) (L ⊗[K] A) ≃ₐ[L] Matrix (Fin m) (Fin m) L) := by
  rw [relative, MonoidHom.mem_ker, baseChangeHom_mk, mk_eq_one_iff]
  rfl

/-- If the base-changed algebra is a matrix algebra over `L`, then the class of `A` is split
by `L`. -/
theorem mk_mem_relative_of_algEquiv_matrix {A : CSA.{u, u} K} {n : ℕ} (hn : n ≠ 0)
    (e : (L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) : (⟦A⟧ : BrauerGroup K) ∈ relative K L := by
  rw [relative, MonoidHom.mem_ker, baseChangeHom_mk]
  exact mk_eq_one_of_algEquiv_matrix hn e

end BrauerGroup

section Functoriality

/-- Base change along a tower `K → L → M`, on the level of algebras. -/
noncomputable def Algebra.TensorProduct.baseChangeTower (K L M : Type*) [Field K] [Field L]
    [Field M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] (A : Type*)
    [Ring A] [Algebra K A] : M ⊗[K] A ≃ₐ[M] M ⊗[L] (L ⊗[K] A) :=
  (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid L M M) AlgEquiv.refl).symm.trans
    (Algebra.TensorProduct.assoc K L M M L A)

namespace BrauerGroup

/-- Base change along the identity extension is the identity. -/
theorem baseChangeHom_self (K : Type u) [Field K] :
    baseChangeHom (K := K) K = MonoidHom.id (BrauerGroup.{u, u} K) :=
  MonoidHom.ext <| Quotient.ind fun A =>
    Quotient.sound (IsBrauerEquivalent.of_algEquiv (Algebra.TensorProduct.lid K A))

/-- Base change is functorial in the field: base changing along `K → M` agrees with base
changing along `K → L` and then along `L → M`. -/
theorem baseChangeHom_comp (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    (baseChangeHom (K := L) M).comp (baseChangeHom (K := K) L) = baseChangeHom (K := K) M :=
  MonoidHom.ext <| Quotient.ind fun A => Quotient.sound (IsBrauerEquivalent.of_algEquiv
    (Algebra.TensorProduct.baseChangeTower K L M A).symm)

end BrauerGroup

end Functoriality
