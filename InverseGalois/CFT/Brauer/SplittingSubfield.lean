import Mathlib
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.CentralizerProduct
import InverseGalois.CFT.Brauer.Split
import InverseGalois.CFT.Brauer.Group
import InverseGalois.CFT.Brauer.BaseChange
import InverseGalois.CFT.Brauer.TensorSimple

/-!
# Splitting fields sit inside a central simple algebra of the expected dimension

Let `L / K` be a finite extension of fields. This file shows that every class of the relative
Brauer group `Br(L / K)` is represented by a central simple `K`-algebra of dimension `[L : K]²`
which contains a copy of `L`.

The construction goes through the centralizer theorem. Let `A` be a central simple `K`-algebra
split by `L`, so that `L ⊗[K] A ≃ₐ[L] Mₙ(L)`. The space `V = Lⁿ` is then a module over `A`
through `A → L ⊗[K] A ≃ Mₙ(L) ≃ End_L V`, and this action commutes with the action of `L` by
scalars. Regarding `V` as a `K`-vector space, its endomorphism algebra `E = End_K V` is a matrix
algebra over `K`, the image `B` of `A` in `E` is a central simple subalgebra isomorphic to `A`,
and the scalar action of `L` lands in the centralizer `C` of `B`. The centralizer theorem makes
`C` central simple of dimension `[L : K]²`, and the centralizer product theorem identifies the
class of `C` with the inverse of the class of `A`. Feeding the opposite algebra `Aᵐᵒᵖ` into this
construction produces a representative of the class of `A` itself.

## Main results

* `InverseGalois.CFT.endRestrictScalars`: restriction of scalars, as a `K`-algebra homomorphism
  from `End_L V` to `End_K V`.
* `InverseGalois.CFT.lsmul_mem_centralizer`: the scalar action of `L` on `V` centralizes any set
  of `L`-linear endomorphisms of `V`.
* `InverseGalois.CFT.exists_csa_inv_of_algEquiv_matrix`: a central simple algebra split by `L`
  has its inverse class represented by a central simple algebra of dimension `[L : K]²`
  containing `L`.
* `InverseGalois.CFT.exists_csa_finrank_sq_of_mem_relative`: **every class of the relative Brauer
  group `Br(L / K)` is represented by a central simple `K`-algebra of dimension `[L : K]²` that
  contains `L`.**

## Tags

Brauer group, central simple algebra, splitting field, centralizer
-/

universe u

open scoped TensorProduct

open Module

attribute [instance] Brauer.CSA_Setoid

namespace InverseGalois.CFT

/-! ### Restriction of scalars on endomorphism algebras -/

section RestrictScalars

variable (R S M : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M] [SMulCommClass S R M]

/-- Restriction of scalars from `S` to `R`, as a homomorphism of `R`-algebras from the algebra of
`S`-linear endomorphisms of `M` to the algebra of `R`-linear endomorphisms of `M`. -/
def endRestrictScalars : Module.End S M →ₐ[R] Module.End R M where
  toFun f := f.restrictScalars R
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Restriction of scalars does not change the underlying function of an endomorphism. -/
@[simp]
theorem endRestrictScalars_apply (f : Module.End S M) (m : M) :
    endRestrictScalars R S M f m = f m := rfl

/-- Scalar multiplication by an element of `S` commutes with every `R`-linear endomorphism of `M`
which is the restriction of scalars of an `S`-linear one. -/
theorem lsmul_mem_centralizer (l : S) (s : Set (Module.End R M))
    (hs : ∀ f ∈ s, ∃ g : Module.End S M, f = endRestrictScalars R S M g) :
    Algebra.lsmul R R M l ∈ Subalgebra.centralizer R s := by
  rw [Subalgebra.mem_centralizer_iff]
  intro f hf
  obtain ⟨g, rfl⟩ := hs f hf
  ext v
  simp

end RestrictScalars

/-! ### The construction -/

section Construction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- A central simple `K`-algebra `A` split by a finite extension `L / K`, say by an isomorphism
`L ⊗[K] A ≃ₐ[L] Mₙ(L)`, has the inverse of its Brauer class represented by a central simple
`K`-algebra of dimension `[L : K]²` which contains a copy of `L`: the centralizer of the image of
`A` in the endomorphism algebra of `Lⁿ` viewed as a `K`-vector space. -/
theorem exists_csa_inv_of_algEquiv_matrix (A : CSA.{u, u} K) {n : ℕ} (hn : n ≠ 0)
    (φ : L ⊗[K] (A : Type u) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    ∃ (C : CSA.{u, u} K) (_ : L →ₐ[K] (C : Type u)),
      (⟦C⟧ : BrauerGroup K) = (⟦A⟧ : BrauerGroup K)⁻¹ ∧
        finrank K (C : Type u) = finrank K L * finrank K L := by
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  have hV : finrank K (Fin n → L) = n * finrank K L := by
    rw [Module.finrank_pi_fintype K (M := fun _ : Fin n => L)]
    simp
  have hLpos : 0 < finrank K L := Module.finrank_pos
  have hVpos : 0 < finrank K (Fin n → L) := by
    rw [hV]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hn) hLpos
  haveI : Nonempty (Fin (finrank K (Fin n → L))) := Fin.pos_iff_nonempty.mp hVpos
  -- the ambient algebra `E = End_K (Lⁿ)` is a matrix algebra over `K`
  have eE : Module.End K (Fin n → L) ≃ₐ[K]
      Matrix (Fin (finrank K (Fin n → L))) (Fin (finrank K (Fin n → L))) K :=
    LinearMap.toMatrixAlgEquiv (Module.finBasis K (Fin n → L))
  haveI : IsSimpleRing (Module.End K (Fin n → L)) :=
    IsSimpleRing.of_ringEquiv eE.symm.toRingEquiv inferInstance
  -- the action of `A` on `Lⁿ`, factored through the `L`-linear endomorphisms
  obtain ⟨ρ, hρfac⟩ : ∃ ρ : (A : Type u) →ₐ[K] Module.End K (Fin n → L),
      ∀ a : (A : Type u), ∃ g : Module.End L (Fin n → L),
        ρ a = endRestrictScalars K L (Fin n → L) g :=
    ⟨((endRestrictScalars K L (Fin n → L)).comp
        (((Matrix.toLinAlgEquiv (Pi.basisFun L (Fin n))).toAlgHom.comp
          φ.toAlgHom).restrictScalars K)).comp Algebra.TensorProduct.includeRight,
      fun a => ⟨_, rfl⟩⟩
  have hinj : Function.Injective ρ := ρ.toRingHom.injective
  haveI : IsSimpleRing ρ.range :=
    IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective ρ hinj).toRingEquiv inferInstance
  haveI : Algebra.IsCentral K ρ.range :=
    Algebra.IsCentral.of_algEquiv K (A : Type u) ρ.range (AlgEquiv.ofInjective ρ hinj)
  -- dimension count
  have hArank : finrank K (A : Type u) = n * n := by
    have h1 : finrank L (L ⊗[K] (A : Type u)) = finrank K (A : Type u) :=
      Module.finrank_baseChange
    have h2 : finrank L (L ⊗[K] (A : Type u)) = n * n := by
      rw [φ.toLinearEquiv.finrank_eq, Module.finrank_matrix]
      simp
    omega
  have hBrank : finrank K ρ.range = n * n := by
    rw [← hArank]
    exact ((AlgEquiv.ofInjective ρ hinj).toLinearEquiv.finrank_eq).symm
  have hErank : finrank K (Module.End K (Fin n → L)) = (n * finrank K L) * (n * finrank K L) := by
    rw [Module.finrank_linearMap, hV]
  have hcent := Centralizer.finrank_mul_finrank_centralizer
    (K := K) (A := Module.End K (Fin n → L)) ρ.range
  have hCrank : finrank K
      (Subalgebra.centralizer K (ρ.range : Set (Module.End K (Fin n → L))))
        = finrank K L * finrank K L := by
    have hnn : 0 < n * n := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hn)
    refine Nat.eq_of_mul_eq_mul_left hnn ?_
    rw [← hBrank, hcent, hErank, hBrank]
    ring
  -- the copy of `L` inside the centralizer
  have hmem : ∀ l : L, Algebra.lsmul K K (Fin n → L) l ∈
      Subalgebra.centralizer K (ρ.range : Set (Module.End K (Fin n → L))) := by
    intro l
    refine lsmul_mem_centralizer K L (Fin n → L) l _ ?_
    rintro f ⟨a, rfl⟩
    exact hρfac a
  refine ⟨Centralizer.csaCentralizer ρ.range,
    AlgHom.codRestrict (Algebra.lsmul K K (Fin n → L)) _ hmem, ?_, hCrank⟩
  -- the Brauer class
  have hmul := Centralizer.brauerClass_mul (K := K) (E := Module.End K (Fin n → L)) ρ.range
  have hone : (⟦Centralizer.csaSelf (K := K) (Module.End K (Fin n → L))⟧ : BrauerGroup K) = 1 :=
    BrauerGroup.mk_eq_one_of_algEquiv_matrix hVpos.ne' eE
  have hB : (⟦Centralizer.csaOfSubalgebra ρ.range⟧ : BrauerGroup K) = ⟦A⟧ :=
    Quotient.sound (IsBrauerEquivalent.of_algEquiv
      (A := Centralizer.csaOfSubalgebra ρ.range) (B := A) (AlgEquiv.ofInjective ρ hinj).symm)
  rw [hB, hone] at hmul
  exact eq_inv_of_mul_eq_one_right hmul

/-- **Every class of the relative Brauer group `Br(L / K)` is represented by a central simple
`K`-algebra of dimension `[L : K]²` containing a copy of `L`.** -/
theorem exists_csa_finrank_sq_of_mem_relative (A : CSA.{u, u} K)
    (hA : (⟦A⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L) :
    ∃ (B : CSA.{u, u} K) (_ : L →ₐ[K] (B : Type u)),
      (⟦B⟧ : BrauerGroup K) = ⟦A⟧ ∧
        Module.finrank K (B : Type u) = Module.finrank K L * Module.finrank K L := by
  have hop : (⟦CSA.op A⟧ : BrauerGroup K) ∈ BrauerGroup.relative K L := by
    rw [← BrauerGroup.mk_inv]
    exact Subgroup.inv_mem _ hA
  obtain ⟨n, hn, ⟨φ⟩⟩ := (BrauerGroup.mem_relative_iff_algEquiv_matrix (CSA.op A)).mp hop
  obtain ⟨C, emb, hC, hCrank⟩ := exists_csa_inv_of_algEquiv_matrix (CSA.op A) hn φ
  refine ⟨C, emb, ?_, hCrank⟩
  rw [hC, ← BrauerGroup.mk_inv, inv_inv]

end Construction

end InverseGalois.CFT
