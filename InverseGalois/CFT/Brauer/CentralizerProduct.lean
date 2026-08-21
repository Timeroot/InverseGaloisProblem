import Mathlib
import InverseGalois.CFT.Brauer.Centralizer
import InverseGalois.CFT.Brauer.Group

/-!
# The centralizer product theorem

Let `K` be a field, `E` a finite-dimensional central simple `K`-algebra and `B` a `K`-subalgebra
of `E` which is itself central simple over `K`. Write `C := Subalgebra.centralizer K (B : Set E)`.
Multiplication inside `E` gives a `K`-algebra homomorphism `↥B ⊗[K] ↥C →ₐ[K] E`, and this file
shows that it is an isomorphism: the source is a simple ring because `↥B` is central and `↥C` is
simple, so the map is injective, and the centralizer theorem says the two sides have the same
`K`-dimension. As a consequence the centralizer `↥C` is again central over `K`, and the class of
`E` in the Brauer group of `K` is the product of the classes of `↥B` and of `↥C`.

## Main results

* `InverseGalois.CFT.Centralizer.tensorCentralizerHom`: the multiplication map
  `↥B ⊗[K] ↥C →ₐ[K] E`.
* `InverseGalois.CFT.Centralizer.tensorCentralizerHom_bijective`: that map is bijective.
* `InverseGalois.CFT.Centralizer.tensorCentralizerEquiv`: **the centralizer product theorem**,
  the resulting isomorphism `↥B ⊗[K] ↥C ≃ₐ[K] E`.
* `InverseGalois.CFT.Centralizer.isCentral_centralizer`: the centralizer of a central simple
  subalgebra of a central simple algebra is central.
* `InverseGalois.CFT.Centralizer.brauerClass_mul`: in the Brauer group of `K`, the product of the
  classes of `↥B` and `↥C` is the class of `E`.

## Tags

central simple algebra, centralizer, Brauer group
-/

universe u v

open scoped TensorProduct

open Module

namespace InverseGalois.CFT

namespace Centralizer

section Product

variable {K : Type u} {E : Type v} [Field K] [Ring E] [Algebra K E]
variable (B : Subalgebra K E)

/-- Multiplication in `E` of an element of a subalgebra `B` with an element of the centralizer
of `B`, as a `K`-algebra homomorphism out of the tensor product. -/
noncomputable def tensorCentralizerHom :
    ↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set E)) →ₐ[K] E :=
  Algebra.TensorProduct.lift B.val (Subalgebra.centralizer K (B : Set E)).val
    fun b c ↦ c.2 (b : E) b.2

/-- The multiplication map sends a pure tensor to the product of its two components. -/
@[simp]
theorem tensorCentralizerHom_tmul (b : ↥B) (c : ↥(Subalgebra.centralizer K (B : Set E))) :
    tensorCentralizerHom B (b ⊗ₜ[K] c) = (b : E) * (c : E) :=
  Algebra.TensorProduct.lift_tmul _ _ _ b c

variable [Algebra.IsCentral K E] [IsSimpleRing E] [FiniteDimensional K E]
variable [Algebra.IsCentral K ↥B] [IsSimpleRing ↥B]

/-- The tensor product of a central simple subalgebra with its centralizer is a simple ring. -/
theorem isSimpleRing_tensor_centralizer :
    IsSimpleRing (↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set E))) :=
  haveI := isSimpleRing_centralizer B
  IsSimpleRing.tensorProduct_of_isCentral

/-- The multiplication map from the tensor product of a central simple subalgebra with its
centralizer is injective. -/
theorem tensorCentralizerHom_injective : Function.Injective (tensorCentralizerHom B) :=
  haveI := isSimpleRing_tensor_centralizer B
  (tensorCentralizerHom B).toRingHom.injective

/-- **The centralizer product theorem**: for a central simple subalgebra `B` of a
finite-dimensional central simple `K`-algebra `E`, multiplication identifies the tensor product
of `B` with its centralizer with the whole of `E`. -/
theorem tensorCentralizerHom_bijective : Function.Bijective (tensorCentralizerHom B) := by
  have hdim : finrank K (↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set E))) = finrank K E := by
    rw [Module.finrank_tensorProduct, finrank_mul_finrank_centralizer B]
  exact ⟨tensorCentralizerHom_injective B,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (tensorCentralizerHom_injective B)⟩

/-- **The centralizer product theorem**, as an isomorphism: a finite-dimensional central simple
`K`-algebra `E` is the tensor product of a central simple subalgebra `B` with the centralizer
of `B` in `E`. -/
noncomputable def tensorCentralizerEquiv :
    ↥B ⊗[K] ↥(Subalgebra.centralizer K (B : Set E)) ≃ₐ[K] E :=
  AlgEquiv.ofBijective (tensorCentralizerHom B) (tensorCentralizerHom_bijective B)

/-- The isomorphism of the centralizer product theorem sends a pure tensor to the product of its
two components. -/
@[simp]
theorem tensorCentralizerEquiv_tmul (b : ↥B) (c : ↥(Subalgebra.centralizer K (B : Set E))) :
    tensorCentralizerEquiv B (b ⊗ₜ[K] c) = (b : E) * (c : E) :=
  tensorCentralizerHom_tmul B b c

/-- An element of the centralizer of `B` which in addition commutes with the whole centralizer
of `B` commutes with every element of `E`. -/
theorem commute_of_mem_centralizer {c : E} (hcB : c ∈ Subalgebra.centralizer K (B : Set E))
    (hcC : ∀ d ∈ Subalgebra.centralizer K (B : Set E), d * c = c * d) (x : E) :
    x * c = c * x := by
  obtain ⟨t, rfl⟩ := (tensorCentralizerHom_bijective B).2 x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b d =>
      have h1 : (d : E) * c = c * (d : E) := hcC (d : E) d.2
      have h2 : (b : E) * c = c * (b : E) := hcB (b : E) b.2
      rw [tensorCentralizerHom_tmul, mul_assoc, h1, ← mul_assoc, h2, mul_assoc]
  | add t₁ t₂ h₁ h₂ => rw [map_add, add_mul, mul_add, h₁, h₂]

/-- The centralizer of a central simple subalgebra of a finite-dimensional central simple
`K`-algebra is itself central over `K`. -/
instance isCentral_centralizer :
    Algebra.IsCentral K ↥(Subalgebra.centralizer K (B : Set E)) where
  out c hc := by
    have hcC : ∀ d ∈ Subalgebra.centralizer K (B : Set E), d * (c : E) = (c : E) * d :=
      fun d hd ↦ congrArg Subtype.val (Subalgebra.mem_center_iff.mp hc ⟨d, hd⟩)
    have hmem : (c : E) ∈ Subalgebra.center K E :=
      Subalgebra.mem_center_iff.mpr (commute_of_mem_centralizer B c.2 hcC)
    obtain ⟨k, hk⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out (K := K) hmem)
    exact Algebra.mem_bot.mpr ⟨k, Subtype.ext hk⟩

end Product

section BrauerClass

variable {K : Type u} [Field K]

/-- A finite-dimensional central simple `K`-algebra, packaged as an object of `CSA K`. -/
def csaSelf (E : Type u) [Ring E] [Algebra K E] [Algebra.IsCentral K E] [IsSimpleRing E]
    [FiniteDimensional K E] : CSA.{u, u} K where
  toAlgCat := AlgCat.of K E

variable {E : Type u} [Ring E] [Algebra K E]
variable [Algebra.IsCentral K E] [IsSimpleRing E] [FiniteDimensional K E]
variable (B : Subalgebra K E) [Algebra.IsCentral K ↥B] [IsSimpleRing ↥B]

/-- A central simple subalgebra of a finite-dimensional central simple `K`-algebra, packaged as
an object of `CSA K`. -/
def csaOfSubalgebra : CSA.{u, u} K where
  toAlgCat := AlgCat.of K ↥B

/-- The centralizer of a central simple subalgebra of a finite-dimensional central simple
`K`-algebra, packaged as an object of `CSA K`. -/
def csaCentralizer : CSA.{u, u} K where
  toAlgCat := AlgCat.of K ↥(Subalgebra.centralizer K (B : Set E))
  isSimple := isSimpleRing_centralizer B

/-- In the Brauer group of `K`, the product of the class of a central simple subalgebra `B` and
the class of its centralizer is the class of the ambient algebra. -/
theorem brauerClass_mul :
    (⟦csaOfSubalgebra B⟧ : BrauerGroup K) * ⟦csaCentralizer B⟧ = ⟦csaSelf E⟧ := by
  rw [BrauerGroup.mk_mul]
  exact Quotient.sound (IsBrauerEquivalent.of_algEquiv
    (A := CSA.tensor (csaOfSubalgebra B) (csaCentralizer B)) (B := csaSelf E)
    (tensorCentralizerEquiv B))

end BrauerClass

end Centralizer

end InverseGalois.CFT
