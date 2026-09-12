/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorShrink

/-!
# An invariant valuation lifts to an invariant tensor once one class is killed

A group acts on an abelian group carrying a valuation onto the free abelian group on a set of
places it permutes, and on a module.  A tensor whose valuation is *invariant* need not itself be
invariant: the difference between its translate and itself has vanishing valuation, so it lies in
the kernel of the valuation tensored with the module, and the resulting one cocycle with
coefficients in that kernel is the obstruction.  **When a homomorphism of the module kills the
class of that cocycle, the pushed forward tensor may be corrected to an invariant one with the same
valuation.**

In the intended reading the abelian group is the multiplicative group of a number field modulo
exponent-th powers, the places are the primes outside a finite set, the kernel of the valuation is
the group of units for that set, and the module is a layer of a tower whose homomorphisms may be
shrunk at will.  The prescribed valuation is a divisor built equivariantly out of the named places
— the orbit sum of a value carried by the decomposition subgroup — and the conclusion is a family
of radicands permuted by the group, which is exactly what a Kummer assembly consumes.

The obstruction lives with coefficients in the units for a finite set, a finitely generated group
fixed before the tower is chosen, so one shrinking suffices: the class is named first and the
homomorphism afterwards.

## Main definitions

* `InverseGalois.CFT.tensorInvariantCocycle`: the obstruction cocycle of a tensor with invariant
  valuation, with coefficients in the kernel of the valuation.
* `InverseGalois.CFT.tensorInvariantClass`: its class in the first cohomology.

## Main results

* `InverseGalois.CFT.exists_invariant_tensorCoeff_of_eq_sub`: **a tensor whose obstruction becomes
  a coboundary after a homomorphism of the module is corrected to an invariant one with the same
  valuation.**
* `InverseGalois.CFT.exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero`: **the same,
  read off the vanishing of the class rather than of a chosen cocycle.**

## Tags

group cohomology, permutation module, S-unit, tensor product, divisor, descent
-/

set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory MulAction TensorProduct groupCohomology

section Invariant

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
  [MulDistribMulAction Q C']
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)

/-! ### The obstruction to invariance -/

section Cocycle

omit [MulAction Q X] [IsStableSubgroup Q B] in
variable (C) in
include hg hB in
/-- The difference between the translate of a tensor whose valuation is invariant and the tensor
itself has vanishing valuation, hence comes from the kernel of the valuation. -/
theorem mem_range_tensorSubIncl_smul_sub
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t)
    (σ : Q) : σ • t - t ∈ LinearMap.range (tensorSubIncl C B) := by
  rw [range_tensorSubIncl g hg hB, LinearMap.mem_ker, ← tensorVal_eq_zero_iff, map_sub, ht σ,
    sub_self]

variable (C) in
/-- **The obstruction cocycle of a tensor whose valuation is invariant**, with coefficients in the
kernel of the valuation: at an element of the group it is the unique preimage of the difference
between the translate of the tensor and the tensor itself. -/
noncomputable def tensorInvariantCocycle
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t)
    (σ : Q) : Additive ↥B ⊗[ℤ] Additive C :=
  (mem_range_tensorSubIncl_smul_sub C g B hg hB ht σ).choose

omit [MulAction Q X] [IsStableSubgroup Q B] in
variable (C) in
@[simp]
theorem tensorSubIncl_tensorInvariantCocycle
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t)
    (σ : Q) :
    tensorSubIncl C B (tensorInvariantCocycle C g B hg hB ht σ) = σ • t - t :=
  (mem_range_tensorSubIncl_smul_sub C g B hg hB ht σ).choose_spec

omit [MulAction Q X] in
variable (C) in
/-- **The obstruction of a tensor whose valuation is invariant is a one cocycle.**  The inclusion
of the kernel of the valuation stays injective after tensoring, so the identity may be read on the
differences themselves, where it is the identity of a principal crossed homomorphism. -/
theorem mem_cocycles₁_tensorInvariantCocycle
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    tensorInvariantCocycle C g B hg hB ht ∈
      cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) := by
  rw [mem_cocycles₁_iff]
  intro σ τ
  show tensorInvariantCocycle C g B hg hB ht (σ * τ)
    = σ • tensorInvariantCocycle C g B hg hB ht τ + tensorInvariantCocycle C g B hg hB ht σ
  refine tensorSubIncl_injective g hg hB ?_
  rw [tensorSubIncl_tensorInvariantCocycle, map_add, tensorSubIncl_smul,
    tensorSubIncl_tensorInvariantCocycle, tensorSubIncl_tensorInvariantCocycle, smul_sub,
    ← mul_smul]
  abel

variable (C) in
/-- **The class of the obstruction of a tensor whose valuation is invariant.**  It vanishes exactly
when the tensor may be corrected to an invariant one by an element of the kernel of the
valuation. -/
noncomputable def tensorInvariantClass
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t) :
    H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) :=
  H1π _ ⟨tensorInvariantCocycle C g B hg hB ht, mem_cocycles₁_tensorInvariantCocycle C g B hg hB ht⟩

end Cocycle

/-! ### The correction -/

section Correct

omit [MulAction Q X] [MulDistribMulAction Q C] in
include hB in
/-- **A tensor whose obstruction becomes a coboundary after a homomorphism of the module is
corrected to an invariant one with the same valuation.**  Subtracting the coboundary makes the
translate agree with the tensor, and the correction lies in the kernel of the valuation, so it
changes nothing there. -/
theorem exists_invariant_tensorCoeff_of_eq_sub (φ : C →* C')
    {t : Additive A ⊗[ℤ] Additive C} {b : Additive ↥B ⊗[ℤ] Additive C'}
    (hb : ∀ σ : Q, σ • tensorCoeff A φ t - tensorCoeff A φ t
      = tensorSubIncl C' B (σ • b - b)) :
    ∃ s : Additive A ⊗[ℤ] Additive C',
      (∀ σ : Q, σ • s = s) ∧
      ∀ x : X, tensorVal C' g s x = Additive.ofMul (φ (tensorVal C g t x).toMul) := by
  refine ⟨tensorCoeff A φ t - tensorSubIncl C' B b, fun σ => ?_, fun x => ?_⟩
  · have h := hb σ
    rw [map_sub, tensorSubIncl_smul] at h
    rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
    exact h
  · have hzero : tensorVal C' g (tensorSubIncl C' B b) = 0 :=
      (tensorVal_eq_zero_iff C' g _).2 (rTensor_tensorSubIncl_eq_zero g hB b)
    rw [map_sub, Finsupp.sub_apply, hzero, Finsupp.coe_zero, Pi.zero_apply, sub_zero,
      tensorVal_tensorCoeff]

omit [MulAction Q X] in
include hg in
/-- **A tensor whose obstruction class is killed by a homomorphism of the module is corrected to an
invariant one with the same valuation.**  The class of the pushed forward obstruction is the
pushed forward class, so its vanishing hands back the element trivialising it, and the correction
is the inclusion of that element. -/
theorem exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero (φ : C →* C')
    (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w)
    {t : Additive A ⊗[ℤ] Additive C} (ht : ∀ σ : Q, tensorVal C g (σ • t) = tensorVal C g t)
    (hzero : (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := ↥B) Q φ hφ) 1).hom
      (tensorInvariantClass C g B hg hB ht) = 0) :
    ∃ s : Additive A ⊗[ℤ] Additive C',
      (∀ σ : Q, σ • s = s) ∧
      ∀ x : X, tensorVal C' g s x = Additive.ofMul (φ (tensorVal C g t x).toMul) := by
  rw [tensorInvariantClass, H1π_comp_map_apply, H1π_eq_zero_iff] at hzero
  obtain ⟨b, hb⟩ : ∃ b : Additive ↥B ⊗[ℤ] Additive C',
      ∀ σ : Q, σ • b - b = tensorCoeff ↥B φ (tensorInvariantCocycle C g B hg hB ht σ) := by
    obtain ⟨b, hb⟩ := hzero
    exact ⟨b, fun σ => congrFun hb σ⟩
  refine exists_invariant_tensorCoeff_of_eq_sub g B hB φ (b := b) fun σ => ?_
  rw [hb σ, ← tensorCoeff_tensorSubIncl, tensorSubIncl_tensorInvariantCocycle, map_sub,
    tensorCoeff_smul _ hφ]

end Correct

end Invariant

/-! ### The valuation is equivariant -/

section Equivariance

variable {Q : Type*} [Group Q] {A : Type*} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type*) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type*} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))

/-- **The valuation of a tensor is equivariant** as soon as the valuation of the group itself is:
the value of the translated tensor at the translated place is the translate of the value. -/
theorem tensorVal_smul_apply
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) (σ • x) = g (Additive.ofMul a) x)
    (σ : Q) (t : Additive A ⊗[ℤ] Additive C) (x : X) :
    tensorVal C g (σ • t) (σ • x) = Additive.ofMul (σ • (tensorVal C g t x).toMul) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
      show tensorVal C g (Additive.ofMul (σ • u.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • v.toMul)) (σ • x)
        = Additive.ofMul (σ • (tensorVal C g
            (Additive.ofMul u.toMul ⊗ₜ[ℤ] Additive.ofMul v.toMul) x).toMul)
      rw [tensorVal_tmul_apply, tensorVal_tmul_apply, hgeq]
      simp [← ofMul_zpow]
      exact (map_zpow (MulDistribMulAction.toMonoidHom C σ) (Additive.toMul v) _).symm
  | add z z' hz hz' => simp [smul_add, hz, hz', smul_mul']

/-- A tensor whose valuation is the equivariant family carried by one orbit has invariant
valuation, so it feeds the descent above with no further hypothesis. -/
theorem tensorVal_smul_eq_of_eq
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) (σ • x) = g (Additive.ofMul a) x)
    {t : Additive A ⊗[ℤ] Additive C} {D : X →₀ Additive C} (hD : tensorVal C g t = D)
    (hDeq : ∀ (σ : Q) (x : X), D (σ • x) = Additive.ofMul (σ • (D x).toMul)) (σ : Q) :
    tensorVal C g (σ • t) = tensorVal C g t := by
  refine Finsupp.ext fun x => ?_
  have hx : σ • (σ⁻¹ • x) = x := smul_inv_smul σ x
  calc tensorVal C g (σ • t) x
      = tensorVal C g (σ • t) (σ • (σ⁻¹ • x)) := by rw [hx]
    _ = Additive.ofMul (σ • (tensorVal C g t (σ⁻¹ • x)).toMul) :=
        tensorVal_smul_apply C g hgeq σ t (σ⁻¹ • x)
    _ = Additive.ofMul (σ • (D (σ⁻¹ • x)).toMul) := by rw [hD]
    _ = D (σ • (σ⁻¹ • x)) := (hDeq σ (σ⁻¹ • x)).symm
    _ = tensorVal C g t x := by rw [hx, hD]

end Equivariance

end InverseGalois.CFT
