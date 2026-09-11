/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.KummerCoeff
import InverseGalois.CFT.Profinite.TwistAction

/-!
# Tensoring the units of a field with a module, along a valuation onto a free module

The units of a number field surject, by the vector of orders at the places outside a finite set,
onto the free abelian group on those places, and the kernel is the group of units for the set.  A
surjection onto a free abelian group splits, so the inclusion of the kernel is a **split**
monomorphism of abelian groups: there is a homomorphism back which restricts to the identity on the
kernel.  Everything then survives tensoring with an arbitrary module, with no flatness or derived
functors: the inclusion of the kernel stays injective, and its image is still the whole kernel of
the valuation.

The splitting is not equivariant — a choice of element with a prescribed order at one place has no
reason to respect the Galois action — but it does not need to be.  It is used only to correct a
cocycle, and the correction is by a coboundary, so the class is unchanged.

## Main definitions

* `InverseGalois.CFT.IsStableSubgroup`: a subgroup carried into itself by the action of the group.
* `InverseGalois.CFT.tensorSubIncl`: the inclusion of such a subgroup, tensored with a module.
* `InverseGalois.CFT.tensorSubInclRep`: **the same, as a morphism of representations.**
* `InverseGalois.CFT.tensorVal`: the valuation of a tensor, as a finitely supported family.

## Main results

* `InverseGalois.CFT.exists_addMonoidHom_add_eq_self`: **a surjection onto a free abelian group
  splits**, and the inclusion of its kernel is a retract.
* `InverseGalois.CFT.tensorSubIncl_injective`: **the inclusion of the kernel stays injective after
  tensoring.**
* `InverseGalois.CFT.range_tensorSubIncl`: **and its image is still the kernel of the valuation.**
* `InverseGalois.CFT.tensorVal_smul`: the valuation of a tensor is equivariant.

## Tags

tensor product, split exact sequence, S-unit, permutation module, Galois cohomology
-/

namespace InverseGalois.CFT

open CategoryTheory TensorProduct

/-! ### A subgroup carried into itself -/

/-- **A subgroup carried into itself by the action of the group.** -/
class IsStableSubgroup (Q : Type*) {A : Type*} [Group Q] [CommGroup A]
    [MulDistribMulAction Q A] (B : Subgroup A) : Prop where
  /-- The action carries an element of the subgroup to an element of the subgroup. -/
  smul_mem : ∀ (σ : Q) {a : A}, a ∈ B → σ • a ∈ B

section Stable

variable {Q : Type*} {A : Type*} [Group Q] [CommGroup A] [MulDistribMulAction Q A]
  (B : Subgroup A) [IsStableSubgroup Q B]

/-- **The action of the group on a subgroup it carries into itself.** -/
instance stableSubgroupMulDistribMulAction : MulDistribMulAction Q ↥B where
  smul σ b := ⟨σ • (b : A), IsStableSubgroup.smul_mem σ b.2⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_mul σ _ _ := Subtype.ext (smul_mul' σ _ _)
  smul_one σ := Subtype.ext (smul_one σ)

@[simp]
theorem coe_smul_stableSubgroup (σ : Q) (b : ↥B) : ((σ • b : ↥B) : A) = σ • (b : A) := rfl

end Stable

/-! ### Splitting a surjection onto a free abelian group -/

section Split

variable {A : Type*} [CommGroup A] {X : Type*}

/-- **A surjection of an abelian group onto the free abelian group on a set splits**, and the
splitting exhibits the kernel as a retract: there is a homomorphism back from the group onto the
kernel and a section of the surjection whose contributions add up to the identity.  Choose an
element with a single prescribed order at each point of the set and extend by linearity; what is
left after subtracting its contribution has no order anywhere, so it lies in the kernel. -/
theorem exists_addMonoidHom_add_eq_self (g : Additive A →+ (X →₀ ℤ)) (hg : Function.Surjective g)
    (B : Subgroup A) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0) :
    ∃ (π : Additive A →+ Additive ↥B) (s : (X →₀ ℤ) →+ Additive A),
      ∀ z : Additive A, MonoidHom.toAdditive B.subtype (π z) + s (g z) = z := by
  classical
  choose a ha using fun x : X => hg (Finsupp.single x (1 : ℤ))
  set s : (X →₀ ℤ) →+ Additive A :=
    Finsupp.liftAddHom (fun x => zmultiplesHom (Additive A) (a x)) with hsdef
  have hgs : ∀ b : X →₀ ℤ, g (s b) = b := by
    intro b
    induction b using Finsupp.induction_linear with
    | zero => rw [map_zero, map_zero]
    | add b b' hb hb' => rw [map_add, map_add, hb, hb']
    | single x n =>
      have h1 : s (Finsupp.single x n) = n • a x := by
        rw [hsdef]
        exact Finsupp.liftAddHom_apply_single _ x n
      rw [h1, map_zsmul, ha, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hker : ∀ z : Additive A, g (z - s (g z)) = 0 := by
    intro z
    rw [map_sub, hgs, sub_self]
  refine ⟨{ toFun := fun z => (⟨(z - s (g z)).toMul, (hB _).2 (hker z)⟩ : ↥B)
            map_zero' := Subtype.ext (by
              show ((0 : Additive A) - s (g 0)).toMul = (1 : A)
              rw [map_zero, map_zero, sub_zero]
              rfl)
            map_add' := fun z z' => Subtype.ext (by
              show ((z + z') - s (g (z + z'))).toMul
                = (z - s (g z)).toMul * (z' - s (g z')).toMul
              rw [map_add, map_add]
              exact congrArg Additive.toMul
                (show z + z' - (s (g z) + s (g z'))
                  = (z - s (g z)) + (z' - s (g z')) by abel)) }, s, fun z => ?_⟩
  show (z - s (g z)) + s (g z) = z
  abel

end Split

/-! ### The inclusion of a subgroup, tensored with a module -/

section Incl

variable {A : Type*} [CommGroup A] (C : Type*) [CommGroup C] (B : Subgroup A)

/-- **The inclusion of a subgroup, tensored with a module.** -/
noncomputable def tensorSubIncl :
    Additive ↥B ⊗[ℤ] Additive C →ₗ[ℤ] Additive A ⊗[ℤ] Additive C :=
  LinearMap.rTensor (Additive C) (MonoidHom.toAdditive B.subtype).toIntLinearMap

@[simp]
theorem tensorSubIncl_tmul (b : ↥B) (w : C) :
    tensorSubIncl C B (Additive.ofMul b ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul (b : A) ⊗ₜ[ℤ] Additive.ofMul w := rfl

variable {C B}
variable {X : Type*} (g : Additive A →+ (X →₀ ℤ))

/-- The valuation vanishes on the inclusion of its kernel, after tensoring. -/
theorem rTensor_tensorSubIncl_eq_zero (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (t : Additive ↥B ⊗[ℤ] Additive C) :
    LinearMap.rTensor (Additive C) g.toIntLinearMap (tensorSubIncl C B t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', add_zero]
  | tmul b w =>
    show LinearMap.rTensor (Additive C) g.toIntLinearMap
      (Additive.ofMul ((b.toMul : ↥B) : A) ⊗ₜ[ℤ] w) = 0
    rw [LinearMap.rTensor_tmul]
    show g (Additive.ofMul ((b.toMul : ↥B) : A)) ⊗ₜ[ℤ] w = 0
    rw [(hB _).1 (b.toMul : ↥B).2, TensorProduct.zero_tmul]

variable {π : Additive A →+ Additive ↥B} {s : (X →₀ ℤ) →+ Additive A}
variable (hsplit : ∀ z : Additive A, MonoidHom.toAdditive B.subtype (π z) + s (g z) = z)

include hsplit

/-- The retraction of a split inclusion is the identity on the subgroup. -/
theorem retraction_eq_self (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0) (b : ↥B) :
    π (Additive.ofMul (b : A)) = Additive.ofMul b := by
  have h := hsplit (Additive.ofMul (b : A))
  rw [(hB _).1 b.2, map_zero, add_zero] at h
  exact Subtype.ext (congrArg Additive.toMul h)

/-- **The retraction survives tensoring**: it is still a left inverse of the inclusion. -/
theorem rTensor_retraction_tensorSubIncl (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (t : Additive ↥B ⊗[ℤ] Additive C) :
    LinearMap.rTensor (Additive C) π.toIntLinearMap (tensorSubIncl C B t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  | tmul b w =>
    show LinearMap.rTensor (Additive C) π.toIntLinearMap
      (Additive.ofMul ((b.toMul : ↥B) : A) ⊗ₜ[ℤ] w) = b ⊗ₜ[ℤ] w
    rw [LinearMap.rTensor_tmul]
    show π (Additive.ofMul ((b.toMul : ↥B) : A)) ⊗ₜ[ℤ] w = b ⊗ₜ[ℤ] w
    rw [retraction_eq_self g hsplit hB]
    rfl

/-- **The splitting survives tensoring**: what the retraction contributes and what the section
contributes still add up to the identity. -/
theorem tensorSubIncl_rTensor_add (t : Additive A ⊗[ℤ] Additive C) :
    tensorSubIncl C B (LinearMap.rTensor (Additive C) π.toIntLinearMap t)
      + LinearMap.rTensor (Additive C) s.toIntLinearMap
        (LinearMap.rTensor (Additive C) g.toIntLinearMap t) = t := by
  have hswap : ∀ p q r u : Additive A ⊗[ℤ] Additive C, p + q + (r + u) = p + r + (q + u) :=
    fun p q r u => by abel
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
  | add t t' ht ht' => rw [map_add, map_add, map_add, map_add, hswap, ht, ht']
  | tmul z w =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    show MonoidHom.toAdditive B.subtype (π z) ⊗ₜ[ℤ] w + s (g z) ⊗ₜ[ℤ] w = z ⊗ₜ[ℤ] w
    rw [← TensorProduct.add_tmul, hsplit]

end Incl

/-! ### The kernel of the valuation after tensoring -/

section Kernel

variable {A : Type*} [CommGroup A] {C : Type*} [CommGroup C] {B : Subgroup A}
variable {X : Type*} (g : Additive A →+ (X →₀ ℤ)) (hg : Function.Surjective g)
  (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)

include hg hB

/-- **The inclusion of the kernel of a valuation onto a free abelian group stays injective after
tensoring with any module.** -/
theorem tensorSubIncl_injective : Function.Injective (tensorSubIncl C B) := by
  obtain ⟨π, s, hsplit⟩ := exists_addMonoidHom_add_eq_self g hg B hB
  intro t t' h
  rw [← rTensor_retraction_tensorSubIncl (C := C) g hsplit hB t,
    ← rTensor_retraction_tensorSubIncl (C := C) g hsplit hB t', h]

/-- **The image of the kernel of a valuation onto a free abelian group is still the whole kernel
after tensoring with any module.** -/
theorem range_tensorSubIncl :
    LinearMap.range (tensorSubIncl C B)
      = LinearMap.ker (LinearMap.rTensor (Additive C) g.toIntLinearMap) := by
  obtain ⟨π, s, hsplit⟩ := exists_addMonoidHom_add_eq_self g hg B hB
  refine le_antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact rTensor_tensorSubIncl_eq_zero g hB t
  · intro t ht
    refine ⟨LinearMap.rTensor (Additive C) π.toIntLinearMap t, ?_⟩
    have h := tensorSubIncl_rTensor_add (C := C) g hsplit t
    rw [LinearMap.mem_ker.1 ht, map_zero, add_zero] at h
    exact h

end Kernel

/-! ### The valuation of a tensor -/

section Val

variable {Q : Type*} [Group Q] {A : Type*} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type*) [CommGroup C] [MulDistribMulAction Q C]
variable {X : Type*} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ))

/-- **The valuation of a tensor**, as a finitely supported family of values of the module. -/
noncomputable def tensorVal :
    Additive A ⊗[ℤ] Additive C →ₗ[ℤ] (X →₀ Additive C) :=
  (TensorProduct.finsuppScalarLeft ℤ (Additive C) X).toLinearMap ∘ₗ
    LinearMap.rTensor (Additive C) g.toIntLinearMap

theorem tensorVal_tmul_apply (a : A) (w : C) (x : X) :
    tensorVal C g (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w) x
      = g (Additive.ofMul a) x • (Additive.ofMul w : Additive C) := by
  show TensorProduct.finsuppScalarLeft ℤ (Additive C) X
    (LinearMap.rTensor (Additive C) g.toIntLinearMap
      (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)) x = _
  rw [LinearMap.rTensor_tmul]
  exact TensorProduct.finsuppScalarLeft_apply_tmul_apply _ _ _

theorem tensorVal_eq_zero_iff (t : Additive A ⊗[ℤ] Additive C) :
    tensorVal C g t = 0 ↔ LinearMap.rTensor (Additive C) g.toIntLinearMap t = 0 := by
  show (TensorProduct.finsuppScalarLeft ℤ (Additive C) X)
      (LinearMap.rTensor (Additive C) g.toIntLinearMap t) = 0 ↔ _
  exact map_eq_zero_iff _ (TensorProduct.finsuppScalarLeft ℤ (Additive C) X).injective

theorem tensorVal_surjective (hg : Function.Surjective g) :
    Function.Surjective (tensorVal C g) := by
  have hg' : Function.Surjective ⇑g.toIntLinearMap := hg
  intro b
  obtain ⟨t, ht⟩ := LinearMap.rTensor_surjective (Additive C) hg'
    ((TensorProduct.finsuppScalarLeft ℤ (Additive C) X).symm b)
  refine ⟨t, ?_⟩
  show (TensorProduct.finsuppScalarLeft ℤ (Additive C) X)
    (LinearMap.rTensor (Additive C) g.toIntLinearMap t) = b
  rw [ht]
  exact (TensorProduct.finsuppScalarLeft ℤ (Additive C) X).apply_symm_apply b

/-- **The valuation of a tensor is equivariant**: an automorphism moves the value and the place at
once. -/
theorem tensorVal_smul
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (σ : Q) (t : Additive A ⊗[ℤ] Additive C) (x : X) :
    tensorVal C g (σ • t) x
      = Additive.ofMul (σ • (tensorVal C g t (σ⁻¹ • x)).toMul) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [smul_zero, map_zero]
    simp only [Finsupp.coe_zero, Pi.zero_apply, _root_.toMul_zero, smul_one,
      _root_.ofMul_one]
  | add t t' ht ht' =>
    rw [smul_add, map_add, Finsupp.add_apply, ht, ht', map_add, Finsupp.add_apply,
      _root_.toMul_add, ← _root_.ofMul_mul, smul_mul']
  | tmul z w =>
    have h1 : tensorVal C g (σ • (z ⊗ₜ[ℤ] w)) x
        = g (Additive.ofMul (σ • z.toMul)) x • (Additive.ofMul (σ • w.toMul) : Additive C) := by
      show tensorVal C g
        (Additive.ofMul (σ • z.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul)) x = _
      exact tensorVal_tmul_apply C g _ _ x
    have h2 : tensorVal C g (z ⊗ₜ[ℤ] w) (σ⁻¹ • x)
        = g (Additive.ofMul z.toMul) (σ⁻¹ • x) • (Additive.ofMul w.toMul : Additive C) :=
      tensorVal_tmul_apply C g z.toMul w.toMul (σ⁻¹ • x)
    rw [h1, h2, hgeq, ← _root_.ofMul_zpow, ← smul_zpow', _root_.toMul_zsmul]
    rfl

end Val

/-! ### The inclusion as a morphism of representations -/

section Rep

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable (C : Type) [CommGroup C] [MulDistribMulAction Q C]
variable (B : Subgroup A) [IsStableSubgroup Q B]

/-- The inclusion of a stable subgroup, tensored with a module, is equivariant. -/
theorem tensorSubIncl_smul (σ : Q) (t : Additive ↥B ⊗[ℤ] Additive C) :
    tensorSubIncl C B (σ • t) = σ • tensorSubIncl C B t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, smul_add, ht, ht']
  | tmul b w =>
    show tensorSubIncl C B (Additive.ofMul (σ • b.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul))
      = σ • (Additive.ofMul ((b.toMul : ↥B) : A) ⊗ₜ[ℤ] w)
    rw [tensorSubIncl_tmul]
    rfl

variable (Q) in
/-- **The inclusion of a stable subgroup, tensored with a module, as a morphism of
representations.** -/
noncomputable def tensorSubInclRep :
    Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C) ⟶
      Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C) :=
  repHomOfAddHom Q _ _ (tensorSubIncl C B).toAddMonoidHom (tensorSubIncl_smul C B)

@[simp]
theorem tensorSubInclRep_hom_apply (t : Additive ↥B ⊗[ℤ] Additive C) :
    (tensorSubInclRep Q C B).hom.hom t = tensorSubIncl C B t := rfl

end Rep

end InverseGalois.CFT
