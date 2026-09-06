/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.InfiniteLevelPower
import InverseGalois.CFT.Tate.FamilyTensorFull
import InverseGalois.CFT.Units.LocalEmbedding

/-!
# From a decomposition subgroup to a completion

A class of the first cohomology of a Galois group with radical coefficients is trivial on a
decomposition subgroup exactly when the unit it comes from becomes a `p`-th power in the compositum
of the base field with the fixed field of that subgroup.  The idelic reading of the same condition
asks instead that the unit become a `p`-th power in the completion at the place below.  This file
compares the two readings, in the direction that the first implies the second.

For a single unit the comparison is Kummer theory at a level: a `p`-th root inside the compositum
is fixed by every automorphism of the whole extension that fixes the place and the base field
pointwise, because such an automorphism fixes both factors of the compositum, and a radical fixed
by the decomposition subgroup has a radicand which is a `p`-th power in the completion below.

Cohomology classes are not units but elements of a tensor product of the units with the
coefficients, and there divisibility by `p` is tested coordinate by coordinate along a basis of the
coefficients over the field with `p` elements.  A map tensored with such coefficients therefore
kills whatever a second one kills as soon as divisibility after the second follows from
divisibility after the first, which is what the comparison for a single unit provides.  So the
whole class dies in the completion once it dies in the compositum.

## Main results

* `InverseGalois.CFT.fix_of_mem_sup_of_restrictScalars_mem`: an automorphism of the extension over
  a level lying in a subgroup fixes the compositum of the level with the fixed field of that
  subgroup.
* `InverseGalois.CFT.exists_pow_adicUnitHom_of_exists_pow_sup`: **a unit of a level which is a
  `p`-th power in the compositum of the level with the fixed field of a decomposition subgroup at a
  prime is a `p`-th power in the completion of the level at the place below.**
* `InverseGalois.CFT.exists_pow_infiniteUnitHom_of_exists_pow_sup`: **the same at an archimedean
  place.**
* `InverseGalois.CFT.tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero`: **an element of the units
  of a level tensored with coefficients of finite rank which dies in the compositum with the fixed
  field of a decomposition subgroup at a prime dies in the completion at the place below.**
* `InverseGalois.CFT.tensor_infiniteUnitHom_eq_zero_of_tensor_sup_eq_zero`: **the same at an
  archimedean place.**

## Tags

number field, decomposition group, Kummer theory, completion, local power, tensor product, idele
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise TensorProduct

/-! ### A `p`-th power of a unit -/

section UnitsPow

/-- A unit of a field which is the `p`-th power of an element of the field is the `p`-th power of a
unit, the element being nonzero because its power is. -/
theorem exists_units_pow_eq_of_pow_eq_coe {F : Type*} [Field F] {p : ℕ} (hp : p ≠ 0) {u : Fˣ}
    {c : F} (hc : c ^ p = (u : F)) : ∃ d : Fˣ, d ^ p = u := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hp] at hc
    exact u.ne_zero hc.symm
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hc

end UnitsPow

/-! ### Automorphisms over a level -/

section Fix

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {K : IntermediateField k Ω}

/-- The action of an automorphism of the extension over a level on the ideals of the integers is
its action as an automorphism over the base. -/
theorem smul_restrictScalars_ideal (σ : Ω ≃ₐ[↥K] Ω) (I : Ideal (𝓞 Ω)) :
    (σ.restrictScalars k) • I = σ • I := rfl

/-- The action of an automorphism of the extension over a level on the archimedean places is its
action as an automorphism over the base. -/
theorem smul_restrictScalars_infinitePlace (σ : Ω ≃ₐ[↥K] Ω) (W : InfinitePlace Ω) :
    (σ.restrictScalars k) • W = σ • W := rfl

/-- **An automorphism of the extension over a level which lies in a subgroup fixes the compositum
of the level with the fixed field of that subgroup.**  It fixes the level because it is an
automorphism over it, and it fixes the fixed field because it lies in the subgroup. -/
theorem fix_of_mem_sup_of_restrictScalars_mem {F : IntermediateField k Ω}
    {D : Subgroup Gal(Ω/k)} (hF : F.fixingSubgroup = D) {σ : Gal(Ω/↥K)}
    (hσ : (σ.restrictScalars k) ∈ D) {b : Ω} (hb : b ∈ K ⊔ F) : σ b = b := by
  have hK : (σ.restrictScalars k) ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact σ.commutes (⟨y, hy⟩ : ↥K)
  have hmem : (σ.restrictScalars k) ∈ (K ⊔ F).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, hF]
    exact ⟨hK, hσ⟩
  exact (IntermediateField.mem_fixingSubgroup_iff (K ⊔ F) _).1 hmem b hb

/-- An automorphism of the extension over a level fixing a prime fixes the compositum of the level
with the fixed field of the decomposition subgroup at that prime. -/
theorem fix_of_mem_sup_of_mem_stabilizer_ideal {F : IntermediateField k Ω} {P : Ideal (𝓞 Ω)}
    (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P) (σ : ↥(stabilizer Gal(Ω/↥K) P)) {b : Ω}
    (hb : b ∈ K ⊔ F) : (σ : Gal(Ω/↥K)) b = b :=
  fix_of_mem_sup_of_restrictScalars_mem hF
    (mem_stabilizer_iff.mpr
      (by rw [smul_restrictScalars_ideal]; exact mem_stabilizer_iff.mp σ.2)) hb

/-- An automorphism of the extension over a level fixing an archimedean place fixes the compositum
of the level with the fixed field of the decomposition subgroup at that place. -/
theorem fix_of_mem_sup_of_mem_stabilizer_infinitePlace {F : IntermediateField k Ω}
    {W : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) W)
    (σ : ↥(stabilizer Gal(Ω/↥K) W)) {b : Ω} (hb : b ∈ K ⊔ F) : (σ : Gal(Ω/↥K)) b = b :=
  fix_of_mem_sup_of_restrictScalars_mem hF
    (mem_stabilizer_iff.mpr
      (by rw [smul_restrictScalars_infinitePlace]; exact mem_stabilizer_iff.mp σ.2)) hb

end Fix

/-! ### A single unit -/

section OneUnit

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω} [NumberField ↥K] {p : ℕ} {ζ : ↥K}
  (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
  (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)

omit [IsGalois k Ω] [NumberField ↥K] in
include hj in
/-- A unit of a level whose image in the compositum is a `p`-th power there gives an element of the
compositum whose `p`-th power is the unit, read in the whole extension. -/
theorem algebraMap_eq_pow_of_pow_eq {a : (↥K)ˣ} {b : (↥(K ⊔ F))ˣ} (hb : b ^ p = j a) :
    algebraMap ↥K Ω (a : ↥K) = (algebraMap ↥(K ⊔ F) Ω (b : ↥(K ⊔ F))) ^ p := by
  have h : (algebraMap ↥(K ⊔ F) Ω) ((j a : ↥(K ⊔ F))) = (algebraMap ↥K Ω) (a : ↥K) :=
    congrArg Units.val (hj a)
  have hbp : ((b : ↥(K ⊔ F))) ^ p = (j a : ↥(K ⊔ F)) := by
    rw [← Units.val_pow_eq_pow_val, hb]
  rw [← map_pow, hbp, h]

include hj in
/-- **A unit of a level which is a `p`-th power in the compositum of the level with the fixed field
of a decomposition subgroup at a prime is a `p`-th power in the completion of the level at the
place below.**  A `p`-th root in the compositum is fixed by every automorphism of the whole
extension over the level which fixes the prime, and a radical fixed by the decomposition subgroup
has a radicand which is a `p`-th power in the completion. -/
theorem exists_pow_adicUnitHom_of_exists_pow_sup (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P)
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P) {a : (↥K)ˣ}
    (ha : ∃ b : (↥(K ⊔ F))ˣ, b ^ p = j a) :
    ∃ c : (v.adicCompletion ↥K)ˣ, c ^ p = adicUnitHom v a := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := exists_pow_adicCompletion_of_forall_stabilizer_smul_eq (k := ↥K) hζ hp
    (algebraMap_eq_pow_of_pow_eq j hj hb)
    (fun σ => fix_of_mem_sup_of_mem_stabilizer_ideal hF σ (b : ↥(K ⊔ F)).2) hv
  exact exists_units_pow_eq_of_pow_eq_coe hp hc

include hj in
/-- **A unit of a level which is a `p`-th power in the compositum of the level with the fixed field
of a decomposition subgroup at an archimedean place is a `p`-th power in the completion of the
level at the place below.** -/
theorem exists_pow_infiniteUnitHom_of_exists_pow_sup (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0)
    {W : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) W)
    {u : InfinitePlace ↥K} (hu : u = W.comap (algebraMap ↥K Ω)) {a : (↥K)ˣ}
    (ha : ∃ b : (↥(K ⊔ F))ˣ, b ^ p = j a) :
    ∃ c : u.Completionˣ, c ^ p = infiniteUnitHom u a := by
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := exists_pow_infiniteCompletion_of_forall_stabilizer_smul_eq (k := ↥K) hζ hp
    (algebraMap_eq_pow_of_pow_eq j hj hb)
    (fun σ => fix_of_mem_sup_of_mem_stabilizer_infinitePlace hF σ (b : ↥(K ⊔ F)).2) hu
  exact exists_units_pow_eq_of_pow_eq_coe hp hc

end OneUnit

/-! ### A whole class -/

section Tensor

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {K F : IntermediateField k Ω} [NumberField ↥K] {p d : ℕ} [Fact p.Prime] {ζ : ↥K}
  {W : Type*} [AddCommGroup W] [Module ℤ W] (e : W ≃+ (Fin d → ZMod p))
  (j : (↥K)ˣ →* (↥(K ⊔ F))ˣ)
  (hj : ∀ a : (↥K)ˣ, Units.map (algebraMap ↥(K ⊔ F) Ω : ↥(K ⊔ F) →* Ω) (j a)
    = Units.map (algebraMap ↥K Ω : ↥K →* Ω) a)

include e hj in
/-- **An element of the units of a level tensored with coefficients of finite rank over the field
with `p` elements which dies in the compositum of the level with the fixed field of a decomposition
subgroup at a prime dies in the completion of the level at the place below.**  Divisibility by `p`
is read coordinate by coordinate along a basis of the coefficients, and each coordinate which
becomes a `p`-th power in the compositum becomes one in the completion. -/
theorem tensor_adicUnitHom_eq_zero_of_tensor_sup_eq_zero (hζ : IsPrimitiveRoot ζ p)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) P)
    {v : HeightOneSpectrum (𝓞 ↥K)} (hv : v.asIdeal = Ideal.under (𝓞 ↥K) P)
    {t : Additive (↥K)ˣ ⊗[ℤ] W}
    (ht : TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0) :
    TensorProduct.map (MonoidHom.toAdditive (adicUnitHom v)).toIntLinearMap LinearMap.id t = 0 := by
  refine Tate.map_eq_zero_of_forall_exists_nsmul e _ _ (fun a ha => ?_) ht
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := exists_pow_adicUnitHom_of_exists_pow_sup j hj hζ
    (Nat.Prime.ne_zero Fact.out) hF hv (a := Additive.toMul a) ⟨Additive.toMul b, hb⟩
  exact ⟨Additive.ofMul c, hc⟩

include e hj in
/-- **An element of the units of a level tensored with coefficients of finite rank over the field
with `p` elements which dies in the compositum of the level with the fixed field of a decomposition
subgroup at an archimedean place dies in the completion of the level at the place below.** -/
theorem tensor_infiniteUnitHom_eq_zero_of_tensor_sup_eq_zero (hζ : IsPrimitiveRoot ζ p)
    {V : InfinitePlace Ω} (hF : F.fixingSubgroup = stabilizer Gal(Ω/k) V)
    {u : InfinitePlace ↥K} (hu : u = V.comap (algebraMap ↥K Ω))
    {t : Additive (↥K)ˣ ⊗[ℤ] W}
    (ht : TensorProduct.map (MonoidHom.toAdditive j).toIntLinearMap LinearMap.id t = 0) :
    TensorProduct.map (MonoidHom.toAdditive (infiniteUnitHom u)).toIntLinearMap LinearMap.id t
      = 0 := by
  refine Tate.map_eq_zero_of_forall_exists_nsmul e _ _ (fun a ha => ?_) ht
  obtain ⟨b, hb⟩ := ha
  obtain ⟨c, hc⟩ := exists_pow_infiniteUnitHom_of_exists_pow_sup j hj hζ
    (Nat.Prime.ne_zero Fact.out) hF hu (a := Additive.toMul a) ⟨Additive.toMul b, hb⟩
  exact ⟨Additive.ofMul c, hc⟩

end Tensor

end InverseGalois.CFT
