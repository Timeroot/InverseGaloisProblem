/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.TensorOrbit

/-!
# Shrinking the module kills a class carried into the kernel of the valuation

A finite group acts on an abelian group carrying a valuation onto the free abelian group on a set
of places it permutes, and on a module.  **A class with coefficients in the tensor product which
comes from the kernel of the valuation, and whose chosen preimage there is killed by a homomorphism
of the module, is itself killed by that homomorphism**: the homomorphism commutes with the
inclusion of the kernel, so the image of the class is the image of zero.

In the intended reading the abelian group is the multiplicative group of a number field, the places
are the primes outside a finite set, the kernel of the valuation is the group of units for that
set, and the module is a layer of a tower whose homomorphisms may be shrunk at will.  Carrying a
class into the units for a finite set is what makes the shrinking possible at all, because the
units for a finite set are finitely generated and so cohomology with those coefficients is finite;
and it is enough to kill the *one* preimage one has chosen, so the class to be killed is fixed
before the homomorphism is chosen.  That order matters: a shrink kills a prescribed finite list of
classes, and the list must be named first.

Also recorded is the variant in which the passage into the kernel is itself effected by a
homomorphism, one killing the one-dimensional classes of every subgroup of the group; the valuation
of a cocycle at a place is a one-cocycle for the subgroup fixing that place, so such a homomorphism
supplies the local input at every place at once.

## Main definitions

* `InverseGalois.CFT.tensorCoeff`: a homomorphism of the second factor of the tensor product.
* `InverseGalois.CFT.tensorCoeffRep`: the same, as a morphism of representations.

## Main results

* `InverseGalois.CFT.map_tensorCoeffRep_eq_zero_of_map_tensorSubInclRep`: **a class whose chosen
  preimage in the kernel of the valuation is killed by a homomorphism of the module is itself
  killed by it.**
* `InverseGalois.CFT.mem_range_map_tensorSubInclRep_of_forall_subgroup`: **a class pushed forward
  along a homomorphism killing the classes of every subgroup comes from the kernel of the
  valuation.**
* `InverseGalois.CFT.map_tensorCoeffRep_eq_zero_of_forall_subgroup`: **two such homomorphisms in
  succession kill every class.**

## Tags

group cohomology, permutation module, S-unit, tensor product, shrinking
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction TensorProduct groupCohomology

/-! ### A homomorphism of the second factor -/

section Coeff

variable {A : Type*} [CommGroup A] {C C' C'' : Type*} [CommGroup C] [CommGroup C'] [CommGroup C'']

variable (A) in
/-- **A homomorphism of the second factor of a tensor product with the additive copy of a group.**
-/
noncomputable def tensorCoeff (φ : C →* C') :
    Additive A ⊗[ℤ] Additive C →ₗ[ℤ] Additive A ⊗[ℤ] Additive C' :=
  TensorProduct.map LinearMap.id (MonoidHom.toAdditive φ).toIntLinearMap

@[simp]
theorem tensorCoeff_tmul (φ : C →* C') (a : A) (w : C) :
    tensorCoeff A φ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul w)
      = Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul (φ w) := rfl

/-- **A homomorphism of the second factor which is a composite acts as the composite.** -/
theorem tensorCoeff_comp {φ : C →* C'} {φ' : C' →* C''} (ψ : C →* C'')
    (hψ : ∀ w : C, ψ w = φ' (φ w)) (t : Additive A ⊗[ℤ] Additive C) :
    tensorCoeff A ψ t = tensorCoeff A φ' (tensorCoeff A φ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul z w =>
    exact congrArg (fun v => Additive.ofMul z.toMul ⊗ₜ[ℤ] Additive.ofMul v) (hψ w.toMul)

variable {Q : Type*} [Group Q] [MulDistribMulAction Q A] [MulDistribMulAction Q C]
  [MulDistribMulAction Q C']

/-- **A homomorphism of the second factor which is equivariant induces an equivariant map of the
tensor product.** -/
theorem tensorCoeff_smul (φ : C →* C') (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w)
    (σ : Q) (t : Additive A ⊗[ℤ] Additive C) :
    tensorCoeff A φ (σ • t) = σ • tensorCoeff A φ t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, smul_add, ht, ht']
  | tmul z w =>
    show tensorCoeff A φ (Additive.ofMul (σ • z.toMul) ⊗ₜ[ℤ] Additive.ofMul (σ • w.toMul)) = _
    rw [tensorCoeff_tmul, hφ]
    rfl

variable {X : Type*} [MulAction Q X] [DecidableEq X]

/-- **The valuation of a tensor is natural in the second factor**: the valuation of the pushed
forward tensor at a place is the value at that place pushed forward. -/
theorem tensorVal_tensorCoeff (φ : C →* C') (g : Additive A →+ (X →₀ ℤ))
    (t : Additive A ⊗[ℤ] Additive C) (x : X) :
    tensorVal C' g (tensorCoeff A φ t) x = Additive.ofMul (φ (tensorVal C g t x).toMul) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, _root_.toMul_zero, _root_.map_one,
      _root_.ofMul_one]
  | add t t' ht ht' =>
    simp only [map_add, Finsupp.add_apply, ht, ht', _root_.toMul_add, _root_.map_mul,
      _root_.ofMul_mul]
  | tmul z w =>
    have h1 : tensorVal C' g (tensorCoeff A φ (z ⊗ₜ[ℤ] w)) x
        = g (Additive.ofMul z.toMul) x • (Additive.ofMul (φ w.toMul) : Additive C') :=
      tensorVal_tmul_apply C' g z.toMul (φ w.toMul) x
    have h2 : tensorVal C g (z ⊗ₜ[ℤ] w) x
        = g (Additive.ofMul z.toMul) x • (Additive.ofMul w.toMul : Additive C) :=
      tensorVal_tmul_apply C g z.toMul w.toMul x
    rw [h1, h2, _root_.toMul_zsmul, _root_.map_zpow, _root_.ofMul_zpow]
    rfl

/-- **A homomorphism of the second factor commutes with the inclusion of a subgroup of the
first.** -/
theorem tensorCoeff_tensorSubIncl (φ : C →* C') (B : Subgroup A)
    (t : Additive ↥B ⊗[ℤ] Additive C) :
    tensorCoeff A φ (tensorSubIncl C B t) = tensorSubIncl C' B (tensorCoeff ↥B φ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul b w => rfl

end Coeff

/-! ### The homomorphism as a morphism of representations -/

section Rep

variable {Q : Type} [Group Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
  [MulDistribMulAction Q C']

variable (Q) in
/-- **An equivariant homomorphism of the second factor, as a morphism of representations.** -/
noncomputable def tensorCoeffRep (φ : C →* C')
    (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w) :
    Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C) ⟶
      Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C') :=
  repHomOfAddHom Q _ _ (tensorCoeff A φ).toAddMonoidHom (tensorCoeff_smul φ hφ)

@[simp]
theorem tensorCoeffRep_hom_apply (φ : C →* C')
    (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w) (t : Additive A ⊗[ℤ] Additive C) :
    (tensorCoeffRep (A := A) Q φ hφ).hom.hom t = tensorCoeff A φ t := rfl

end Rep

/-! ### The class comes from the kernel of the valuation -/

section Main

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C C' C'' : Type} [CommGroup C] [CommGroup C'] [CommGroup C'']
  [MulDistribMulAction Q C] [MulDistribMulAction Q C'] [MulDistribMulAction Q C'']
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]
variable (φ : C →* C') (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w)

/-- **A cocycle with coefficients in the tensor product, pushed forward along a homomorphism of the
module which kills the one-dimensional classes of every subgroup, has a class coming from the
tensor product of the kernel of the valuation with the module.**  At each place the valuation of
the cocycle, restricted to the subgroup fixing that place, is a one-cocycle with values in the
module; the hypothesis makes it a coboundary after pushing forward, which is exactly the local
input to the statement that a class trivial at every place comes from the kernel of the
valuation. -/
theorem mem_range_map_tensorSubInclRep_of_forall_subgroup_cocycle (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hkill : ∀ (D : Subgroup Q) (d : ↥D → C),
      (∀ ρ τ : ↥D, d (ρ * τ) = (ρ : Q) • d τ * d ρ) →
      ∃ u : C', ∀ ρ : ↥D, φ (d ρ) = (ρ : Q) • u / u)
    (c : Q → Additive A ⊗[ℤ] Additive C)
    (hcoc : c ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom
        (H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩) ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C'))
        (tensorSubInclRep Q C' B) 1).hom := by
  have hc : ∀ σ τ : Q, c (σ * τ) = σ • c τ + c σ :=
    (mem_cocycles₁_iff (A := Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) c).1 hcoc
  have hc'coc : (fun σ : Q => tensorCoeff A φ (c σ))
      ∈ cocycles₁ (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C')) := by
    refine (mem_cocycles₁_iff
      (A := Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C')) _).2 fun σ τ => ?_
    show tensorCoeff A φ (c (σ * τ)) = σ • tensorCoeff A φ (c τ) + tensorCoeff A φ (c σ)
    rw [hc σ τ, map_add, tensorCoeff_smul φ hφ]
  have heq : (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom
        (H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C)) ⟨c, hcoc⟩)
      = H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C')) ⟨_, hc'coc⟩ := by
    rw [H1π_comp_map_apply]
    exact congrArg (fun w => H1π (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C')) w)
      (Subtype.ext rfl)
  rw [heq]
  refine mem_range_map_tensorSubInclRep_of_forall_stabilizer C' g B hg hB hgeq _ hc'coc ?_
  intro x
  have hd : ∀ ρ τ : ↥(MulAction.stabilizer Q x),
      (tensorVal C g (c ((ρ * τ : ↥(MulAction.stabilizer Q x)) : Q)) x).toMul
        = (ρ : Q) • (tensorVal C g (c (τ : Q)) x).toMul
          * (tensorVal C g (c (ρ : Q)) x).toMul := by
    intro ρ τ
    have hinv : (ρ : Q)⁻¹ • x = x :=
      inv_smul_eq_iff.2 (MulAction.mem_stabilizer_iff.1 ρ.2).symm
    show (tensorVal C g (c ((ρ : Q) * (τ : Q))) x).toMul = _
    rw [hc, map_add, Finsupp.add_apply, _root_.toMul_add, tensorVal_smul C g hgeq, hinv]
    rfl
  obtain ⟨u, hu⟩ := hkill (MulAction.stabilizer Q x)
    (fun ρ => (tensorVal C g (c (ρ : Q)) x).toMul) hd
  refine ⟨Additive.ofMul u, fun ρ hρ => ?_⟩
  show tensorVal C' g (tensorCoeff A φ (c ρ)) x = _
  rw [tensorVal_tensorCoeff φ g (c ρ) x, hu ⟨ρ, hρ⟩]
  exact _root_.ofMul_div _ _

/-- **A class with coefficients in the tensor product, pushed forward along a homomorphism of the
module which kills the one-dimensional classes of every subgroup, comes from the tensor product of
the kernel of the valuation with the module.** -/
theorem mem_range_map_tensorSubInclRep_of_forall_subgroup (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hkill : ∀ (D : Subgroup Q) (d : ↥D → C),
      (∀ ρ τ : ↥D, d (ρ * τ) = (ρ : Q) • d τ * d ρ) →
      ∃ u : C', ∀ ρ : ↥D, φ (d ρ) = (ρ : Q) • u / u)
    (y : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom y ∈
      LinearMap.range (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C'))
        (tensorSubInclRep Q C' B) 1).hom := by
  induction y using H1_induction_on with
  | @h z =>
    exact mem_range_map_tensorSubInclRep_of_forall_subgroup_cocycle g B φ hφ hg hB hgeq hkill _ z.2

omit [Finite Q] in
/-- **A class coming from the tensor product of the kernel of the valuation with the module, whose
chosen preimage is killed by a homomorphism of the module, is itself killed by that
homomorphism.**  The homomorphism commutes with the inclusion of the kernel, so the image of the
preimage is the image of zero.  This is the form in which only *one* class need be killed: the
preimage is chosen first and the homomorphism afterwards. -/
theorem map_tensorCoeffRep_eq_zero_of_map_tensorSubInclRep
    {w : H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C))}
    {y : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))}
    (hw : (groupCohomology.map (MonoidHom.id Q)
      (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C))
      (tensorSubInclRep Q C B) 1).hom w = y)
    (hkill : (groupCohomology.map (MonoidHom.id Q)
      (tensorCoeffRep (A := ↥B) Q φ hφ) 1).hom w = 0) :
    (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom y = 0 := by
  have hrep : tensorSubInclRep Q C B ≫ tensorCoeffRep (A := A) Q φ hφ
      = tensorCoeffRep (A := ↥B) Q φ hφ ≫ tensorSubInclRep Q C' B := by
    ext t
    exact tensorCoeff_tensorSubIncl φ B t
  have hsquare := congrArg
    (fun m : Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C) ⟶
        Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C') =>
      (groupCohomology.map (MonoidHom.id Q)
        (A := Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)) m 1).hom w) hrep
  simp only [groupCohomology.map_id_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hsquare
  rw [← hw, hsquare, hkill, _root_.map_zero]

include hφ in
/-- **Two homomorphisms of the module in succession, the first killing the one-dimensional classes
of every subgroup and the second those with coefficients in the kernel of the valuation, kill every
class with coefficients in the tensor product.**  The first carries the class into the image of the
kernel of the valuation, where the second annihilates it. -/
theorem map_tensorCoeffRep_eq_zero_of_forall_subgroup (hg : Function.Surjective g)
    (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hkill : ∀ (D : Subgroup Q) (d : ↥D → C),
      (∀ ρ τ : ↥D, d (ρ * τ) = (ρ : Q) • d τ * d ρ) →
      ∃ u : C', ∀ ρ : ↥D, φ (d ρ) = (ρ : Q) • u / u)
    (φ' : C' →* C'') (hφ' : ∀ (σ : Q) (w : C'), φ' (σ • w) = σ • φ' w)
    (hkill' : ∀ w : H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C')),
      (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := ↥B) Q φ' hφ') 1).hom w = 0)
    (ψ : C →* C'') (hψ : ∀ w : C, ψ w = φ' (φ w))
    (hψeq : ∀ (σ : Q) (w : C), ψ (σ • w) = σ • ψ w)
    (y : H1 (Rep.ofDistribMulAction ℤ Q (Additive A ⊗[ℤ] Additive C))) :
    (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q ψ hψeq) 1).hom y = 0 := by
  obtain ⟨w, hw⟩ := mem_range_map_tensorSubInclRep_of_forall_subgroup g B φ hφ hg hB hgeq hkill y
  have hsplit : (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q ψ hψeq) 1).hom y
      = (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ' hφ') 1).hom
        ((groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := A) Q φ hφ) 1).hom y) := by
    have hrep : tensorCoeffRep (A := A) Q ψ hψeq
        = tensorCoeffRep (A := A) Q φ hφ ≫ tensorCoeffRep (A := A) Q φ' hφ' := by
      ext t
      exact tensorCoeff_comp ψ hψ t
    rw [hrep, groupCohomology.map_id_comp]
    rfl
  rw [hsplit]
  exact map_tensorCoeffRep_eq_zero_of_map_tensorSubInclRep B φ' hφ' hw (hkill' w)

end Main

end InverseGalois.CFT
