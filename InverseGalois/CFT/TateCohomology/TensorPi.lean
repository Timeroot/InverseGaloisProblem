/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Product
import InverseGalois.CFT.TateCohomology.TensorPTorsion

/-!
# A product of representations tensored with coefficients of finite rank over a prime field

Tensoring does not commute with an infinite product in general, so the complete cohomology of a
product of representations tensored with a fixed representation is not the product of the complete
cohomologies of the factors tensored with it.  It is, however, as soon as the fixed representation
is of finite rank over a prime field and every factor is killed by that prime: a choice of
coordinates then writes the tensor product with the coefficients as a finite power, and a finite
power does commute with a product.

The coordinates are the content of this file.  An isomorphism of the coefficients onto a finite
power of the integers modulo a prime lets one multiply a vector killed by that prime by a residue
class, and that multiplication is additive in the class exactly because the vector is killed by the
prime.  The resulting map from the tensor product of a group killed by the prime with the
coefficients to the corresponding finite power of the group is an isomorphism, natural in the
group, and comparing it for a product and for each factor identifies the canonical map between them.

## Main definitions

* `InverseGalois.CFT.Tate.coordEquiv`: **an abelian group killed by a prime, tensored with
  coefficients of finite rank over the field with that many elements, is a finite power of the
  group.**
* `InverseGalois.CFT.Tate.tensorPiHom`: the canonical map from a product tensored with a
  representation to the product of the tensor products.
* `InverseGalois.CFT.Tate.tensorPiIso`: **a product of representations killed by a prime, tensored
  with coefficients of finite rank over the field with that many elements, is the product of the
  factors tensored with the coefficients.**

## Main results

* `InverseGalois.CFT.Tate.nsmul_eq_zero_of_equivPi`: **coefficients of finite rank over the field
  with a prime number of elements are killed by that prime.**
* `InverseGalois.CFT.Tate.coordMap_map`: the coordinates are natural in the group.
* `InverseGalois.CFT.Tate.isZero_tateModule_tensorObj_piRep`: **a product of representations killed
  by a prime, tensored with coefficients of finite rank over the field with that many elements, has
  no complete cohomology in a degree in which no factor tensored with the coefficients has any.**

## Tags

tensor product, product, Tate cohomology, torsion, coordinates
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory

open scoped TensorProduct

noncomputable section

/-! ### Additive maps between modules over the integers -/

section IntLinear

variable {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

/-- **An additive map between modules over the integers is linear**, whichever module structures
the two groups carry. -/
def intLinearOfAddHom (f : M →+ N) : M →ₗ[ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain rfl : (inferInstance : Module ℤ M) = AddCommGroup.toIntModule M :=
      Subsingleton.elim _ _
    obtain rfl : (inferInstance : Module ℤ N) = AddCommGroup.toIntModule N :=
      Subsingleton.elim _ _
    exact f.map_zsmul x c

@[simp]
theorem intLinearOfAddHom_apply (f : M →+ N) (x : M) : intLinearOfAddHom f x = f x := rfl

end IntLinear

/-! ### Coefficients of finite rank over a prime field -/

section Killed

variable {p d : ℕ} {W : Type*} [AddCommGroup W]

/-- **Coefficients of finite rank over the field with a prime number of elements are killed by that
prime.** -/
theorem nsmul_eq_zero_of_equivPi (e : W ≃+ (Fin d → ZMod p)) (x : W) : p • x = 0 := by
  refine e.injective ?_
  rw [map_nsmul, map_zero]
  refine funext fun j => ?_
  show p • e x j = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end Killed

/-! ### Multiplying a vector killed by a number by a residue class -/

section Residue

variable {p : ℕ} {M : Type*} [AddCommGroup M]

/-- **Multiplying a vector killed by a number depends only on the residue of the multiplier.** -/
theorem nsmul_mod_of_nsmul_eq_zero (hM : ∀ m : M, p • m = 0) (n : ℕ) (m : M) :
    (n % p) • m = n • m :=
  calc (n % p) • m = 0 + (n % p) • m := (zero_add _).symm
    _ = p • ((n / p) • m) + (n % p) • m := by rw [hM]
    _ = (p * (n / p)) • m + (n % p) • m := by rw [mul_smul]
    _ = (p * (n / p) + n % p) • m := (add_nsmul _ _ _).symm
    _ = n • m := by rw [Nat.div_add_mod]

variable [NeZero p]

/-- **Multiplying a vector killed by a number by a residue class is additive in the class.** -/
theorem val_add_nsmul (hM : ∀ m : M, p • m = 0) (a b : ZMod p) (m : M) :
    (a + b).val • m = a.val • m + b.val • m := by
  rw [ZMod.val_add, nsmul_mod_of_nsmul_eq_zero hM, add_nsmul]

end Residue

/-! ### Coordinates on a tensor product with coefficients of finite rank -/

section Coord

variable {p d : ℕ} [Fact p.Prime] {W M N : Type*} [AddCommGroup W] [Module ℤ W]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  (e : W ≃+ (Fin d → ZMod p))

/-- Multiplying a vector killed by a prime by the coordinates of a vector of the coefficients. -/
def coordBil (hM : ∀ m : M, p • m = 0) : M →ₗ[ℤ] W →ₗ[ℤ] (Fin d → M) :=
  intLinearOfAddHom
    { toFun := fun m => intLinearOfAddHom
        { toFun := fun x j => (e x j).val • m
          map_zero' := by
            refine funext fun j => ?_
            simp
          map_add' := fun x y => funext fun j => by
            simp only [map_add, Pi.add_apply]
            exact val_add_nsmul hM _ _ m }
      map_zero' := by
        refine LinearMap.ext fun x => funext fun j => ?_
        simp
      map_add' := fun m m' => by
        refine LinearMap.ext fun x => funext fun j => ?_
        simp }

@[simp]
theorem coordBil_apply (hM : ∀ m : M, p • m = 0) (m : M) (x : W) (j : Fin d) :
    coordBil e hM m x j = (e x j).val • m := rfl

/-- **The coordinates of a tensor product with coefficients of finite rank over a prime field.** -/
def coordMap (hM : ∀ m : M, p • m = 0) : M ⊗[ℤ] W →ₗ[ℤ] (Fin d → M) :=
  TensorProduct.lift (coordBil e hM)

@[simp]
theorem coordMap_tmul (hM : ∀ m : M, p • m = 0) (m : M) (x : W) (j : Fin d) :
    coordMap e hM (m ⊗ₜ[ℤ] x) j = (e x j).val • m := rfl

/-- **The coordinates are natural in the group being tensored.** -/
theorem coordMap_map (f : M →ₗ[ℤ] N) (hM : ∀ m : M, p • m = 0) (hN : ∀ m : N, p • m = 0)
    (t : M ⊗[ℤ] W) (j : Fin d) :
    coordMap e hN (TensorProduct.map f LinearMap.id t) j = f (coordMap e hM t j) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => simp
  | add t t' ht ht' => simp only [map_add, Pi.add_apply, ht, ht']

omit [Module ℤ W] [Module ℤ M] [AddCommGroup N] [Module ℤ N] in
/-- The vector of the coefficients whose coordinates are the unit at one place. -/
def coordVec (j : Fin d) : W := e.symm (Pi.single j 1)

omit [Module ℤ W] [Module ℤ M] [AddCommGroup N] [Module ℤ N] in
/-- A multiple of a distinguished vector of the coefficients is the vector whose only nonzero
coordinate is the corresponding residue class. -/
theorem nsmul_coordVec (a : ZMod p) (j : Fin d) :
    a.val • coordVec e j = e.symm (Pi.single j a) := by
  rw [coordVec, ← map_nsmul]
  congr 1
  refine funext fun l => ?_
  rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : l = j
  · simp [h, nsmul_eq_mul]
  · simp [h]

omit [Module ℤ W] [Module ℤ M] [AddCommGroup N] [Module ℤ N] in
/-- The coordinates of a distinguished vector of the coefficients are the unit at one place. -/
theorem apply_coordVec (j : Fin d) : e (coordVec e j) = Pi.single j 1 :=
  e.apply_symm_apply _

omit [Module ℤ W] [Module ℤ M] [AddCommGroup N] [Module ℤ N] in
/-- **A vector of the coefficients is the combination of the distinguished ones given by its
coordinates.** -/
theorem sum_nsmul_coordVec (x : W) : ∑ j, (e x j).val • coordVec e j = x := by
  calc ∑ j, (e x j).val • coordVec e j = ∑ j, e.symm (Pi.single j (e x j)) := by
        exact Finset.sum_congr rfl fun j _ => nsmul_coordVec e (e x j) j
    _ = e.symm (∑ j, Pi.single j (e x j)) := (map_sum e.symm _ _).symm
    _ = x := by rw [Finset.univ_sum_single, AddEquiv.symm_apply_apply]

variable (M) in
/-- The vector of the coefficients read back out of its coordinates. -/
def coordInv : (Fin d → M) →ₗ[ℤ] M ⊗[ℤ] W :=
  intLinearOfAddHom
    { toFun := fun f => ∑ j, f j ⊗ₜ[ℤ] coordVec e j
      map_zero' := by simp
      map_add' := fun f g => by
        simp only [Pi.add_apply, TensorProduct.add_tmul]
        exact Finset.sum_add_distrib }

@[simp]
theorem coordInv_apply (f : Fin d → M) : coordInv M e f = ∑ j, f j ⊗ₜ[ℤ] coordVec e j := rfl

/-- A whole multiple crosses a tensor product over the integers. -/
theorem nsmul_tmul (n : ℕ) (m : M) (x : W) : (n • m) ⊗ₜ[ℤ] x = m ⊗ₜ[ℤ] (n • x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, TensorProduct.tmul_add, ih]

/-- Reading a vector of a finite power back into the tensor product and taking its coordinates
returns the vector. -/
theorem coordMap_coordInv (hM : ∀ m : M, p • m = 0) (f : Fin d → M) :
    coordMap e hM (coordInv M e f) = f := by
  refine funext fun l => ?_
  rw [coordInv_apply, map_sum, Finset.sum_apply]
  refine (Finset.sum_eq_single l ?_ ?_).trans ?_
  · intro j _ hj
    rw [coordMap_tmul, apply_coordVec, Pi.single_eq_of_ne (Ne.symm hj), ZMod.val_zero, zero_smul]
  · intro hl
    exact absurd (Finset.mem_univ l) hl
  · rw [coordMap_tmul, apply_coordVec, Pi.single_eq_same, ZMod.val_one, one_smul]

/-- Taking the coordinates of an element of the tensor product and reading them back returns the
element. -/
theorem coordInv_coordMap (hM : ∀ m : M, p • m = 0) (t : M ⊗[ℤ] W) :
    coordInv M e (coordMap e hM t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m x =>
      rw [coordInv_apply]
      calc ∑ j, coordMap e hM (m ⊗ₜ[ℤ] x) j ⊗ₜ[ℤ] coordVec e j
          = ∑ j, m ⊗ₜ[ℤ] ((e x j).val • coordVec e j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [coordMap_tmul, nsmul_tmul]
        _ = m ⊗ₜ[ℤ] ∑ j, (e x j).val • coordVec e j := by rw [TensorProduct.tmul_sum]
        _ = m ⊗ₜ[ℤ] x := by rw [sum_nsmul_coordVec]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

/-- **An abelian group killed by a prime, tensored with coefficients of finite rank over the field
with that many elements, is a finite power of the group.** -/
def coordEquiv (hM : ∀ m : M, p • m = 0) : M ⊗[ℤ] W ≃ₗ[ℤ] (Fin d → M) :=
  LinearEquiv.ofLinear (coordMap e hM) (coordInv M e)
    (LinearMap.ext (coordMap_coordInv e hM)) (LinearMap.ext (coordInv_coordMap e hM))

@[simp]
theorem coordEquiv_apply (hM : ∀ m : M, p • m = 0) (t : M ⊗[ℤ] W) :
    coordEquiv e hM t = coordMap e hM t := rfl

end Coord

/-! ### The tensor product of a product of representations -/

section Rep

variable {G ι : Type} [Group G] [Finite G] (A : ι → Rep ℤ G) (W : Rep ℤ G)

/-- **The canonical map from a product of representations tensored with a representation to the
product of the tensor products.** -/
def tensorPiHom : tensorObj (piRep A) W ⟶ piRep fun i => tensorObj (A i) W :=
  mkHom (LinearMap.pi fun i => TensorProduct.map (LinearMap.proj i) LinearMap.id) fun _ =>
    TensorProduct.ext' fun _ _ => rfl

omit [Finite G] in
@[simp]
theorem tensorPiHom_tmul (u : ↥(piRep A).V) (x : ↥W.V) (i : ι) :
    (tensorPiHom A W).hom.hom (u ⊗ₜ[ℤ] x) i = u i ⊗ₜ[ℤ] x := rfl

variable {p d : ℕ} [Fact p.Prime] (e : ↥W.V ≃+ (Fin d → ZMod p))
  (hA : ∀ i, ∀ m : ↥(A i).V, p • m = 0)

omit [Finite G] [Fact p.Prime] in
include hA in
/-- A product of groups each killed by a number is killed by it. -/
theorem nsmul_eq_zero_piRep (m : ↥(piRep A).V) : p • m = 0 :=
  funext fun i => hA i (m i)

omit [Finite G] in
include e hA in
/-- **The canonical map is bijective when the coefficients are of finite rank over the field with
`p` elements and every factor is killed by `p`.** -/
theorem bijective_tensorPiHom : Function.Bijective (tensorPiHom A W).hom.hom := by
  have hpi : ∀ m : ↥(piRep A).V, p • m = 0 := nsmul_eq_zero_piRep A hA
  have hkey : ∀ (t : ↥(tensorObj (piRep A) W).V) (i : ι) (j : Fin d),
      coordMap e (hA i) ((tensorPiHom A W).hom.hom t i) j = coordMap e hpi t j i :=
    fun t i j => coordMap_map e (piProj A i).hom.hom hpi (hA i) t j
  constructor
  · refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun t ht => ?_)
    refine (coordEquiv e hpi).injective (funext fun j => funext fun i => ?_)
    have ht' : (tensorPiHom A W).hom.hom t i = 0 := congrFun ht i
    have h := hkey t i j
    rw [ht', map_zero, Pi.zero_apply] at h
    show coordMap e hpi t j i = coordMap e hpi 0 j i
    simp only [map_zero, Pi.zero_apply]
    exact h.symm
  · intro s
    refine ⟨(coordEquiv e hpi).symm fun j i => coordMap e (hA i) (s i) j, funext fun i => ?_⟩
    refine (coordEquiv e (hA i)).injective (funext fun j => ?_)
    have hsymm : coordMap e hpi ((coordEquiv e hpi).symm fun j i => coordMap e (hA i) (s i) j)
        = fun j i => coordMap e (hA i) (s i) j := (coordEquiv e hpi).apply_symm_apply _
    show coordMap e (hA i)
        ((tensorPiHom A W).hom.hom ((coordEquiv e hpi).symm fun j i =>
          coordMap e (hA i) (s i) j) i) j = coordMap e (hA i) (s i) j
    rw [hkey, hsymm]

include e hA in
/-- **A product of representations killed by a prime, tensored with coefficients of finite rank
over the field with that many elements, is the product of the factors tensored with the
coefficients.** -/
def tensorPiIso : tensorObj (piRep A) W ≅ piRep fun i => tensorObj (A i) W :=
  isoOfBijective (tensorPiHom A W) (bijective_tensorPiHom A W e hA)

include e hA in
/-- **A product of representations killed by a prime, tensored with coefficients of finite rank
over the field with that many elements, has no complete cohomology in a degree in which no factor
tensored with the coefficients has any.** -/
theorem isZero_tateModule_tensorObj_piRep (n : ℤ)
    (h : ∀ i, Limits.IsZero (tateModule (tensorObj (A i) W) n)) :
    Limits.IsZero (tateModule (tensorObj (piRep A) W) n) :=
  isZero_tateModule_of_iso (tensorPiIso A W e hA) n
    (isZero_tateModule_piRep (fun i => tensorObj (A i) W) n h)

end Rep

end

end InverseGalois.CFT.Tate
