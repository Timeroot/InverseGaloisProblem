/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerCoord

/-!
# The matrix of a comparison map between layers

A basis of a layer having been named, an element of it is the product of the powers of the basis by
its coordinates, so a homomorphism of groups induces on the layers a map whose coordinates are read
off from its values on the basis: the coordinates of the image are the matrix of those values
against the coordinates of the argument.

That matrix is the only thing the reciprocity residue is compared against.  The arithmetic names,
at the higher level, one local class for each basis vector, and the prescription at the lower level
asks for one local class for each basis vector *there*; the two are related by exactly this matrix,
so an identity holding coordinate by coordinate upstairs is carried downstairs by it.

## Main results

* `InverseGalois.Shafarevich.layerCoord_prod` — the coordinates of a product are the sums of the
  coordinates.
* `InverseGalois.Shafarevich.layerCoord_pow` — the coordinates of a power are the multiples of the
  coordinates.
* `InverseGalois.Shafarevich.layerCoord_layerBasis` — the coordinates of a basis vector.
* `InverseGalois.Shafarevich.layerCoord_prod_layerBasis_pow` — **the coordinates of a product of
  powers of the basis are the exponents.**
* `InverseGalois.Shafarevich.layerCoord_layerSubMap` — **the coordinates of the image of an element
  under a comparison map are the matrix of the images of the basis against its coordinates.**

## Tags

p-central series, elementary abelian, basis, coordinates, matrix
-/

namespace InverseGalois.Shafarevich

section Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q] {j : ℕ}

/-- The coordinates of a product over a finite index set are the sums of the coordinates. -/
theorem layerCoord_prod {ι : Type*} (s : Finset ι) (g : ι → ↥(layerSub ℓ P j))
    (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (∏ t ∈ s, g t) i = ∑ t ∈ s, layerCoord ℓ P j (g t) i := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, layerCoord_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, layerCoord_mul, ih]

/-- The coordinates of a power are the multiples of the coordinates. -/
theorem layerCoord_pow (e : ↥(layerSub ℓ P j)) (m : ℕ) (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (e ^ m) i = (m : ZMod ℓ) * layerCoord ℓ P j e i := by
  induction m with
  | zero => rw [pow_zero, layerCoord_one, Nat.cast_zero, zero_mul]
  | succ m ih =>
      rw [pow_succ, layerCoord_mul, ih]
      push_cast
      ring

/-- The coordinates of a basis vector: one in its own place and zero elsewhere. -/
theorem layerCoord_layerBasis (t i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (layerBasis ℓ P j t) i = if i = t then 1 else 0 := by
  show ((layerCoordEquiv ℓ P j ((layerCoordEquiv ℓ P j).symm
    (Pi.mulSingle t (Multiplicative.ofAdd (1 : ZMod ℓ))))) i).toAdd = _
  rw [MulEquiv.apply_symm_apply, Pi.mulSingle_apply]
  split_ifs with h
  · rfl
  · rfl

/-- **The coordinates of a product of powers of the basis are the exponents.** -/
theorem layerCoord_prod_layerBasis_pow (v : Fin (layerDim ℓ P j) → ZMod ℓ)
    (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (∏ t, layerBasis ℓ P j t ^ (v t).val) i = v i := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [layerCoord_prod, Finset.sum_eq_single i]
  · rw [layerCoord_pow, layerCoord_layerBasis, if_pos rfl, mul_one,
      ZMod.natCast_rightInverse (v i)]
  · intro t _ ht
    rw [layerCoord_pow, layerCoord_layerBasis, if_neg (Ne.symm ht), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The coordinates of the image of an element under a comparison map are the matrix of the
images of the basis against its coordinates.** -/
theorem layerCoord_layerSubMap (f : P →* Q) (e : ↥(layerSub ℓ P j))
    (q : Fin (layerDim ℓ Q j)) :
    layerCoord ℓ Q j (layerSubMap ℓ f j e) q = ∑ t, layerCoord ℓ P j e t *
      layerCoord ℓ Q j (layerSubMap ℓ f j (layerBasis ℓ P j t)) q := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  conv_lhs => rw [← prod_layerBasis_pow_layerCoord e]
  rw [_root_.map_prod, layerCoord_prod]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [_root_.map_pow, layerCoord_pow, ZMod.natCast_rightInverse (layerCoord ℓ P j e t)]

omit [Fact ℓ.Prime] [Finite P] [Finite Q] in
/-- The linear map of layers induced by a homomorphism is the homomorphism of the multiplicative
layers. -/
theorem layerLinear_eq_layerSubMap (f : P →* Q) (v : Layer ℓ P j) :
    Additive.toMul (layerLinear ℓ f j v) = layerSubMap ℓ f j (Additive.toMul v) := rfl

end Matrix

end InverseGalois.Shafarevich
