/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.LayerPi

/-!
# Coordinates of a layer

A layer of the descending central series is a finite vector space over the field with `ℓ` elements,
so once a basis of it is named every element has coordinates and a homomorphism into it is nothing
but a tuple of additive characters with values in that field.  This file names the coordinates and
records the dictionary.

The generation clauses of the ladder never needed this: a family indexed by the elements of the
layer generates it whatever the coordinates are.  A clause asking a homomorphism to take *given*
values on a subgroup does need it, since a prescription is made coordinate by coordinate and the
values are then reassembled.

## Main definitions

* `InverseGalois.Shafarevich.layerDim` — the dimension of a layer over the field with `ℓ` elements.
* `InverseGalois.Shafarevich.layerCoord` — the coordinates of an element of a layer.
* `InverseGalois.Shafarevich.layerBasis` — the basis the coordinates are read against.
* `InverseGalois.Shafarevich.layerHomOfCoord` — **the homomorphism into a layer assembled from a
  tuple of additive characters.**

## Main results

* `InverseGalois.Shafarevich.layerSub_ext` — an element of a layer is determined by its coordinates.
* `InverseGalois.Shafarevich.prod_layerBasis_pow_layerCoord` — **an element of a layer is the
  product of the powers of the basis by its coordinates.**
* `InverseGalois.Shafarevich.layerCoord_layerHomOfCoord` — the coordinates of the assembled
  homomorphism are the characters it was assembled from.
* `InverseGalois.Shafarevich.layerHomOfCoord_eq_of_coord_eq` — **the assembled homomorphism agrees
  with a prescribed one wherever its characters are the coordinates of that one.**

## Tags

p-central series, elementary abelian, basis, character, coordinates
-/

namespace InverseGalois.Shafarevich

section Coord

variable (ℓ : ℕ) [Fact ℓ.Prime] (P : Type*) [Group P] [Finite P] (j : ℕ)

/-- The dimension of a layer of the descending central series over the field with `ℓ` elements. -/
noncomputable abbrev layerDim : ℕ := Module.finrank (ZMod ℓ) (Layer ℓ P j)

/-- **A layer is the tuple of its coordinates**, a basis of it over the field with `ℓ` elements
having been named. -/
noncomputable def layerCoordEquiv :
    ↥(layerSub ℓ P j) ≃* (Fin (layerDim ℓ P j) → Multiplicative (ZMod ℓ)) :=
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  layerPiMulEquiv ℓ P j (Multiplicative (ZMod ℓ)) (by simp [Nat.card_eq_fintype_card])

/-- The coordinates of an element of a layer. -/
noncomputable def layerCoord (e : ↥(layerSub ℓ P j)) (i : Fin (layerDim ℓ P j)) : ZMod ℓ :=
  (layerCoordEquiv ℓ P j e i).toAdd

/-- The basis of a layer the coordinates are read against. -/
noncomputable def layerBasis (t : Fin (layerDim ℓ P j)) : ↥(layerSub ℓ P j) :=
  (layerCoordEquiv ℓ P j).symm (Pi.mulSingle t (Multiplicative.ofAdd (1 : ZMod ℓ)))

variable {ℓ P j}

/-- An element of the basis of a layer is killed by the exponent. -/
theorem layerBasis_pow_eq_one (t : Fin (layerDim ℓ P j)) : layerBasis ℓ P j t ^ ℓ = 1 :=
  layerSub_pow_eq_one ℓ P j _

/-- **An element of a layer is the product of the powers of the basis by its coordinates.** -/
theorem prod_layerBasis_pow_layerCoord (e : ↥(layerSub ℓ P j)) :
    ∏ t, layerBasis ℓ P j t ^ (layerCoord ℓ P j e t).val = e := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine (layerCoordEquiv ℓ P j).injective (funext fun t => ?_)
  rw [_root_.map_prod]
  simp only [layerBasis, _root_.map_pow, MulEquiv.apply_symm_apply]
  rw [Finset.prod_apply, Finset.prod_eq_single t]
  · rw [Pi.pow_apply, Pi.mulSingle_eq_same, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
      ZMod.natCast_rightInverse _]
    rfl
  · intro s _ hs
    rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne (Ne.symm hs), one_pow]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- An element of a layer is determined by its coordinates. -/
theorem layerSub_ext {e e' : ↥(layerSub ℓ P j)}
    (h : ∀ i, layerCoord ℓ P j e i = layerCoord ℓ P j e' i) : e = e' := by
  refine (layerCoordEquiv ℓ P j).injective (funext fun i => ?_)
  exact Multiplicative.toAdd.injective (h i)

/-- The coordinates of a product are the sums of the coordinates. -/
theorem layerCoord_mul (e e' : ↥(layerSub ℓ P j)) (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (e * e') i = layerCoord ℓ P j e i + layerCoord ℓ P j e' i := by
  show ((layerCoordEquiv ℓ P j (e * e')) i).toAdd = _
  rw [_root_.map_mul]
  rfl

/-- The coordinates of the identity vanish. -/
theorem layerCoord_one (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (1 : ↥(layerSub ℓ P j)) i = 0 := by
  show ((layerCoordEquiv ℓ P j 1) i).toAdd = _
  rw [_root_.map_one]
  rfl

end Coord

/-! ### Assembling a homomorphism from its coordinates -/

section One

variable {G A : Type*} [Group G] [AddGroup A]

/-- A map turning products into sums kills the identity. -/
theorem map_one_eq_zero_of_map_mul_eq_add {f : G → A} (hf : ∀ x y : G, f (x * y) = f x + f y) :
    f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one] at h
  refine add_left_cancel (a := f 1) ?_
  rw [add_zero]
  exact h.symm

end One

section Assemble

variable {ℓ : ℕ} [Fact ℓ.Prime] {P : Type*} [Group P] [Finite P] {j : ℕ} {G : Type*} [Group G]
  (f : Fin (layerDim ℓ P j) → G → ZMod ℓ) (hf : ∀ i, ∀ x y : G, f i (x * y) = f i x + f i y)

/-- **The homomorphism into a layer assembled from a tuple of additive characters.** -/
noncomputable def layerHomOfCoord : G →* ↥(layerSub ℓ P j) :=
  (layerCoordEquiv ℓ P j).symm.toMonoidHom.comp
    { toFun := fun x i => Multiplicative.ofAdd (f i x)
      map_one' := funext fun i =>
        congrArg Multiplicative.ofAdd (map_one_eq_zero_of_map_mul_eq_add (hf i))
      map_mul' := fun x y => funext fun i => congrArg Multiplicative.ofAdd (hf i x y) }

set_option maxRecDepth 4000 in
/-- The coordinates of the assembled homomorphism are the characters it was assembled from. -/
theorem layerCoord_layerHomOfCoord (x : G) (i : Fin (layerDim ℓ P j)) :
    layerCoord ℓ P j (layerHomOfCoord f hf x) i = f i x := by
  show ((layerCoordEquiv ℓ P j ((layerCoordEquiv ℓ P j).symm
    (fun i => Multiplicative.ofAdd (f i x)))) i).toAdd = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- **The assembled homomorphism agrees with a prescribed one wherever its characters are the
coordinates of that one.** -/
theorem layerHomOfCoord_eq_of_coord_eq {A : Subgroup G} (a : ↥A →* ↥(layerSub ℓ P j))
    (h : ∀ (i : Fin (layerDim ℓ P j)) (x : ↥A), f i (x : G) = layerCoord ℓ P j (a x) i)
    (x : ↥A) : layerHomOfCoord f hf (x : G) = a x :=
  layerSub_ext fun i => by rw [layerCoord_layerHomOfCoord f hf, h i x]

end Assemble

end InverseGalois.Shafarevich
