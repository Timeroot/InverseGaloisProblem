/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Cup

/-!
# The Cartier dual of a module of a topological group

Fix a group acting on an abelian group of coefficients, the roots of unity in practice.  The
*Cartier dual* of a module is the group of homomorphisms from it to those coefficients, with the
group acting by transporting the argument backwards and the value forwards.  Evaluation is then a
pairing of a module with its Cartier dual, equivariant for the two actions, and it is universal:
the map sending an element to evaluation at it is the comparison of a module with its double dual.

The pairing is what the duality theorems of global arithmetic are about.  Cupping a one cocycle
with values in a module against a one cocycle with values in the dual gives a two cocycle with
values in the coefficients, and for the absolute Galois group of a number field the coefficients
are the roots of unity, so the product is a Brauer class and its local invariants add up to zero.
Both factors being everywhere locally trivial is inherited by the product, so the pairing descends
to the everywhere locally trivial classes.

The action on the dual is smooth as soon as the actions on the module and on the coefficients are,
because an open normal subgroup acting trivially on both acts trivially on the homomorphisms
between them; so the dual of a module of a profinite group is again a module of the same kind and
the cohomology of the two can be compared.

## Main definitions

* `InverseGalois.CFT.CartierDual`: **the homomorphisms from a module to the coefficients**, with
  the conjugated action.
* `InverseGalois.CFT.CartierDual.evalPairing`: **evaluation, as a pairing of a module with its
  Cartier dual.**
* `InverseGalois.CFT.CartierDual.toDoubleDual`: the comparison of a module with its double dual.

## Main results

* `InverseGalois.CFT.CartierDual.evalPairing_smul`: **evaluation is equivariant.**
* `InverseGalois.CFT.CartierDual.toDoubleDual_smul`: the comparison with the double dual is
  equivariant.
* `InverseGalois.CFT.CartierDual.instIsSmoothAction`: **the dual of a smooth module is smooth.**

## Tags

Cartier dual, pairing, Galois cohomology, cup product, duality
-/

namespace InverseGalois.CFT

/-- **The Cartier dual** of a module relative to a group of coefficients: the homomorphisms from
the module to the coefficients.  A group acting on both acts on these by transporting the argument
backwards and the value forwards. -/
def CartierDual (A μ : Type*) [CommGroup A] [CommGroup μ] : Type _ := A →* μ

namespace CartierDual

variable {G A B μ : Type*} [CommGroup A] [CommGroup B] [CommGroup μ]

instance : CommGroup (CartierDual A μ) := inferInstanceAs (CommGroup (A →* μ))

instance : FunLike (CartierDual A μ) A μ := inferInstanceAs (FunLike (A →* μ) A μ)

instance : MonoidHomClass (CartierDual A μ) A μ :=
  inferInstanceAs (MonoidHomClass (A →* μ) A μ)

@[ext]
theorem ext {f g : CartierDual A μ} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

@[simp]
theorem mul_apply (f g : CartierDual A μ) (a : A) : (f * g) a = f a * g a := rfl

@[simp]
theorem one_apply (a : A) : (1 : CartierDual A μ) a = 1 := rfl

/-- A homomorphism to the coefficients, read as an element of the Cartier dual. -/
def ofHom (f : A →* μ) : CartierDual A μ := f

@[simp]
theorem ofHom_apply (f : A →* μ) (a : A) : ofHom f a = f a := rfl

/-! ### The action -/

section Action

variable [Group G] [MulDistribMulAction G A] [MulDistribMulAction G μ]

instance : SMul G (CartierDual A μ) where
  smul g f := ofHom
    { toFun := fun a => g • f (g⁻¹ • a)
      map_one' := by simp
      map_mul' := fun a b => by simp [smul_mul'] }

@[simp]
theorem smul_apply (g : G) (f : CartierDual A μ) (a : A) : (g • f) a = g • f (g⁻¹ • a) := rfl

instance : MulAction G (CartierDual A μ) where
  one_smul f := ext fun a => by simp
  mul_smul g h f := ext fun a => by simp [mul_smul, mul_inv_rev]

instance : MulDistribMulAction G (CartierDual A μ) where
  smul_mul g f₁ f₂ := ext fun a => by simp [smul_mul']
  smul_one g := ext fun a => by simp

/-- **The value of a translated homomorphism at a translated argument is the translated value.** -/
theorem smul_apply_smul (g : G) (f : CartierDual A μ) (a : A) : (g • f) (g • a) = g • f a := by
  simp

end Action

/-! ### Evaluation -/

section Pairing

variable [Group G] [MulDistribMulAction G A] [MulDistribMulAction G μ]

variable (A μ) in
/-- **Evaluation, as a pairing of a module with its Cartier dual.** -/
def evalPairing : A →* CartierDual A μ →* μ where
  toFun a :=
    { toFun := fun f => f a
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  map_one' := MonoidHom.ext fun f => map_one f
  map_mul' a b := MonoidHom.ext fun f => map_mul f a b

@[simp]
theorem evalPairing_apply (a : A) (f : CartierDual A μ) : evalPairing A μ a f = f a := rfl

/-- **Evaluation is equivariant**: the pairing of a translated element with a translated
homomorphism is the translated pairing. -/
theorem evalPairing_smul (g : G) (a : A) (f : CartierDual A μ) :
    evalPairing A μ (g • a) (g • f) = g • evalPairing A μ a f :=
  smul_apply_smul g f a

variable (A μ) in
/-- The comparison of a module with its double dual: an element is sent to evaluation at it. -/
def toDoubleDual : A →* CartierDual (CartierDual A μ) μ := evalPairing A μ

@[simp]
theorem toDoubleDual_apply (a : A) (f : CartierDual A μ) : toDoubleDual A μ a f = f a := rfl

/-- **The comparison of a module with its double dual is equivariant.** -/
theorem toDoubleDual_smul (g : G) (a : A) :
    toDoubleDual A μ (g • a) = g • toDoubleDual A μ a :=
  ext fun f => by simp

end Pairing

/-! ### Smoothness -/

section Smooth

variable [Group G] [TopologicalSpace G] [MulDistribMulAction G A] [MulDistribMulAction G μ]

/-- **The Cartier dual of a smooth module is smooth**: an open normal subgroup acting trivially on
the module and on the coefficients acts trivially on the homomorphisms between them. -/
instance [IsSmoothAction G A] [IsSmoothAction G μ] :
    IsSmoothAction G (CartierDual A μ) where
  exists_isOpenNormal := by
    obtain ⟨N, hN, hNA⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := A)
    obtain ⟨N', hN', hNμ⟩ := IsSmoothAction.exists_isOpenNormal (G := G) (M := μ)
    refine ⟨N ⊓ N', hN.inf hN', fun n hn f => ext fun a => ?_⟩
    rw [smul_apply, hNA n⁻¹ (inv_mem hn.1) a, hNμ n hn.2 (f a)]

end Smooth

end CartierDual

end InverseGalois.CFT
