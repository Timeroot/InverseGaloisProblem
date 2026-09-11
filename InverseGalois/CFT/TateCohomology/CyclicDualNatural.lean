/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.CyclicDual

/-!
# The pairing of a cyclic representation, along a map of coefficients

The complete cohomology of the maps out of a cyclic representation is dual to the complete
cohomology of the maps into it, in complementary degrees.  A map of the target of those maps moves
both sides at once, and in opposite directions: the maps *into* the target are carried forward by
composing after, the maps *out of* it are carried backward by composing before.  What is proven here
is that the pairing does not notice the difference - **pairing the pushed class against a class
downstairs is pairing the class upstairs against the pulled one.**

This is the compatibility a shrinking argument runs on.  A class of complete cohomology in degree
minus two is produced from an obstruction before any change of coefficients is chosen; the change is
chosen afterwards, and what has to be known is that killing the class kills the character it cuts
out.  The naturality proven here is exactly that transfer, and it needs nothing beyond the two
compatibilities already available: that the duality of complete cohomology against the rational
circle is natural, and that composing before and composing after agree inside the pairing.

## Main definitions

* `InverseGalois.CFT.Tate.linHomPostHom`: the maps into a representation, carried forward along a
  map of that representation.
* `InverseGalois.CFT.Tate.linHomPreHom`: the maps out of a representation, carried backward along a
  map of that representation.

## Main results

* `InverseGalois.CFT.Tate.cartierHom_naturality`: composing after and composing before agree under
  the pairing of a cyclic representation.
* `InverseGalois.CFT.Tate.cartierPairing_naturality`: **the duality of the complete cohomology of a
  cyclic representation is compatible with every map of the coefficients.**

## Tags

Tate cohomology, duality, naturality, cyclic representation, Cartier dual
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

noncomputable section

universe u

/-! ### Composing with a map of representations -/

section LinHom

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) {B B' : Rep k G} (f : B ⟶ B')

/-- The maps into a representation, carried forward by composing after a map of it. -/
def linHomPostLinear : ↥(linHomObj A B).V →ₗ[k] ↥(linHomObj A B').V :=
  LinearMap.llcomp k ↥A.V ↥B.V ↥B'.V f.hom.hom

theorem linHomPostLinear_apply (x : ↥A.V →ₗ[k] ↥B.V) :
    linHomPostLinear A f x = f.hom.hom.comp x := rfl

theorem linHomPostLinear_equivariant (g : G) :
    linHomPostLinear A f ∘ₗ (linHomObj A B).ρ g
      = (linHomObj A B').ρ g ∘ₗ linHomPostLinear A f := by
  refine LinearMap.ext fun (x : ↥A.V →ₗ[k] ↥B.V) => LinearMap.ext fun a => ?_
  show f.hom.hom (B.ρ g (x (A.ρ g⁻¹ a))) = B'.ρ g (f.hom.hom (x (A.ρ g⁻¹ a)))
  exact Rep.hom_comm_apply f g _

/-- **The maps into a representation, along a map of that representation.**  A map into the source
is read into the target by composing after it. -/
def linHomPostHom : linHomObj A B ⟶ linHomObj A B' :=
  mkHom (linHomPostLinear A f) (linHomPostLinear_equivariant A f)

theorem linHomPostHom_hom : (linHomPostHom A f).hom.hom = linHomPostLinear A f := rfl

/-- The maps out of a representation, carried backward by composing before a map of it. -/
def linHomPreLinear : ↥(linHomObj B' A).V →ₗ[k] ↥(linHomObj B A).V :=
  LinearMap.lcomp k ↥A.V f.hom.hom

theorem linHomPreLinear_apply (x : ↥B'.V →ₗ[k] ↥A.V) :
    linHomPreLinear A f x = x.comp f.hom.hom := rfl

theorem linHomPreLinear_equivariant (g : G) :
    linHomPreLinear A f ∘ₗ (linHomObj B' A).ρ g
      = (linHomObj B A).ρ g ∘ₗ linHomPreLinear A f := by
  refine LinearMap.ext fun (x : ↥B'.V →ₗ[k] ↥A.V) => LinearMap.ext fun b => ?_
  show A.ρ g (x (B'.ρ g⁻¹ (f.hom.hom b))) = A.ρ g (x (f.hom.hom (B.ρ g⁻¹ b)))
  exact congrArg (fun y => A.ρ g (x y)) (LinearMap.congr_fun (hom_equivariant f g⁻¹) b).symm

/-- **The maps out of a representation, along a map of that representation.**  A map out of the
target is read on the source by composing before it, which reverses the direction. -/
def linHomPreHom : linHomObj B' A ⟶ linHomObj B A :=
  mkHom (linHomPreLinear A f) (linHomPreLinear_equivariant A f)

theorem linHomPreHom_hom : (linHomPreHom A f).hom.hom = linHomPreLinear A f := rfl

end LinHom

/-! ### The pairing along a map of coefficients -/

section Cartier

variable {G : Type} [Group G] (A : Rep ℤ G) [IsAddCyclic ↥A.V] [Finite ↥A.V] {B B' : Rep ℤ G}
  (f : B ⟶ B')

/-- **Composing after and composing before agree under the pairing of a cyclic representation.**
Both readings of a map out of the target, tested on a map into the source, compose the three maps
in the same order and read the value off with the same character. -/
theorem cartierHom_naturality :
    cartierHom A B' ≫ coeffDualHom (linHomPostHom A f) (AddCircle (1 : ℚ))
      = linHomPreHom A f ≫ cartierHom A B :=
  Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

variable [Finite G] [Finite ↥B.V] [Finite ↥B'.V]

theorem cartierPairing_apply (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) (n : ℤ)
    (x : ↥(tateModule (linHomObj A B) n)) (c : ↥(tateModule (linHomObj B A) (-n - 1))) :
    cartierPairing A B hB n x c
      = tateDualPairing (linHomObj A B) n x (tateMap (cartierHom A B) (-n - 1) c) := rfl

/-- **The duality of the complete cohomology of a cyclic representation is compatible with every
map of the coefficients.**  A class carried forward along the map, paired with a class of the
complementary degree downstairs, is the class itself paired with that class carried backward. -/
theorem cartierPairing_naturality (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0)
    (hB' : ∀ b : ↥B'.V, Nat.card ↥A.V • b = 0) (n : ℤ)
    (x : ↥(tateModule (linHomObj A B) n)) (c : ↥(tateModule (linHomObj B' A) (-n - 1))) :
    cartierPairing A B' hB' n (tateMap (linHomPostHom A f) n x) c
      = cartierPairing A B hB n x (tateMap (linHomPreHom A f) (-n - 1) c) := by
  rw [cartierPairing_apply, cartierPairing_apply,
    tateDualPairing_naturality (linHomPostHom A f) n x, tateMap_comp_apply, cartierHom_naturality,
    ← tateMap_comp_apply]

end Cartier

end

end InverseGalois.CFT.Tate
