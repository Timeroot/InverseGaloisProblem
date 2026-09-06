/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.UnramifiedCoboundary
import InverseGalois.CFT.Tate.TensorSplit
import InverseGalois.CFT.TateCohomology.Shifting
import InverseGalois.CFT.Units.IdeleRep

/-!
# A uniformizer of the base field splits the units of the valuation ring off the local factor

Let a group act on a valued field by isometries and fix a uniformizer of the field that every
element of the group leaves alone.  Subtracting from a unit the appropriate power of that
uniformizer is a homomorphism onto the units of the valuation ring which commutes with the action
and restricts to the identity on those units, so **the units of the valuation ring are a retract of
the units of the field as representations of the group.**

For untwisted coefficients this is not needed: at an unramified place the units of the valuation
ring have no complete cohomology whatsoever, so the place drops out of the description of the
cohomology of the ideles.  After tensoring the coefficients with a representation killed by a prime
that vanishing is gone, and what replaces it is the retraction: a retract stays a retract after
tensoring and after passing to complete cohomology, so the contribution of the units of the
valuation ring is a subgroup of the contribution of the whole local factor rather than zero.  That
is exactly what is needed to compare the ideles that are units outside a finite set with the full
product over the places.

## Main definitions

* `InverseGalois.CFT.kerUnitValHom`: the units of the valuation ring inside the units of the field,
  as a map of representations.
* `InverseGalois.CFT.unitValRetract`: **the retraction cut out by a fixed uniformizer.**

## Main results

* `InverseGalois.CFT.kerUnitValHom_comp_unitValRetract`: **the retraction is a left inverse of the
  inclusion.**
* `InverseGalois.CFT.injective_tateMap_tensorHomLeft_kerUnitValHom`: **the complete cohomology of
  the units of the valuation ring, with coefficients twisted by a representation, injects into that
  of the units of the field.**

## Tags

valued field, uniformizer, local units, retraction, Tate cohomology, tensor product
-/

namespace InverseGalois.CFT

open CategoryTheory Tate

open scoped WithZero

noncomputable section

variable {G A : Type} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

/-! ### The inclusion of the units of the valuation ring -/

/-- **The units of the valuation ring inside the units of the field**, as a map of representations
of a group acting by isometries. -/
def kerUnitValHom :
    repOfAddAut (kerUnitValAutHom hv) ⟶ repOfAddAut (smulUnitsAut (G := G) (R := A)) :=
  mkHom (unitVal (A := A)).ker.subtype.toIntLinearMap fun _ => LinearMap.ext fun _ => rfl

/-! ### The retraction cut out by a fixed uniformizer -/

section Uniformizer

variable (π : Aˣ) (hπval : unitVal (Additive.ofMul π) = 1)

/-- A unit of the field with the appropriate power of a uniformizer taken out is a unit of the
valuation ring, and the passage is additive. -/
def unitValSplitHom : Additive Aˣ →+ ↥(unitVal (A := A)).ker where
  toFun x := ⟨x - unitVal x • Additive.ofMul π, by
    rw [AddMonoidHom.mem_ker, map_sub, map_zsmul, hπval, smul_eq_mul, mul_one, sub_self]⟩
  map_zero' := Subtype.ext (by
    show (0 : Additive Aˣ) - unitVal 0 • Additive.ofMul π = (0 : Additive Aˣ)
    rw [map_zero, zero_zsmul, sub_zero])
  map_add' x y := Subtype.ext (by
    show x + y - unitVal (x + y) • Additive.ofMul π
      = x - unitVal x • Additive.ofMul π + (y - unitVal y • Additive.ofMul π)
    rw [map_add, add_zsmul]
    abel)

theorem coe_unitValSplitHom (x : Additive Aˣ) :
    ((unitValSplitHom π hπval x : ↥(unitVal (A := A)).ker) : Additive Aˣ)
      = x - unitVal x • Additive.ofMul π := rfl

variable (hπfix : ∀ g : G, g • (π : A) = (π : A))

omit [Valued A ℤᵐ⁰] in
include hπfix in
/-- A uniformizer left alone by the group is left alone by the induced action on the units. -/
theorem smulUnitsAut_of_fixed (g : G) :
    smulUnitsAut (R := A) g (Additive.ofMul π) = Additive.ofMul π := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [coe_smulUnitsAut_apply]
  exact hπfix g

include hv hπfix in
/-- Taking out the appropriate power of a fixed uniformizer commutes with the action. -/
theorem unitValSplitHom_equivariant (g : G) (x : Additive Aˣ) :
    unitValSplitHom π hπval (smulUnitsAut g x)
      = kerUnitValAut hv g (unitValSplitHom π hπval x) :=
  Subtype.ext <| by
    show smulUnitsAut g x - unitVal (smulUnitsAut g x) • Additive.ofMul π
      = smulUnitsAut g (x - unitVal x • Additive.ofMul π)
    rw [map_sub, map_zsmul, smulUnitsAut_of_fixed π hπfix, unitVal_smulUnitsAut hv]

include hv hπfix in
/-- **The retraction cut out by a fixed uniformizer**: a unit of the field with the appropriate
power of the uniformizer taken out, read as a map of representations. -/
def unitValRetract :
    repOfAddAut (smulUnitsAut (G := G) (R := A)) ⟶ repOfAddAut (kerUnitValAutHom hv) :=
  mkHom (unitValSplitHom π hπval).toIntLinearMap fun g =>
    LinearMap.ext fun x => unitValSplitHom_equivariant hv π hπval hπfix g x

include hv hπfix in
/-- **The retraction cut out by a fixed uniformizer is a left inverse of the inclusion**: a unit of
the valuation ring has nothing to take out. -/
theorem kerUnitValHom_comp_unitValRetract :
    kerUnitValHom hv ≫ unitValRetract hv π hπval hπfix = 𝟙 _ := by
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_))
  have hx : unitVal x.1 = 0 := AddMonoidHom.mem_ker.1 x.2
  show x.1 - unitVal x.1 • Additive.ofMul π = x.1
  rw [hx, zero_zsmul, sub_zero]

variable [Finite G]

include hv hπval hπfix in
/-- **The complete cohomology of the units of the valuation ring, with coefficients twisted by a
representation, injects into that of the units of the field.**  A fixed uniformizer makes the
inclusion a retract, and a retract stays a retract after tensoring and after passing to complete
cohomology. -/
theorem injective_tateMap_tensorHomLeft_kerUnitValHom (M : Rep ℤ G) (n : ℤ) :
    Function.Injective (tateMap (tensorHomLeft M (kerUnitValHom hv)) n) :=
  injective_tateMap_tensorHomLeft_of_retraction _ (unitValRetract hv π hπval hπfix)
    (kerUnitValHom_comp_unitValRetract hv π hπval hπfix) M n

end Uniformizer

end

end InverseGalois.CFT
