/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.TateTheorem

/-!
# Restriction to a subgroup in degree one

Restriction to a subgroup was built degree by degree out of the two identifications that raise and
lower the degree, and in degree one it therefore reads as a connecting map followed by restriction
in degree zero.  On a cocycle it is nevertheless the obvious thing: the cocycle read on the
subgroup.

The comparison rests on two computations.  The connecting map out of degree zero is computed on a
lift of an invariant vector and on the cochain measuring the failure of that lift to be invariant;
restricting the lift and the cochain to the subgroup computes the connecting map of the restricted
extension, which is the naturality of the connecting map.  And in the extension defining the shift,
a cocycle is its own lift: the record of all the translates of the value of a cocycle at an element
is the difference of the translate of the cocycle and the cocycle, which is precisely the cocycle
identity.  So the class of a cocycle in the shift is invariant and the connecting map carries it to
the class of the cocycle.

## Main definitions

* `InverseGalois.CFT.Tate.shiftInvariants`: the invariant vector of the shift attached to a cocycle
  in degree one.

## Main results

* `InverseGalois.CFT.Tate.H0toH1_res_eq_H1π`: **the connecting map out of degree zero is natural
  for restriction to a subgroup.**
* `InverseGalois.CFT.Tate.H0toH1_shiftSeq`: **the connecting map of the extension defining the
  shift carries the class of a cocycle to the class of that cocycle.**
* `InverseGalois.CFT.Tate.tateRes_one_H1π`: **restriction to a subgroup in degree one carries the
  class of a cocycle to the class of the cocycle read on the subgroup.**

## Tags

Tate cohomology, restriction, dimension shifting, cocycle
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Naturality of the connecting map out of degree zero -/

section Naturality

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (H : Subgroup G)

/-- **The connecting map out of degree zero is natural for restriction to a subgroup**: a lift of
an invariant vector and the cochain measuring its failure to be invariant compute the connecting
map of the restricted extension just as well. -/
theorem H0toH1_res_eq_H1π (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = (z : X.X₃))
    (x : groupCohomology.cocycles₁ X.X₁)
    (hx : X.f.hom ∘ (x : G → X.X₁) = groupCohomology.d₀₁ X.X₂ y) :
    H0toH1 (resSeq_shortExact hX H) (res0 H X.X₃.ρ (H0mk X.X₃.ρ z))
      = groupCohomology.H1π (resObj H X.X₁) (resCocycles₁ H X.X₁ x) := by
  rw [res0_H0mk]
  refine H0toH1_eq_H1π (X := resSeq H X) (resSeq_shortExact hX H) (resInvariants H X.X₃.ρ z) y hy
    (resCocycles₁ H X.X₁ x) ?_
  exact funext fun h => congrFun hx (h : G)

end Naturality

/-! ### A cocycle is its own lift in the extension defining the shift -/

section Shift

variable (A : Rep k G) (b : groupCohomology.cocycles₁ A)

omit [Finite G] in
/-- **The record of all the translates of the value of a cocycle** is the difference between the
translate of the cocycle and the cocycle itself. -/
theorem coindEmb_comp_eq_d₀₁ :
    (shiftSeq A).f.hom ∘ (b : G → ↥A.V) = groupCohomology.d₀₁ (indObj A) (b : G → ↥A.V) := by
  have h : ∀ g x : G, A.ρ x (b g) = b (x * g) - b x := fun g x => by
    rw [(groupCohomology.mem_cocycles₁_iff (b : G → ↥A.V)).1 b.2 x g, add_sub_cancel_right]
  exact funext fun g => funext fun x => h g x

omit [Finite G] in
/-- **The class of a cocycle in the shift is invariant.** -/
theorem mem_invariants_mkQ_cocycles₁ :
    (LinearMap.range (coindEmb A.ρ)).mkQ (b : G → ↥A.V) ∈ (shiftObj A).ρ.invariants := by
  intro g
  show (LinearMap.range (coindEmb A.ρ)).mkQ ((indObj A).ρ g (b : G → ↥A.V))
    = (LinearMap.range (coindEmb A.ρ)).mkQ (b : G → ↥A.V)
  exact (Submodule.Quotient.eq _).2 ⟨b g, congrFun (coindEmb_comp_eq_d₀₁ A b) g⟩

/-- **The invariant vector of the shift attached to a cocycle in degree one.** -/
def shiftInvariants : (shiftObj A).ρ.invariants :=
  ⟨(LinearMap.range (coindEmb A.ρ)).mkQ (b : G → ↥A.V), mem_invariants_mkQ_cocycles₁ A b⟩

/-- **The connecting map of the extension defining the shift carries the class of a cocycle to the
class of that cocycle.** -/
theorem H0toH1_shiftSeq :
    H0toH1 (shiftSeq_shortExact A) (H0mk (shiftObj A).ρ (shiftInvariants A b))
      = groupCohomology.H1π A b :=
  H0toH1_eq_H1π (X := shiftSeq A) (shiftSeq_shortExact A) (shiftInvariants A b)
    (b : G → ↥A.V) rfl b (coindEmb_comp_eq_d₀₁ A b)

/-- **The connecting map of the extension defining the shift, read on a subgroup, carries the class
of a cocycle to the class of the cocycle read on the subgroup.** -/
theorem H0toH1_resSeq_shiftSeq (H : Subgroup G) :
    H0toH1 (resSeq_shortExact (shiftSeq_shortExact A) H)
        (res0 H (shiftObj A).ρ (H0mk (shiftObj A).ρ (shiftInvariants A b)))
      = groupCohomology.H1π (resObj H A) (resCocycles₁ H A b) :=
  H0toH1_res_eq_H1π (shiftSeq_shortExact A) H (shiftInvariants A b) (b : G → ↥A.V) rfl b
    (coindEmb_comp_eq_d₀₁ A b)

/-! ### Restriction in degree one -/

/-- Restriction in degree one is the identification with degree zero of the shift, followed by
restriction in degree zero and the identification read on the subgroup. -/
theorem tateRes_one (H : Subgroup G) :
    tateRes H A 1 = (resShiftEquiv H A 0).toLinearMap ∘ₗ res0 H (shiftObj A).ρ ∘ₗ
      (tateShiftEquiv A 0).symm.toLinearMap := rfl

/-- **Restriction to a subgroup in degree one carries the class of a cocycle to the class of the
cocycle read on the subgroup.** -/
theorem tateRes_one_H1π (H : Subgroup G) :
    tateRes H A 1 (groupCohomology.H1π A b)
      = groupCohomology.H1π (resObj H A) (resCocycles₁ H A b) := by
  have h : (tateShiftEquiv A 0).symm
      (H0toH1 (shiftSeq_shortExact A) (H0mk (shiftObj A).ρ (shiftInvariants A b)))
      = H0mk (shiftObj A).ρ (shiftInvariants A b) :=
    (tateShiftEquiv A 0).symm_apply_apply _
  rw [← H0toH1_shiftSeq A b]
  show resShiftEquiv H A 0 (res0 H (shiftObj A).ρ ((tateShiftEquiv A 0).symm
      (H0toH1 (shiftSeq_shortExact A) (H0mk (shiftObj A).ρ (shiftInvariants A b)))))
    = groupCohomology.H1π (resObj H A) (resCocycles₁ H A b)
  rw [h]
  exact H0toH1_resSeq_shiftSeq A b H

end Shift

end

end InverseGalois.CFT.Tate
