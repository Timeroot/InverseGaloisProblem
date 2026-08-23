/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.InfiniteAction
import InverseGalois.CFT.Local.UnitValuation
import InverseGalois.CFT.Tate.FamilyRing

/-!
# The Galois action on the family of completions at the infinite places

This is the archimedean counterpart of the action on the completions at the finite places.  A
Galois automorphism of a number field carries the completion at an infinite place isomorphically
onto the completion at the image place, and doing this for every infinite place at once presents
the completions as a family of rings carrying an action of the Galois group; the group then acts on
the sections of the family and on the sections of the family of unit groups, which are the
archimedean components of the group of ideles.

As at the finite places, the compatibility of the transports is checked on the image of the field,
which is dense in each completion, and extends by continuity.

## Main definitions

* `InverseGalois.CFT.infiniteCoe`: the section of the family of completions determined by an
  element of the field.
* `InverseGalois.CFT.infiniteRingFamily`: **the Galois action on the family of completions at the
  infinite places.**

## Main results

* `InverseGalois.CFT.infiniteCompletionGalEquiv_infiniteCoe`: the transport carries the section
  determined by an element of the field to the section determined by its image.
* `InverseGalois.CFT.transport_infiniteUnitsFamily`: **the transport of the unit group of a
  completion by an automorphism fixing the place is the action of the decomposition group.**

## Tags

class field theory, idele, infinite place, completion, Galois action, family of rings
-/

namespace InverseGalois.CFT

open MulAction NumberField NumberField.InfinitePlace

section InfiniteFamily

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A shortcut instance for the commutative ring structure on the completion at an infinite
place. -/
noncomputable instance instCommRingInfiniteCompletion (w : InfinitePlace K) :
    CommRing w.Completion := inferInstance

/-- **The section of the family of completions at the infinite places determined by an element of
the field**: at each place, the image of the element in the completion there. -/
def infiniteCoe (y : K) (w : InfinitePlace K) : w.Completion :=
  (((WithAbs.equiv w.1).symm y : WithAbs w.1) : w.Completion)

theorem ringCast_infiniteCoe {w w' : InfinitePlace K} (h : w = w') (y : K) :
    ringCast (fun u : InfinitePlace K => u.Completion) h (infiniteCoe y w) = infiniteCoe y w' :=
  ringCast_apply_section _ h (infiniteCoe y)

/-- **The transport carries the section determined by an element of the field to the section
determined by its image.** -/
@[simp]
theorem infiniteCompletionGalEquiv_infiniteCoe (w : InfinitePlace K) (σ : Gal(K/k)) (y : K) :
    infiniteCompletionGalEquiv w σ (infiniteCoe y w) = infiniteCoe (σ y) (σ • w) := by
  rw [infiniteCoe, infiniteCompletionGalEquiv_coe]
  rfl

/-- **The Galois group acts on the family of completions of a number field at its infinite
places.** -/
noncomputable def infiniteRingFamily :
    RingFamilyAction (fun w : InfinitePlace K => w.Completion) Gal(K/k) where
  map σ w := infiniteCompletionGalEquiv w σ
  map_one w z := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (continuous_infiniteCompletionGalEquiv w 1)
        (continuous_ringCast _ (one_smul Gal(K/k) w).symm)) fun x => ?_
    show infiniteCompletionGalEquiv w 1 (infiniteCoe (WithAbs.equiv w.1 x) w)
      = ringCast _ _ (infiniteCoe (WithAbs.equiv w.1 x) w)
    rw [infiniteCompletionGalEquiv_infiniteCoe, ringCast_infiniteCoe]
    rfl
  map_mul σ τ w z := by
    refine UniformSpace.Completion.induction_on z
      (isClosed_eq (continuous_infiniteCompletionGalEquiv w (σ * τ))
        (((continuous_ringCast _ (mul_smul σ τ w).symm).comp
          (continuous_infiniteCompletionGalEquiv (τ • w) σ)).comp
          (continuous_infiniteCompletionGalEquiv w τ))) fun x => ?_
    show infiniteCompletionGalEquiv w (σ * τ) (infiniteCoe (WithAbs.equiv w.1 x) w)
      = ringCast _ _ (infiniteCompletionGalEquiv (τ • w) σ
          (infiniteCompletionGalEquiv w τ (infiniteCoe (WithAbs.equiv w.1 x) w)))
    rw [infiniteCompletionGalEquiv_infiniteCoe, infiniteCompletionGalEquiv_infiniteCoe,
      infiniteCompletionGalEquiv_infiniteCoe, ringCast_infiniteCoe]
    rfl

@[simp]
theorem infiniteRingFamily_map (σ : Gal(K/k)) (w : InfinitePlace K) :
    (infiniteRingFamily (k := k) (K := K)).map σ w = infiniteCompletionGalEquiv w σ := rfl

/-! ### The transport by an automorphism fixing the place -/

/-- **A Galois automorphism fixing an infinite place transports the completion there by the action
of the decomposition group.** -/
theorem ringCast_infiniteCompletionGalEquiv (w : InfinitePlace K) (σ : Gal(K/k))
    (hσ : σ • w = w) (z : w.Completion) :
    ringCast (fun u : InfinitePlace K => u.Completion) hσ (infiniteCompletionGalEquiv w σ z)
      = infiniteCompletionAut w σ hσ z := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ((continuous_ringCast _ hσ).comp (continuous_infiniteCompletionGalEquiv w σ))
      (continuous_infiniteCompletionAut w σ hσ)) fun x => ?_
  show ringCast _ hσ (infiniteCompletionGalEquiv w σ (infiniteCoe (WithAbs.equiv w.1 x) w))
    = infiniteCompletionAut w σ hσ (infiniteCoe (WithAbs.equiv w.1 x) w)
  rw [infiniteCompletionGalEquiv_infiniteCoe, ringCast_infiniteCoe]
  simp only [infiniteCoe]
  rw [infiniteCompletionAut_coe]
  rfl

/-- **The transport of the unit group of a completion at an infinite place by a Galois automorphism
fixing the place is the action of the decomposition group.** -/
theorem transport_infiniteUnitsFamily (w : InfinitePlace K) (σ : Gal(K/k)) (hσ : σ • w = w)
    (a : Additive w.Completionˣ) :
    (infiniteRingFamily (k := k) (K := K)).unitsFamily.transport hσ a
      = smulUnitsAut (G := ↥(stabilizer Gal(K/k) w)) (R := w.Completion)
          ⟨σ, mem_stabilizer_iff.mpr hσ⟩ a := by
  refine Additive.toMul.injective (Units.ext ?_)
  rw [FamilyAction.transport_apply, famCast_units, coe_smulUnitsAut_apply,
    stabilizer_smul_infiniteCompletion_def]
  exact ringCast_infiniteCompletionGalEquiv w σ hσ _

end InfiniteFamily

end InverseGalois.CFT
