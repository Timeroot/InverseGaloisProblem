/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Exact
import InverseGalois.CFT.TateCohomology.Induced

/-!
# Shifting the degree of the middle Tate groups

A representation sits inside the functions on the group in two ways.  It embeds by recording all
the translates of a vector, and the functions on the group map onto it by summing the values after
undoing the translation.  Both middle Tate groups of the functions on the group vanish, so the
six term exact sequence of either short exact sequence degenerates: the connecting map becomes an
isomorphism.

The cokernel of the embedding is the *shift* of the representation, and the kernel of the summation
is its *coshift*.  The two isomorphisms say that the group in degree zero of a representation is
the group in degree minus one of its shift, and the group in degree minus one of a representation
is the group in degree zero of its coshift.  Iterating them is the standard device that carries a
statement about the complete cohomology from one degree to the next.

## Main definitions

* `InverseGalois.CFT.Tate.augMap`: the map from the functions on the group onto the representation
  that sums the values after undoing the translation.
* `InverseGalois.CFT.Tate.shiftRep`: the cokernel of the embedding into the functions on the group.
* `InverseGalois.CFT.Tate.coshiftRep`: the kernel of the summation map.

## Main results

* `InverseGalois.CFT.Tate.deltaShiftEquiv`: **the group in degree minus one of the shift is the
  group in degree zero of the representation.**
* `InverseGalois.CFT.Tate.deltaCoshiftEquiv`: **the group in degree minus one of a representation
  is the group in degree zero of its coshift.**

## Tags

Tate cohomology, dimension shifting, induced representation, connecting homomorphism
-/

namespace InverseGalois.CFT.Tate

open Representation

noncomputable section

variable {k G V : Type*} [CommRing k] [Group G] [Finite G] [AddCommGroup V] [Module k V]

/-! ### The summation map -/

section Aug

variable (ρ : Representation k G V)

/-- **The map from the functions on the group onto the representation** that sums the values after
undoing the translation. -/
def augMap : (G → V) →ₗ[k] V := ∑ᶠ x : G, (ρ x⁻¹ : V →ₗ[k] V) ∘ₗ LinearMap.proj x

omit [Finite G] in
theorem augMap_eq_sum [Fintype G] :
    augMap ρ = ∑ x : G, (ρ x⁻¹ : V →ₗ[k] V) ∘ₗ LinearMap.proj x :=
  finsum_eq_sum_of_fintype _

omit [Finite G] in
theorem augMap_apply [Fintype G] (f : G → V) : augMap ρ f = ∑ x : G, ρ x⁻¹ (f x) := by
  simp [augMap_eq_sum, LinearMap.sum_apply]

/-- **The summation map is equivariant.** -/
theorem augMap_comp_inducedRep (g : G) :
    augMap ρ ∘ₗ inducedRep k G V g = ρ g ∘ₗ augMap ρ := by
  letI := Fintype.ofFinite G
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, augMap_apply, augMap_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
  rw [inducedRep_apply, Equiv.coe_mulRight, ← Module.End.mul_apply, ← map_mul, mul_inv_rev,
    mul_inv_cancel_left]

theorem augMap_surjective : Function.Surjective (augMap ρ) := by
  classical
  letI := Fintype.ofFinite G
  intro v
  refine ⟨Pi.single 1 v, ?_⟩
  rw [augMap_apply, Finset.sum_eq_single (1 : G)]
  · rw [Pi.single_eq_same, inv_one, map_one]
    rfl
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Aug

/-! ### The shift and the coshift -/

section Shift

variable (ρ : Representation k G V)

omit [Finite G] in
theorem range_coindEmb_le_comap (g : G) :
    LinearMap.range (coindEmb ρ) ≤ (LinearMap.range (coindEmb ρ)).comap (inducedRep k G V g) := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (coindEmb_equivariant ρ g) v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  exact ⟨ρ g v, h⟩

/-- **The shift of a representation**: the cokernel of the embedding into the functions on the
group. -/
def shiftRep : Representation k G ((G → V) ⧸ LinearMap.range (coindEmb ρ)) :=
  Representation.quotient (inducedRep k G V) _ (range_coindEmb_le_comap ρ)

omit [Finite G] in
theorem mkQ_comp_inducedRep (g : G) :
    (LinearMap.range (coindEmb ρ)).mkQ ∘ₗ inducedRep k G V g
      = shiftRep ρ g ∘ₗ (LinearMap.range (coindEmb ρ)).mkQ :=
  LinearMap.ext fun _ => rfl

theorem ker_augMap_le_comap (g : G) :
    LinearMap.ker (augMap ρ) ≤ (LinearMap.ker (augMap ρ)).comap (inducedRep k G V g) := by
  intro f hf
  have h := LinearMap.congr_fun (augMap_comp_inducedRep ρ g) f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hf, map_zero] at h
  exact LinearMap.mem_ker.mpr h

/-- **The coshift of a representation**: the kernel of the summation map. -/
def coshiftRep : Representation k G ↥(LinearMap.ker (augMap ρ)) :=
  Representation.subrepresentation (inducedRep k G V) _ (ker_augMap_le_comap ρ)

theorem subtype_comp_coshiftRep (g : G) :
    (LinearMap.ker (augMap ρ)).subtype ∘ₗ coshiftRep ρ g
      = inducedRep k G V g ∘ₗ (LinearMap.ker (augMap ρ)).subtype :=
  LinearMap.ext fun _ => rfl

end Shift

/-! ### The two isomorphisms -/

section Degenerate

variable (ρ : Representation k G V)

/-- **The group in degree minus one of the shift is the group in degree zero of the
representation.** -/
def deltaShiftEquiv : Hm1 (shiftRep ρ) ≃ₗ[k] H0 ρ := by
  refine LinearEquiv.ofBijective
    (delta (coindEmb ρ) (coindEmb_equivariant ρ) (LinearMap.range (coindEmb ρ)).mkQ
      (mkQ_comp_inducedRep ρ) (coindEmb_injective ρ) (Submodule.mkQ_surjective _)
      (Submodule.ker_mkQ _).symm) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨y, hy⟩ := (exact_Hm1_delta (coindEmb ρ) (coindEmb_equivariant ρ)
      (LinearMap.range (coindEmb ρ)).mkQ (mkQ_comp_inducedRep ρ) (coindEmb_injective ρ)
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm z).mp hz
    rw [← hy, Hm1_inducedRep_eq_zero y, map_zero]
  · intro w
    refine (exact_delta_H0 (coindEmb ρ) (coindEmb_equivariant ρ)
      (LinearMap.range (coindEmb ρ)).mkQ (mkQ_comp_inducedRep ρ) (coindEmb_injective ρ)
      (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm w).mp ?_
    exact H0_inducedRep_eq_zero _

/-- **The group in degree minus one of a representation is the group in degree zero of its
coshift.** -/
def deltaCoshiftEquiv : Hm1 ρ ≃ₗ[k] H0 (coshiftRep ρ) := by
  refine LinearEquiv.ofBijective
    (delta (LinearMap.ker (augMap ρ)).subtype (subtype_comp_coshiftRep ρ) (augMap ρ)
      (augMap_comp_inducedRep ρ) (Submodule.injective_subtype _) (augMap_surjective ρ)
      (Submodule.range_subtype _)) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    obtain ⟨y, hy⟩ := (exact_Hm1_delta (LinearMap.ker (augMap ρ)).subtype
      (subtype_comp_coshiftRep ρ) (augMap ρ) (augMap_comp_inducedRep ρ)
      (Submodule.injective_subtype _) (augMap_surjective ρ) (Submodule.range_subtype _) z).mp hz
    rw [← hy, Hm1_inducedRep_eq_zero y, map_zero]
  · intro w
    refine (exact_delta_H0 (LinearMap.ker (augMap ρ)).subtype (subtype_comp_coshiftRep ρ)
      (augMap ρ) (augMap_comp_inducedRep ρ) (Submodule.injective_subtype _)
      (augMap_surjective ρ) (Submodule.range_subtype _) w).mp ?_
    exact H0_inducedRep_eq_zero _

end Degenerate

end

end InverseGalois.CFT.Tate
