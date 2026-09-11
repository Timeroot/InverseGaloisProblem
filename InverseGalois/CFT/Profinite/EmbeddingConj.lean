/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.EmbeddingClass

/-!
# The class of an extension on a conjugate subgroup

Splitting an extension over a subgroup is a property of the conjugacy class of the subgroup and not
of the subgroup itself: a splitting over one member of the class is carried to a splitting over any
other by conjugating inside the extension, the projection being onto.

The reading this is for is local solvability over a number field.  A place of the base field has
not one decomposition subgroup of the absolute Galois group but a whole conjugacy class of them,
one for each prime of the big field above it, and there are infinitely many; a family of subgroups
chosen once and for all is necessarily finite, so it can name only one member of each class.  What
is arranged at the named member is therefore of no use at the others unless it is invariant under
conjugation, and splitting is.

## Main results

* `InverseGalois.CFT.resH2_extensionClass_map_conj_eq_one` — **an extension which splits over a
  subgroup splits over every conjugate of it.**

## Tags

group extension, obstruction, conjugate subgroup, decomposition group, local solvability
-/

namespace InverseGalois.CFT

open GroupExtension

section Conj

variable {N E G : Type*} [CommGroup N] [Group E] [Group G] [TopologicalSpace G]
  [DiscreteTopology G]
variable (S : GroupExtension N E G) [MulDistribMulAction G N]
variable (hactG : ∀ (g : G) (n : N), g • n = S.conjActHom g n)

include hactG in
/-- **An extension which splits over a subgroup splits over every conjugate of it.**

A splitting over the subgroup, conjugated inside the extension by any element above the conjugating
element, is a splitting over the conjugate: the projection carries the conjugation upstairs to the
conjugation downstairs, and it is onto, so an element above the conjugating element is available. -/
theorem resH2_extensionClass_map_conj_eq_one (σ : S.Section) (H : Subgroup G) (g : G)
    (h : resH2 H (extensionClass S hactG σ) = 1) :
    resH2 (H.map (MulAut.conj g).toMonoidHom) (extensionClass S hactG σ) = 1 := by
  obtain ⟨f, hf⟩ := (resH2_extensionClass_eq_one_iff S hactG σ H).1 h
  obtain ⟨w, hw⟩ := S.rightHom_surjective g
  have hmem : ∀ x : ↥(H.map (MulAut.conj g).toMonoidHom), g⁻¹ * (x : G) * g ∈ H := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 x.2
    have hcoe : (x : G) = g * y * g⁻¹ := hxy.symm
    have hval : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [hcoe, hval]
    exact hy
  refine (resH2_extensionClass_eq_one_iff S hactG σ _).2
    ⟨(MulAut.conj w).toMonoidHom.comp (f.comp
      (((MulAut.conj g).symm.toMonoidHom.comp
        (H.map (MulAut.conj g).toMonoidHom).subtype).codRestrict H hmem)), fun x => ?_⟩
  show S.rightHom (w * f ⟨g⁻¹ * (x : G) * g, hmem x⟩ * w⁻¹) = (x : G)
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hf, hw]
  show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G)
  group

end Conj

end InverseGalois.CFT
