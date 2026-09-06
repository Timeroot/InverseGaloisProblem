/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Tate.FamilyTensorFull
import InverseGalois.CFT.Tate.FamilyTrunc

/-!
# Finite support and the coordinates of a tensored section

Coefficients of finite rank over the prime field turn an element of the tensor product of the
sections of a family with those coefficients into a finite list of sections, its coordinates along a
basis of the coefficients.  The comparison with the sections of the tensored family is then read
coordinatewise, and so is the support: the value of the comparison at an index is assembled from the
values of the coordinates there, so it vanishes wherever all of them do.

The converse also holds, and is the useful direction.  An element whose comparison has finite
support may be replaced by the truncation of its coordinates on that support without changing it:
off the support the coordinates are divisible by the prime, and moving the prime onto the basis
vectors of the coefficients, which it kills, shows that the discarded part contributes nothing.  So
an element of the tensor product whose comparison has finite support is assembled from coordinates
of finite support.

## Main results

* `InverseGalois.CFT.finsuppSections_sectionsTensorMap_coordInv`: **coordinates of finite support
  assemble to an element whose comparison has finite support.**
* `InverseGalois.CFT.exists_coordInv_finsupp`: **an element whose comparison has finite support is
  assembled from coordinates of finite support.**
* `InverseGalois.CFT.exists_rho_invariant_sub_finsuppTensor`: **an element of the tensor product of
  the sections with the coefficients which the group moves in finitely many places only differs, in
  finitely many places only, from an invariant one.**

## Tags

tensor product, sections, finite support, restricted product, coordinates, prime field
-/

namespace InverseGalois.CFT

open CategoryTheory MulAction Tate

open scoped TensorProduct

noncomputable section

variable {G X : Type} [Group G] [MulAction G X] {M : X → Type} [∀ x, AddCommGroup (M x)]
  (F : FamilyAction M G) (W : Rep ℤ G) {p d : ℕ} [Fact p.Prime]
  (e : ↥W.V ≃+ (Fin d → ZMod p))

/-! ### Reading the comparison coordinatewise -/

/-- The comparison of the sections with the tensored family, evaluated at an index, assembles the
values of the coordinates at that index. -/
theorem sectionsTensorMap_coordInv (u : Fin d → ↥(orbitSectionsRep F).V) (x : X) :
    sectionsTensorMap F W (coordInv (↥(orbitSectionsRep F).V) e u) x
      = coordInv (M x) e (fun j => u j x) := by
  rw [sectionsTensorMap_apply]
  exact Tate.coordInv_map e (sectionsProj F x) u

include e in
/-- **Coordinates of finite support assemble to an element whose comparison has finite support**:
at an index where every coordinate vanishes, the value of the comparison is assembled from zeros. -/
theorem finsuppSections_sectionsTensorMap_coordInv (u : Fin d → ↥(orbitSectionsRep F).V)
    (hu : ∀ j, u j ∈ finsuppSections M) :
    sectionsTensorMap F W (coordInv (↥(orbitSectionsRep F).V) e u)
      ∈ finsuppSections fun x => M x ⊗[ℤ] ↥W.V := by
  rw [mem_finsuppSections]
  refine Set.Finite.subset (Set.finite_iUnion fun j : Fin d => mem_finsuppSections.1 (hu j))
    fun x hx => ?_
  by_contra hc
  refine hx ?_
  rw [sectionsTensorMap_coordInv]
  have hzero : (fun j => u j x) = (0 : Fin d → M x) :=
    funext fun j => by
      by_contra hj
      exact hc (Set.mem_iUnion.2 ⟨j, hj⟩)
  rw [hzero, map_zero]

/-! ### Discarding the coordinates off the support -/

include e in
/-- Coordinates all divisible by the prime assemble to zero: the prime moves onto the basis vectors
of the coefficients, which it kills. -/
theorem coordInv_eq_zero_of_nsmul {N : Type*} [AddCommGroup N] [Module ℤ N] (v : Fin d → N)
    (hv : ∀ j, ∃ z : N, v j = p • z) : coordInv N e v = 0 := by
  rw [coordInv_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨z, hz⟩ := hv j
  rw [hz, nsmul_tmul, nsmul_eq_zero_of_equivPi e, TensorProduct.tmul_zero]

include e in
/-- Truncating the coordinates of an element on a set outside which the comparison vanishes does not
change the element: off that set the coordinates are divisible by the prime, and the prime moves
onto the basis vectors of the coefficients, which it kills. -/
theorem coordInv_truncOutside_eq (g : Fin d → ↥(orbitSectionsRep F).V) (T : Set X)
    (hT : ∀ x ∈ T, sectionsTensorMap F W (coordInv (↥(orbitSectionsRep F).V) e g) x = 0) :
    coordInv (↥(orbitSectionsRep F).V) e (fun j => truncOutside T (g j))
      = coordInv (↥(orbitSectionsRep F).V) e g := by
  classical
  have hx : ∀ (x : X) (j : Fin d), ∃ m : M x, x ∈ T → p • m = g j x := by
    intro x j
    by_cases hxT : x ∈ T
    · obtain ⟨m, hm⟩ := Tate.exists_nsmul_of_coordInv_eq_zero e (fun i => g i x)
        (by rw [← sectionsTensorMap_coordInv]; exact hT x hxT) j
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hxT⟩
  choose c hc using hx
  refine sub_eq_zero.1 ?_
  rw [← map_sub]
  refine coordInv_eq_zero_of_nsmul W e _ fun j => ⟨fun x => if x ∈ T then -c x j else 0, ?_⟩
  funext x
  show truncOutside T (g j) x - g j x = p • (if x ∈ T then -c x j else 0)
  by_cases hxT : x ∈ T
  · rw [truncOutside_of_mem hxT, if_pos hxT, zero_sub, smul_neg, hc x j hxT]
  · rw [truncOutside_of_notMem hxT, if_neg hxT, sub_self, smul_zero]

include e in
/-- **An element of the tensor product of the sections with the coefficients whose comparison has
finite support is assembled from coordinates of finite support.**  Its coordinates are truncated on
the support of the comparison, which is finite, and the truncation changes nothing. -/
theorem exists_coordInv_finsupp (t : ↥(tensorObj (orbitSectionsRep F) W).V)
    (ht : sectionsTensorMap F W t ∈ finsuppSections fun x => M x ⊗[ℤ] ↥W.V) :
    ∃ u : Fin d → ↥(orbitSectionsRep F).V, (∀ j, u j ∈ finsuppSections M) ∧
      coordInv (↥(orbitSectionsRep F).V) e u = t := by
  classical
  obtain ⟨g, rfl⟩ := Tate.surjective_coordInv (M := ↥(orbitSectionsRep F).V) e t
  refine ⟨fun j => truncOutside
      {x : X | sectionsTensorMap F W (coordInv (↥(orbitSectionsRep F).V) e g) x = 0} (g j),
    fun j => ?_, coordInv_truncOutside_eq F W e g _ fun _ hx => hx⟩
  rw [mem_finsuppSections]
  refine (mem_finsuppSections.1 ht).subset fun x hx => ?_
  rcases eq_or_ne (sectionsTensorMap F W (coordInv (↥(orbitSectionsRep F).V) e g) x) 0 with h0 | h0
  · have hmem : x ∈ {y : X | sectionsTensorMap F W
        (coordInv (↥(orbitSectionsRep F).V) e g) y = 0} := h0
    exact absurd (truncOutside_of_mem hmem (g j)) hx
  · exact h0

/-! ### Correcting a tensored section into an invariant one -/

/-- The comparison with the sections of the tensored family is equivariant, read on an element. -/
theorem sectionsTensorMap_rho (g : G) (t : ↥(tensorObj (orbitSectionsRep F) W).V) :
    sectionsTensorMap F W ((tensorObj (orbitSectionsRep F) W).ρ g t)
      = (F.tensorRight W).familyAut g (sectionsTensorMap F W t) :=
  LinearMap.congr_fun (sectionsTensorMap_equivariant F W g) t

include e in
/-- **An element of the tensor product of the sections with the coefficients which the group moves
in finitely many places only differs, in finitely many places only, from an invariant one.**  Its
comparison is a section which the group moves in finitely many places only, so clearing that section
on the finite invariant saturation of those places leaves an invariant section, and the comparison
is bijective. -/
theorem exists_rho_invariant_sub_finsuppTensor [Finite G]
    (t : ↥(tensorObj (orbitSectionsRep F) W).V)
    (ht : ∀ g : G, sectionsTensorMap F W ((tensorObj (orbitSectionsRep F) W).ρ g t - t)
      ∈ finsuppSections fun x => M x ⊗[ℤ] ↥W.V) :
    ∃ t' : ↥(tensorObj (orbitSectionsRep F) W).V,
      (∀ g : G, (tensorObj (orbitSectionsRep F) W).ρ g t' = t') ∧
        sectionsTensorMap F W (t - t') ∈ finsuppSections fun x => M x ⊗[ℤ] ↥W.V := by
  obtain ⟨f', hf'inv, hf'sub⟩ :=
    (F.tensorRight W).exists_familyAut_invariant_sub_finsupp (sectionsTensorMap F W t) fun g => by
      have hg := ht g
      rw [_root_.map_sub, sectionsTensorMap_rho] at hg
      exact hg
  obtain ⟨t', ht'⟩ := (bijective_sectionsTensorMap_of_equivPi F W e).2 f'
  refine ⟨t', fun g => ?_, ?_⟩
  · refine (bijective_sectionsTensorMap_of_equivPi F W e).1 ?_
    rw [sectionsTensorMap_rho, ht', hf'inv g]
  · rw [_root_.map_sub, ht']
    exact hf'sub

end

end InverseGalois.CFT
