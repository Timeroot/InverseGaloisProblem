/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Connected
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy

/-!
# Transitive monodromy of an irreducible family

Local path-connectedness travels along a local homeomorphism: a chart carries a path-connected
neighbourhood downstairs back to one upstairs.  The root cover of a family is locally
homeomorphic to the parameter plane away from the degeneracy set, so it is locally path connected;
being connected as well, it is path connected.

Path-connectedness of the total space of a covering space is exactly what makes the monodromy
action on a fibre transitive: a path joining two points of the fibre projects to a loop whose lift
joins them.  So the monodromy group of an irreducible family is transitive on the fibre, and the
branch cycles, which generate it, act transitively too.

## Main results

* `Rigidity.RET.Analytic.locPathConnectedSpace_of_isLocalHomeomorph` — a space locally
  homeomorphic to a locally path-connected space is locally path connected.
* `Rigidity.RET.Analytic.pathConnectedSpace_punctured` — the root cover of an irreducible family
  is path connected over the complement of the degeneracy set.
* `Rigidity.RET.Analytic.monodromy_transitive` — the monodromy action on a fibre is transitive.
* `Rigidity.RET.Analytic.sphereMonodromy_transitive` — the same for the sphere presentation group,
  whose distinguished generators are the branch cycles.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### Local path-connectedness along a local homeomorphism -/

/-- **A basis criterion for local path-connectedness**: it is enough that every point of every
open set has a path-connected open neighbourhood inside that set. -/
theorem locPathConnectedSpace_of_basis {X : Type*} [TopologicalSpace X]
    (h : ∀ (x : X) (u : Set X), IsOpen u → x ∈ u →
      ∃ v : Set X, IsOpen v ∧ x ∈ v ∧ v ⊆ u ∧ IsPathConnected v) :
    LocPathConnectedSpace X := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x u hu hxu
  obtain ⟨v, hvopen, hxv, hvu, hvpc⟩ := h x u hu hxu
  exact Filter.mem_of_superset (hvopen.mem_nhds hxv) (hvpc.subset_pathComponentIn hxv hvu)

/-- **Local path-connectedness lifts along a local homeomorphism.**  A chart identifies a
neighbourhood of a point with an open set downstairs, where path-connected neighbourhoods are
available, and carries one of them back. -/
theorem locPathConnectedSpace_of_isLocalHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocPathConnectedSpace Y] {f : X → Y} (hf : IsLocalHomeomorph f) :
    LocPathConnectedSpace X := by
  refine locPathConnectedSpace_of_basis fun x u hu hxu => ?_
  obtain ⟨e, hxe, hfe⟩ := hf x
  -- the image of the open set `e.source ∩ u` is open downstairs
  have hVopen : IsOpen (e '' (e.source ∩ u)) := e.isOpen_image_source_inter hu
  have hxV : e x ∈ e '' (e.source ∩ u) := ⟨x, ⟨hxe, hxu⟩, rfl⟩
  obtain ⟨w, ⟨hwopen, hew, hwpc⟩, hwV⟩ :=
    (isOpen_isPathConnected_basis (e x)).mem_iff.mp (hVopen.mem_nhds hxV)
  have hwt : w ⊆ e.target := hwV.trans fun _ hy => by
    obtain ⟨y, hy', rfl⟩ := hy
    exact e.map_source hy'.1
  refine ⟨e.source ∩ e ⁻¹' w,
    e.continuousOn.isOpen_inter_preimage e.open_source hwopen, ⟨hxe, hew⟩, ?_, ?_⟩
  · -- the chart is injective on its source, so the preimage stays inside `u`
    rintro y ⟨hys, hyw⟩
    obtain ⟨y', hy', hy'e⟩ := hwV hyw
    rw [e.injOn hys hy'.1 hy'e.symm]
    exact hy'.2
  · -- and it is the homeomorphic image of the path-connected set `w`
    have himg : e.source ∩ e ⁻¹' w = e.symm '' w := by
      ext y
      constructor
      · rintro ⟨hys, hyw⟩
        exact ⟨e y, hyw, e.left_inv hys⟩
      · rintro ⟨t, htw, rfl⟩
        refine ⟨e.map_target (hwt htw), ?_⟩
        show e (e.symm t) ∈ w
        rw [e.right_inv (hwt htw)]
        exact htw
    rw [himg]
    exact hwpc.image' (e.continuousOn_symm.mono hwt)

/-! ### The root cover of an irreducible family is path connected -/

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ}

/-- **The root cover over the complement of the degeneracy set is locally path connected**, being
locally homeomorphic to an open subset of the parameter plane. -/
theorem locPathConnectedSpace_punctured (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    LocPathConnectedSpace ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) :=
  haveI : LocPathConnectedSpace ↥((S : Set ℂ)ᶜ) :=
    (S.finite_toSet.isClosed.isOpen_compl).locPathConnectedSpace
  locPathConnectedSpace_of_isLocalHomeomorph
    (isCoveringMap_puncturedProj hP hS).isLocalHomeomorph

/-- **The root cover of an irreducible family is path connected** over the complement of the
degeneracy set. -/
theorem pathConnectedSpace_punctured (hP : P.Monic) (hdeg : 0 < P.natDegree)
    (hirr : Irreducible P) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) :
    PathConnectedSpace ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) := by
  haveI := locPathConnectedSpace_punctured hP hS
  haveI : ConnectedSpace ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ)) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_puncturedVariety hP hdeg hirr S.finite_toSet hS)
  exact PathConnectedSpace.of_locPathConnectedSpace

/-! ### Transitivity -/

/-- **The monodromy action of an irreducible family on a fibre is transitive.** -/
theorem monodromy_transitive (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ e₁ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    ∃ γ : FundamentalGroup ↥((S : Set ℂ)ᶜ) ⟨z₀, hz₀⟩, monodromyHom hP hS hz₀ γ e₀ = e₁ := by
  haveI := pathConnectedSpace_punctured hP hdeg hirr hS
  obtain ⟨γ, hγ⟩ :=
    (isCoveringMap_puncturedProj hP hS).orbitMap_surjective ⟨z₀, hz₀⟩ e₀ e₁
  exact ⟨γ, hγ⟩

/-- **The branch cycles of an irreducible family act transitively on a fibre.**  The sphere
presentation group surjects onto the fundamental group of the punctured plane, so its monodromy
image is the full monodromy group; the branch cycles generate that image. -/
theorem sphereMonodromy_transitive (hP : P.Monic) (hdeg : 0 < P.natDegree) (hirr : Irreducible P)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {z₀ : ℂ} (hz₀ : z₀ ∉ (S : Set ℂ))
    (e₀ e₁ : puncturedProj P S ⁻¹' {(⟨z₀, hz₀⟩ : ↥((S : Set ℂ)ᶜ))}) :
    ∃ γ : SphereGroup (S.card + 1), sphereMonodromy hP hS hz₀ γ e₀ = e₁ := by
  obtain ⟨δ, hδ⟩ := monodromy_transitive hP hdeg hirr hS hz₀ e₀ e₁
  refine ⟨(pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some δ, ?_⟩
  have hcomp : sphereMonodromy hP hS hz₀ ((pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some δ)
      = monodromyHom hP hS hz₀ δ := by
    show monodromyHom hP hS hz₀ ((pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some.symm
      ((pi1_compl_mulEquiv_sphereGroup S z₀ hz₀).some δ)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [hcomp]
  exact hδ

end Rigidity.RET.Analytic

end
