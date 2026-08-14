/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureLoop

/-!
# Filling in a puncture kills its loop

A loop that winds once around a point which the region still contains bounds a disc, and a disc is
contractible: such a loop is trivial.  Only the points that are genuinely missing from the region
carry a non-trivial loop, so the loops constructed around a point of the region itself contribute
nothing to the fundamental group.

## Main results

* `Rigidity.RET.subsingleton_fundamentalGroup_ball` — a disc has trivial fundamental group.
* `Rigidity.RET.eq_one_of_isPunctureLoop_of_mem` — a loop winding around a point that the region
  still contains is trivial.
* `Rigidity.RET.IsPunctureLoop.mono` — winding around a point survives enlarging the region.
* `Rigidity.RET.IsPunctureLoop.transport` — winding around a point survives moving the basepoint
  along a path.
-/

open CategoryTheory Topology

noncomputable section

namespace Rigidity.RET

/-! ### Functoriality of the induced map on fundamental groups -/

/-- The map on fundamental groups induced by a composite is the composite of the induced maps. -/
theorem fundamentalGroup_map_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (F : C(Y, Z)) (G : C(X, Y)) (x : X) (g : FundamentalGroup X x) :
    FundamentalGroup.map (F.comp G) x g
      = FundamentalGroup.map F (G x) (FundamentalGroup.map G x g) := by
  obtain ⟨p, rfl⟩ :=
    Path.Homotopic.Quotient.mk_surjective (show Path.Homotopic.Quotient x x from g)
  rfl

/-- Transport of a loop along a path commutes with a continuous map. -/
theorem map_fundamentalGroupMulEquivOfPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x₀ x₁ : X} (δ : Path x₀ x₁) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.map f x₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath δ γ)
      = FundamentalGroup.fundamentalGroupMulEquivOfPath (δ.map f.continuous)
        (FundamentalGroup.map f x₀ γ) := by
  set F := FundamentalGroupoid.map f with hF
  set α : (FundamentalGroupoid.mk x₀ : FundamentalGroupoid X) ≅ FundamentalGroupoid.mk x₁ :=
    (Groupoid.isoEquivHom _ _).symm (⟦δ⟧ : Path.Homotopic.Quotient x₀ x₁) with hα
  set β : (FundamentalGroupoid.mk (f x₀) : FundamentalGroupoid Y) ≅
      FundamentalGroupoid.mk (f x₁) :=
    (Groupoid.isoEquivHom _ _).symm
      (⟦δ.map f.continuous⟧ : Path.Homotopic.Quotient (f x₀) (f x₁)) with hβ
  have hiso : F.mapIso α = β := Iso.ext rfl
  show F.map (α.conj γ) = β.conj (F.map γ)
  rw [F.map_conj α γ, hiso]
  rfl

/-- Transporting a loop along a concatenation of paths transports it along each path in turn. -/
theorem fundamentalGroupMulEquivOfPath_trans {X : Type*} [TopologicalSpace X] {x₀ x₁ x₂ : X}
    (δ : Path x₀ x₁) (ε : Path x₁ x₂) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (δ.trans ε) γ
      = FundamentalGroup.fundamentalGroupMulEquivOfPath ε
        (FundamentalGroup.fundamentalGroupMulEquivOfPath δ γ) := by
  have hiso :
      ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₂)).symm
          (⟦δ.trans ε⟧ : Path.Homotopic.Quotient x₀ x₂))
        = ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
            (⟦δ⟧ : Path.Homotopic.Quotient x₀ x₁)) ≪≫
          ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₁) (FundamentalGroupoid.mk x₂)).symm
            (⟦ε⟧ : Path.Homotopic.Quotient x₁ x₂)) := Iso.ext rfl
  show ((Groupoid.isoEquivHom _ _).symm (⟦δ.trans ε⟧ : Path.Homotopic.Quotient x₀ x₂)).conj γ = _
  rw [hiso, Iso.trans_conj]
  rfl

/-- Transporting a loop back along a path undoes transporting it along the path. -/
theorem fundamentalGroupMulEquivOfPath_symm {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (δ : Path x₀ x₁) (γ : FundamentalGroup X x₁) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath δ).symm γ
      = FundamentalGroup.fundamentalGroupMulEquivOfPath δ.symm γ := by
  have hiso :
      ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₁) (FundamentalGroupoid.mk x₀)).symm
          (⟦δ.symm⟧ : Path.Homotopic.Quotient x₁ x₀))
        = ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x₀) (FundamentalGroupoid.mk x₁)).symm
            (⟦δ⟧ : Path.Homotopic.Quotient x₀ x₁)).symm := Iso.ext rfl
  show ((Groupoid.isoEquivHom _ _).symm (⟦δ⟧ : Path.Homotopic.Quotient x₀ x₁)).conj.symm γ
    = ((Groupoid.isoEquivHom _ _).symm (⟦δ.symm⟧ : Path.Homotopic.Quotient x₁ x₀)).conj γ
  rw [hiso]
  exact (MulEquiv.symm_apply_eq _).2
    (Iso.self_symm_conj ((Groupoid.isoEquivHom _ _).symm
      (⟦δ⟧ : Path.Homotopic.Quotient x₀ x₁)) γ).symm

/-! ### Two inclusions -/

/-- A disc contained in a region of the plane sits inside it. -/
def ballIncl {X : Set ℂ} {s : ℂ} {ρ : ℝ} (h : Metric.ball s ρ ⊆ X) :
    C(↥(Metric.ball s ρ), ↥X) :=
  ⟨fun z => ⟨z.1, h z.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- A punctured disc sits inside the disc it came from. -/
def discToBall (s : ℂ) (ρ : ℝ) : C(↥(puncturedDisc s ρ), ↥(Metric.ball s ρ)) :=
  ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

theorem discIncl_eq_comp {X : Set ℂ} {s : ℂ} {ρ : ℝ} (h : Metric.ball s ρ ⊆ X)
    (h' : puncturedDisc s ρ ⊆ X) :
    discIncl h' = (ballIncl h).comp (discToBall s ρ) := rfl

/-- A punctured disc about a point of the region extends to a whole disc inside the region. -/
theorem ball_subset_of_mem {X : Set ℂ} {s : ℂ} {ρ : ℝ} (hs : s ∈ X)
    (h : puncturedDisc s ρ ⊆ X) : Metric.ball s ρ ⊆ X := by
  intro z hz
  rcases eq_or_ne z s with rfl | hzs
  · exact hs
  · exact h ⟨hz, hzs⟩

/-! ### A disc is simply connected -/

/-- **A disc has trivial fundamental group.**  A disc is convex, hence contractible, hence simply
connected. -/
theorem subsingleton_fundamentalGroup_ball (s : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (x : ↥(Metric.ball s ρ)) : Subsingleton (FundamentalGroup ↥(Metric.ball s ρ) x) := by
  haveI := Metric.contractibleSpace_ball (x := s) hρ
  exact inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x))

/-! ### Loops around a point of the region -/

/-- **A loop around a point that was never removed is trivial.**  Such a loop lives in a disc about
the point, and a disc is simply connected. -/
theorem eq_one_of_isPunctureLoop_of_mem {X : Set ℂ} {s : ℂ} (hs : s ∈ X) {z₀ : ℂ}
    (hz₀ : z₀ ∈ X) {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop X s hz₀ γ) : γ = 1 := by
  obtain ⟨ρ, h, b, g, δ, hρ, -, rfl⟩ := hγ
  have hball : Metric.ball s ρ ⊆ X := ball_subset_of_mem hs h
  haveI : Subsingleton (FundamentalGroup ↥(Metric.ball s ρ) (discToBall s ρ b)) :=
    subsingleton_fundamentalGroup_ball s hρ _
  have hmap : FundamentalGroup.map (discIncl h) b g
      = FundamentalGroup.map (ballIncl hball) (discToBall s ρ b)
        (FundamentalGroup.map (discToBall s ρ) b g) :=
    fundamentalGroup_map_comp (ballIncl hball) (discToBall s ρ) b g
  rw [hmap, Subsingleton.elim (FundamentalGroup.map (discToBall s ρ) b g) 1, map_one, map_one]

/-! ### Enlarging the region -/

/-- A region of the plane sits inside any larger region. -/
def subsetIncl {X X' : Set ℂ} (hsub : X ⊆ X') : C(↥X, ↥X') :=
  ⟨fun z => ⟨z.1, hsub z.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- **Winding around a point survives enlarging the region.**  A loop of `X` that winds once around
`s` still winds once around `s` when read in a larger region, in particular when some of the
punctures are filled back in. -/
theorem IsPunctureLoop.mono {X X' : Set ℂ} (hsub : X ⊆ X') {s z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (hγ : IsPunctureLoop X s hz₀ γ) :
    IsPunctureLoop X' s (hsub hz₀) (FundamentalGroup.map (subsetIncl hsub) ⟨z₀, hz₀⟩ γ) := by
  obtain ⟨ρ, h, b, g, δ, hρ, hgen, rfl⟩ := hγ
  refine ⟨ρ, h.trans hsub, b, g, δ.map (subsetIncl hsub).continuous, hρ, hgen, ?_⟩
  rw [map_fundamentalGroupMulEquivOfPath, ← fundamentalGroup_map_comp]
  rfl

/-! ### Changing the basepoint -/

/-- **Winding around a point does not depend on the basepoint.**  Dragging a loop that winds once
around `s` along a path to a new basepoint leaves a loop that still winds once around `s`. -/
theorem IsPunctureLoop.transport {X : Set ℂ} {s z₀ z₁ : ℂ} {hz₀ : z₀ ∈ X} {hz₁ : z₁ ∈ X}
    (ε : Path (⟨z₀, hz₀⟩ : ↥X) ⟨z₁, hz₁⟩) {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop X s hz₀ γ) :
    IsPunctureLoop X s hz₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath ε γ) := by
  obtain ⟨ρ, h, b, g, δ, hρ, hgen, rfl⟩ := hγ
  exact ⟨ρ, h, b, g, δ.trans ε, hρ, hgen, (fundamentalGroupMulEquivOfPath_trans δ ε _).symm⟩

/-- **Winding around a point does not depend on the basepoint**, in the backwards direction. -/
theorem IsPunctureLoop.transport_symm {X : Set ℂ} {s z₀ z₁ : ℂ} {hz₀ : z₀ ∈ X} {hz₁ : z₁ ∈ X}
    (ε : Path (⟨z₀, hz₀⟩ : ↥X) ⟨z₁, hz₁⟩) {γ : FundamentalGroup ↥X ⟨z₁, hz₁⟩}
    (hγ : IsPunctureLoop X s hz₁ γ) :
    IsPunctureLoop X s hz₀ ((FundamentalGroup.fundamentalGroupMulEquivOfPath ε).symm γ) := by
  rw [fundamentalGroupMulEquivOfPath_symm]
  exact hγ.transport ε.symm

/-- **A loop around a point that is filled back in becomes trivial.** -/
theorem map_eq_one_of_isPunctureLoop {X X' : Set ℂ} (hsub : X ⊆ X') {s z₀ : ℂ} (hs : s ∈ X')
    {hz₀ : z₀ ∈ X} {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (hγ : IsPunctureLoop X s hz₀ γ) :
    FundamentalGroup.map (subsetIncl hsub) ⟨z₀, hz₀⟩ γ = 1 :=
  eq_one_of_isPunctureLoop_of_mem hs (hsub hz₀) (hγ.mono hsub)

end Rigidity.RET

end
