/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.VanKampen.Statement
import Mathlib.Topology.Subpath

/-!
# Lifting subpaths into a cover element

The other half of the Seifert–van Kampen "generation" analysis: once a path has been chopped so
that a piece `γ.subpath t₀ t₁` lies entirely inside a cover element `U`, that piece **comes from**
the fundamental groupoid of `U`.  Concretely the subpath lifts to a genuine path in the subspace
`↥U`, and pushing that lift forward along the inclusion `U ↪ X` recovers the original subpath.  At
the level of homotopy classes this says the morphism `⟦γ.subpath t₀ t₁⟧` of `π(X)` is the image of a
morphism of `π(U)` under the inclusion-induced functor `mapUX`.

This is exactly what lets every morphism of `π(X)`, decomposed via `Generation.lean` into a
concatenation of such pieces, be written using only morphisms coming from `π(U)` and `π(V)` — the
input to both the uniqueness and the existence half of the universal property.

## Main declarations

* `Rigidity.RET.VanKampen.exists_lift_subpath_left` / `..._right` — a subpath with range in `U`
  (resp. `V`) is the pushforward of a path in `↥U` (resp. `↥V`).
* `Rigidity.RET.VanKampen.mk_subpath_eq_mapUX` / `..._mapVX` — the groupoid-level statement: the
  class of such a subpath is `mapUX` (resp. `mapVX`) applied to a class in `π(U)` (resp. `π(V)`).
-/

universe u

open CategoryTheory FundamentalGroupoid Set unitInterval

namespace Rigidity.RET.VanKampen

variable {X : Type u} [TopologicalSpace X]

/-- A subpath of `γ` whose range lies in `U` lifts to a path in the subspace `↥U`, and pushing that
lift forward along `U ↪ X` gives back the subpath. -/
theorem exists_lift_subpath_left (U : Set X) {a b : X} (γ : Path a b) (t₀ t₁ : I)
    (h : range (γ.subpath t₀ t₁) ⊆ U) :
    ∃ (m0 : γ t₀ ∈ U) (m1 : γ t₁ ∈ U)
      (δ : Path (⟨γ t₀, m0⟩ : U) (⟨γ t₁, m1⟩ : U)),
      δ.map continuous_subtype_val = γ.subpath t₀ t₁ := by
  have m0 : γ t₀ ∈ U := h ⟨0, (γ.subpath t₀ t₁).source⟩
  have m1 : γ t₁ ∈ U := h ⟨1, (γ.subpath t₀ t₁).target⟩
  refine ⟨m0, m1, ?_, ?_⟩
  · exact
      { toFun := fun s => ⟨γ.subpath t₀ t₁ s, h (mem_range_self s)⟩
        continuous_toFun := (map_continuous (γ.subpath t₀ t₁)).subtype_mk _
        source' := Subtype.ext (γ.subpath t₀ t₁).source
        target' := Subtype.ext (γ.subpath t₀ t₁).target }
  · ext s; rfl

/-- A subpath of `γ` whose range lies in `V` lifts to a path in the subspace `↥V`. -/
theorem exists_lift_subpath_right (V : Set X) {a b : X} (γ : Path a b) (t₀ t₁ : I)
    (h : range (γ.subpath t₀ t₁) ⊆ V) :
    ∃ (m0 : γ t₀ ∈ V) (m1 : γ t₁ ∈ V)
      (δ : Path (⟨γ t₀, m0⟩ : V) (⟨γ t₁, m1⟩ : V)),
      δ.map continuous_subtype_val = γ.subpath t₀ t₁ := by
  have m0 : γ t₀ ∈ V := h ⟨0, (γ.subpath t₀ t₁).source⟩
  have m1 : γ t₁ ∈ V := h ⟨1, (γ.subpath t₀ t₁).target⟩
  refine ⟨m0, m1, ?_, ?_⟩
  · exact
      { toFun := fun s => ⟨γ.subpath t₀ t₁ s, h (mem_range_self s)⟩
        continuous_toFun := (map_continuous (γ.subpath t₀ t₁)).subtype_mk _
        source' := Subtype.ext (γ.subpath t₀ t₁).source
        target' := Subtype.ext (γ.subpath t₀ t₁).target }
  · ext s; rfl

/-- **Bridge (groupoid form, `U`).**  The homotopy class of a subpath lying in `U` is the image
under the inclusion functor `mapUX` of a morphism of `π(U)`. -/
theorem mk_subpath_eq_mapUX (U : Set X) {a b : X} (γ : Path a b) (t₀ t₁ : I)
    (h : range (γ.subpath t₀ t₁) ⊆ U) :
    ∃ (m0 : γ t₀ ∈ U) (m1 : γ t₁ ∈ U)
      (δ : (⟨⟨γ t₀, m0⟩⟩ : FundamentalGroupoid U) ⟶ ⟨⟨γ t₁, m1⟩⟩),
      (FundamentalGroupoid.map (inclUX U)).map δ = (⟦γ.subpath t₀ t₁⟧ :
        Path.Homotopic.Quotient (γ t₀) (γ t₁)) := by
  obtain ⟨m0, m1, δ, hδ⟩ := exists_lift_subpath_left U γ t₀ t₁ h
  refine ⟨m0, m1, ⟦δ⟧, ?_⟩
  have hmap : (FundamentalGroupoid.map (inclUX U)).map ⟦δ⟧
      = ⟦δ.map continuous_subtype_val⟧ := rfl
  rw [hmap]
  exact congrArg (fun p => (⟦p⟧ : Path.Homotopic.Quotient (γ t₀) (γ t₁))) hδ

/-- **Bridge (groupoid form, `V`).**  The homotopy class of a subpath lying in `V` is the image
under the inclusion functor `mapVX` of a morphism of `π(V)`. -/
theorem mk_subpath_eq_mapVX (V : Set X) {a b : X} (γ : Path a b) (t₀ t₁ : I)
    (h : range (γ.subpath t₀ t₁) ⊆ V) :
    ∃ (m0 : γ t₀ ∈ V) (m1 : γ t₁ ∈ V)
      (δ : (⟨⟨γ t₀, m0⟩⟩ : FundamentalGroupoid V) ⟶ ⟨⟨γ t₁, m1⟩⟩),
      (FundamentalGroupoid.map (inclVX V)).map δ = (⟦γ.subpath t₀ t₁⟧ :
        Path.Homotopic.Quotient (γ t₀) (γ t₁)) := by
  obtain ⟨m0, m1, δ, hδ⟩ := exists_lift_subpath_right V γ t₀ t₁ h
  refine ⟨m0, m1, ⟦δ⟧, ?_⟩
  have hmap : (FundamentalGroupoid.map (inclVX V)).map ⟦δ⟧
      = ⟦δ.map continuous_subtype_val⟧ := rfl
  rw [hmap]
  exact congrArg (fun p => (⟦p⟧ : Path.Homotopic.Quotient (γ t₀) (γ t₁))) hδ

end Rigidity.RET.VanKampen
