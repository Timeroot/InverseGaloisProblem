/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Seifert–van Kampen: the groupoid pushout statement

For an open cover `X = U ∪ V` of a topological space, the fundamental groupoid of `X` is the
**pushout** of the fundamental groupoids of `U` and `V` along that of the intersection `W = U ∩ V`:

```
        π(W) ──→ π(U)
         │         │
         ↓         ↓
        π(V) ──→ π(X)
```

is a pushout square in the category `Grpd` of groupoids.  This is the Ronnie Brown "groupoid"
formulation of the Seifert–van Kampen theorem; it is basepoint-free and hence cleaner than the
classical fundamental-*group* statement, which it specialises to at any point of `W` (see
`VanKampen/Group.lean`).

This file fixes the interfaces: the four inclusion-induced functors and the commuting square
(proved here — it is pure functoriality).  The pushout universal property itself is assembled in
`VanKampen/Uniqueness.lean` (the generation/uniqueness half) and `VanKampen/Existence.lean` (the
descended-functor half), from the path-subdivision analysis of `VanKampen/Subdivision.lean`.

## Main declarations

* `Rigidity.RET.VanKampen.mapUW`, `mapVW`, `mapUX`, `mapVX` — the four inclusion functors as
  morphisms of `Grpd`.
* `Rigidity.RET.VanKampen.commSq` — the square commutes.
-/

universe u

open CategoryTheory FundamentalGroupoid

namespace Rigidity.RET.VanKampen

variable {X : Type u} [TopologicalSpace X] (U V : Set X)

/-- The fundamental groupoid of a subset, packaged as an object of `Grpd`. -/
@[reducible] noncomputable def grpd (s : Set X) : Grpd := Grpd.of (FundamentalGroupoid s)

/-- The fundamental groupoid of the ambient space, as an object of `Grpd`. -/
@[reducible] noncomputable def grpdX (Y : Type u) [TopologicalSpace Y] : Grpd :=
  Grpd.of (FundamentalGroupoid Y)

/-- The inclusion `U ∩ V ↪ U` as a bundled continuous map. -/
def inclUW : C((U ∩ V : Set X), U) := ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩

/-- The inclusion `U ∩ V ↪ V` as a bundled continuous map. -/
def inclVW : C((U ∩ V : Set X), V) := ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩

/-- The inclusion `U ↪ X` as a bundled continuous map. -/
def inclUX : C((U : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `V ↪ X` as a bundled continuous map. -/
def inclVX : C((V : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- `π(U ∩ V) ⥤ π(U)`, induced by the inclusion. -/
noncomputable def mapUW : grpd (U ∩ V) ⟶ grpd U := FundamentalGroupoid.map (inclUW U V)

/-- `π(U ∩ V) ⥤ π(V)`, induced by the inclusion. -/
noncomputable def mapVW : grpd (U ∩ V) ⟶ grpd V := FundamentalGroupoid.map (inclVW U V)

/-- `π(U) ⥤ π(X)`, induced by the inclusion. -/
noncomputable def mapUX : grpd U ⟶ grpdX X := FundamentalGroupoid.map (inclUX U)

/-- `π(V) ⥤ π(X)`, induced by the inclusion. -/
noncomputable def mapVX : grpd V ⟶ grpdX X := FundamentalGroupoid.map (inclVX V)

/-- The two composites `U ∩ V ↪ U ↪ X` and `U ∩ V ↪ V ↪ X` are the same continuous map (both are
the inclusion `U ∩ V ↪ X`). -/
theorem inclUX_comp_inclUW :
    (inclUX U).comp (inclUW U V) = (inclVX V).comp (inclVW U V) := by
  ext w
  rfl

/-- The Seifert–van Kampen square commutes: `π(W) → π(U) → π(X)` equals `π(W) → π(V) → π(X)`. -/
theorem commSq : CommSq (mapUW U V) (mapVW U V) (mapUX U) (mapVX V) := by
  refine ⟨?_⟩
  show FundamentalGroupoid.map (inclUW U V) ⋙ FundamentalGroupoid.map (inclUX U) =
    FundamentalGroupoid.map (inclVW U V) ⋙ FundamentalGroupoid.map (inclVX V)
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp, inclUX_comp_inclUW]

end Rigidity.RET.VanKampen
