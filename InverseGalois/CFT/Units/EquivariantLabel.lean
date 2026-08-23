/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Labelling the points of a set by the points of another

A set acted on by a group is often given together with an injective equivariant map to another set
carrying an action of the same group: the places above a fixed place of a base field, say, labelled
by the places of the extension.  Such a labelling identifies the stabiliser of a point with the
stabiliser of its label, which is what lets a decomposition group be read off either from the
abstract orbit or from the concrete object it names.

## Main results

* `InverseGalois.CFT.stabilizer_eq_of_equivariant`: **an injective equivariant labelling
  identifies the stabilisers.**
* `InverseGalois.CFT.mem_stabilizer_of_smul_eq`: the stabiliser of a label contains every element
  fixing the point.
* `InverseGalois.CFT.smul_eq_of_mem_stabilizer`: every element fixing the label fixes the point.

## Tags

group action, stabiliser, equivariant map
-/

namespace InverseGalois.CFT

open MulAction

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y] {ι : X → Y}
  (hι : ∀ (g : G) (x : X), ι (g • x) = g • ι x) (hinj : Function.Injective ι) (x₀ : X)

include hι hinj

/-- **An injective equivariant labelling identifies the stabilisers.** -/
theorem stabilizer_eq_of_equivariant : stabilizer G (ι x₀) = stabilizer G x₀ := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← hι g x₀]
  exact ⟨fun h => hinj h, fun h => congrArg ι h⟩

/-- The stabiliser of a label contains every element fixing the point. -/
theorem mem_stabilizer_of_smul_eq (g : G) (hg : g • x₀ = x₀) : g ∈ stabilizer G (ι x₀) := by
  rw [stabilizer_eq_of_equivariant hι hinj x₀]
  exact hg

/-- Every element fixing the label fixes the point. -/
theorem smul_eq_of_mem_stabilizer (g : ↥(stabilizer G (ι x₀))) : (g : G) • x₀ = x₀ :=
  hinj (by rw [hι]; exact g.2)

end InverseGalois.CFT
