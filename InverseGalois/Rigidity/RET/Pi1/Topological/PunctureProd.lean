/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# Ordered products of puncture loops

A spider relation says that a given loop is, in a prescribed order, the product of one loop around
each of the missing points.  This file introduces the predicate `IsPunctureProd X T hz₀ g` saying
that `g` is such a product for the finite set `T` of punctures, and the four combinators that make
it usable in a geometric induction:

* the empty product is trivial and a single puncture loop is a product over a singleton;
* products over disjoint sets of punctures multiply, in the order in which they are written;
* a product survives moving the basepoint along a path.

Because the number of factors is packaged as an anonymous `Fin r`-indexed family with injective
labels, gluing two products is `Fin.append` and nothing else.

## Main results

* `Rigidity.RET.IsPunctureProd` — the predicate.
* `Rigidity.RET.IsPunctureProd.mul` — products over disjoint sets of punctures multiply.
* `Rigidity.RET.IsPunctureProd.transport` — a product survives moving the basepoint.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-- A loop of a region of the plane is a **product of puncture loops around `T`** when it is the
ordered product of one loop winding around each point of `T`. -/
def IsPunctureProd (X : Set ℂ) (T : Set ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ X)
    (g : FundamentalGroup ↥X ⟨z₀, hz₀⟩) : Prop :=
  ∃ (r : ℕ) (pt : Fin r → ℂ) (γ : Fin r → FundamentalGroup ↥X ⟨z₀, hz₀⟩),
    Function.Injective pt ∧ Set.range pt = T ∧
      (∀ i, IsPunctureLoop X (pt i) hz₀ (γ i)) ∧ (List.ofFn γ).prod = g

/-- The trivial loop is the empty product of puncture loops. -/
theorem IsPunctureProd.one {X : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ X) :
    IsPunctureProd X ∅ hz₀ 1 :=
  ⟨0, Fin.elim0, Fin.elim0, Function.injective_of_subsingleton _, by simp, fun i => i.elim0,
    by simp⟩

/-- A loop winding once around a single point is a product of puncture loops over a singleton. -/
theorem IsPunctureProd.single {X : Set ℂ} {s z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (hg : IsPunctureLoop X s hz₀ g) :
    IsPunctureProd X {s} hz₀ g :=
  ⟨1, fun _ => s, fun _ => g, Function.injective_of_subsingleton _, by simp, fun _ => hg, by simp⟩

/-- Being a product of puncture loops transfers along an equality of loops. -/
theorem IsPunctureProd.congr {X T : Set ℂ} {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g g' : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (h : IsPunctureProd X T hz₀ g) (hg : g = g') :
    IsPunctureProd X T hz₀ g' := hg ▸ h

/-! ### Gluing two indexed families -/

/-- The range of a concatenation of two families is the union of the ranges. -/
theorem range_fin_append {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Set.range (Fin.append a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · exact Or.inl ⟨i, by rw [Fin.append_left]⟩
    · exact Or.inr ⟨i, by rw [Fin.append_right]⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left a b i⟩
    · exact ⟨Fin.natAdd m i, Fin.append_right a b i⟩

/-- A concatenation of two injective families with disjoint ranges is injective. -/
theorem injective_fin_append {α : Type*} {m n : ℕ} {a : Fin m → α} {b : Fin n → α}
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hdisj : Disjoint (Set.range a) (Set.range b)) : Function.Injective (Fin.append a b) := by
  have key : ∀ (i : Fin m) (j : Fin n), a i ≠ b j := by
    intro i j hij
    exact Set.disjoint_left.mp hdisj ⟨i, rfl⟩ ⟨j, hij ▸ rfl⟩
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => rw [Fin.append_left, Fin.append_left] at hij; rw [ha hij]
    | right j => rw [Fin.append_left, Fin.append_right] at hij; exact absurd hij (key i j)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left] at hij; exact absurd hij.symm (key j i)
    | right j => rw [Fin.append_right, Fin.append_right] at hij; rw [hb hij]

/-! ### The combinators -/

/-- **Products of puncture loops over disjoint sets of punctures multiply.** -/
theorem IsPunctureProd.mul {X T₁ T₂ : Set ℂ} {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g₁ g₂ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (h₁ : IsPunctureProd X T₁ hz₀ g₁)
    (h₂ : IsPunctureProd X T₂ hz₀ g₂) (hdisj : Disjoint T₁ T₂) :
    IsPunctureProd X (T₁ ∪ T₂) hz₀ (g₁ * g₂) := by
  obtain ⟨r₁, pt₁, γ₁, hinj₁, hrange₁, hloop₁, hprod₁⟩ := h₁
  obtain ⟨r₂, pt₂, γ₂, hinj₂, hrange₂, hloop₂, hprod₂⟩ := h₂
  refine ⟨r₁ + r₂, Fin.append pt₁ pt₂, Fin.append γ₁ γ₂,
    injective_fin_append hinj₁ hinj₂ (by rw [hrange₁, hrange₂]; exact hdisj),
    by rw [range_fin_append, hrange₁, hrange₂], fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i => rw [Fin.append_left, Fin.append_left]; exact hloop₁ i
    | right i => rw [Fin.append_right, Fin.append_right]; exact hloop₂ i
  · rw [List.ofFn_fin_append, List.prod_append, hprod₁, hprod₂]

/-- **A product of puncture loops survives moving the basepoint along a path.** -/
theorem IsPunctureProd.transport {X T : Set ℂ} {z₀ z₁ : ℂ} {hz₀ : z₀ ∈ X} {hz₁ : z₁ ∈ X}
    (ε : Path (⟨z₀, hz₀⟩ : ↥X) ⟨z₁, hz₁⟩) {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    (h : IsPunctureProd X T hz₀ g) :
    IsPunctureProd X T hz₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath ε g) := by
  obtain ⟨r, pt, γ, hinj, hrange, hloop, hprod⟩ := h
  refine ⟨r, pt, fun i => FundamentalGroup.fundamentalGroupMulEquivOfPath ε (γ i), hinj, hrange,
    fun i => (hloop i).transport ε, ?_⟩
  have hmap : List.ofFn (fun i => FundamentalGroup.fundamentalGroupMulEquivOfPath ε (γ i))
      = (List.ofFn γ).map (FundamentalGroup.fundamentalGroupMulEquivOfPath ε) := by
    simp [List.map_ofFn, Function.comp_def]
  rw [hmap, ← hprod]
  exact (map_list_prod _ _).symm

end Rigidity.RET

end
