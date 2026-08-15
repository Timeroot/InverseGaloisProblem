/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# Ordered products of puncture loops

A spider relation says that a given loop is, in a prescribed order, the product of one loop around
each of the missing points.  This file introduces the predicate `IsPunctureProd X T hz₀ g N` saying
that `g` is such a product for the finite set `T` of punctures, and that the factors generate at
least the subgroup `N`; and the combinators that make it usable in a geometric induction:

* the empty product is trivial and a single puncture loop is a product over a singleton;
* products over disjoint sets of punctures multiply, in the order in which they are written;
* a product survives moving the basepoint along a path.

Carrying the subgroup `N` along is what lets a single system of loops be produced that both
multiplies out to the prescribed loop *and* generates: each combinator records how much of the
ambient fundamental group the factors already account for, and the geometric induction feeds that
clause with the Seifert–van Kampen theorem.

Because the number of factors is packaged as an anonymous `Fin r`-indexed family with injective
labels, gluing two products is `Fin.append` and nothing else.

## Main results

* `Rigidity.RET.IsPunctureProd` — the predicate.
* `Rigidity.RET.IsPunctureProd.mono` — the subgroup clause may be weakened.
* `Rigidity.RET.IsPunctureProd.mul` — products over disjoint sets of punctures multiply.
* `Rigidity.RET.IsPunctureProd.transport` — a product survives moving the basepoint.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-- A loop of a region of the plane is a **product of puncture loops around `T` generating `N`**
when it is the ordered product of one loop winding around each point of `T`, and those loops
generate at least the subgroup `N`. -/
def IsPunctureProd (X : Set ℂ) (T : Set ℂ) {z₀ : ℂ} (hz₀ : z₀ ∈ X)
    (g : FundamentalGroup ↥X ⟨z₀, hz₀⟩) (N : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)) : Prop :=
  ∃ (r : ℕ) (pt : Fin r → ℂ) (γ : Fin r → FundamentalGroup ↥X ⟨z₀, hz₀⟩),
    Function.Injective pt ∧ Set.range pt = T ∧
      (∀ i, IsPunctureLoop X (pt i) hz₀ (γ i)) ∧ (List.ofFn γ).prod = g ∧
      N ≤ Subgroup.closure (Set.range γ)

/-- Asking the puncture loops to generate less is a weaker statement. -/
theorem IsPunctureProd.mono {X T : Set ℂ} {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩} {N N' : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)}
    (h : IsPunctureProd X T hz₀ g N) (hN : N' ≤ N) : IsPunctureProd X T hz₀ g N' := by
  obtain ⟨r, pt, γ, hinj, hrange, hloop, hprod, hgen⟩ := h
  exact ⟨r, pt, γ, hinj, hrange, hloop, hprod, hN.trans hgen⟩

/-- The trivial loop is the empty product of puncture loops. -/
theorem IsPunctureProd.one {X : Set ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ X) :
    IsPunctureProd X ∅ hz₀ 1 ⊥ :=
  ⟨0, Fin.elim0, Fin.elim0, Function.injective_of_subsingleton _, by simp, fun i => i.elim0,
    by simp, bot_le⟩

/-- A loop winding once around a single point is a product of puncture loops over a singleton,
and its powers are all that it generates. -/
theorem IsPunctureProd.single {X : Set ℂ} {s z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩} (hg : IsPunctureLoop X s hz₀ g) :
    IsPunctureProd X {s} hz₀ g (Subgroup.zpowers g) :=
  ⟨1, fun _ => s, fun _ => g, Function.injective_of_subsingleton _, by simp, fun _ => hg, by simp,
    Subgroup.zpowers_le.2 (Subgroup.subset_closure ⟨0, rfl⟩)⟩

/-- Being a product of puncture loops transfers along an equality of loops. -/
theorem IsPunctureProd.congr {X T : Set ℂ} {z₀ : ℂ} {hz₀ : z₀ ∈ X}
    {g g' : FundamentalGroup ↥X ⟨z₀, hz₀⟩} {N : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)}
    (h : IsPunctureProd X T hz₀ g N) (hg : g = g') :
    IsPunctureProd X T hz₀ g' N := hg ▸ h

/-! ### Gluing two indexed families -/

/-- The range of a concatenation of two families is the union of the ranges. -/
theorem _root_.Fin.range_append {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
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
    {g₁ g₂ : FundamentalGroup ↥X ⟨z₀, hz₀⟩} {N₁ N₂ : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)}
    (h₁ : IsPunctureProd X T₁ hz₀ g₁ N₁)
    (h₂ : IsPunctureProd X T₂ hz₀ g₂ N₂) (hdisj : Disjoint T₁ T₂) :
    IsPunctureProd X (T₁ ∪ T₂) hz₀ (g₁ * g₂) (N₁ ⊔ N₂) := by
  obtain ⟨r₁, pt₁, γ₁, hinj₁, hrange₁, hloop₁, hprod₁, hgen₁⟩ := h₁
  obtain ⟨r₂, pt₂, γ₂, hinj₂, hrange₂, hloop₂, hprod₂, hgen₂⟩ := h₂
  refine ⟨r₁ + r₂, Fin.append pt₁ pt₂, Fin.append γ₁ γ₂,
    injective_fin_append hinj₁ hinj₂ (by rw [hrange₁, hrange₂]; exact hdisj),
    by rw [Fin.range_append, hrange₁, hrange₂], fun i => ?_, ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i => rw [Fin.append_left, Fin.append_left]; exact hloop₁ i
    | right i => rw [Fin.append_right, Fin.append_right]; exact hloop₂ i
  · rw [List.ofFn_fin_append, List.prod_append, hprod₁, hprod₂]
  · rw [Fin.range_append]
    exact sup_le (hgen₁.trans (Subgroup.closure_mono Set.subset_union_left))
      (hgen₂.trans (Subgroup.closure_mono Set.subset_union_right))

/-- **A product of puncture loops survives moving the basepoint along a path.** -/
theorem IsPunctureProd.transport {X T : Set ℂ} {z₀ z₁ : ℂ} {hz₀ : z₀ ∈ X} {hz₁ : z₁ ∈ X}
    (ε : Path (⟨z₀, hz₀⟩ : ↥X) ⟨z₁, hz₁⟩) {g : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    {N : Subgroup (FundamentalGroup ↥X ⟨z₀, hz₀⟩)} (h : IsPunctureProd X T hz₀ g N) :
    IsPunctureProd X T hz₁ (FundamentalGroup.fundamentalGroupMulEquivOfPath ε g)
      (N.map (FundamentalGroup.fundamentalGroupMulEquivOfPath ε).toMonoidHom) := by
  obtain ⟨r, pt, γ, hinj, hrange, hloop, hprod, hgen⟩ := h
  refine ⟨r, pt, fun i => FundamentalGroup.fundamentalGroupMulEquivOfPath ε (γ i), hinj, hrange,
    fun i => (hloop i).transport ε, ?_, ?_⟩
  · have hmap : List.ofFn (fun i => FundamentalGroup.fundamentalGroupMulEquivOfPath ε (γ i))
        = (List.ofFn γ).map (FundamentalGroup.fundamentalGroupMulEquivOfPath ε) := by
      simp [List.map_ofFn, Function.comp_def]
    rw [hmap, ← hprod]
    exact (map_list_prod _ _).symm
  · refine (Subgroup.map_mono hgen).trans ?_
    rw [MonoidHom.map_closure, ← Set.range_comp]
    exact le_rfl

end Rigidity.RET

end
