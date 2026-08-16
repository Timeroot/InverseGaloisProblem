/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Moderate
import InverseGalois.Rigidity.RET.Analytic.CoverRing

/-!
# A function that sees the deck group separates all but finitely many fibres

A function of moderate growth that is moved by every nontrivial deck transformation need not take
distinct values at the points of every fibre: each deck transformation is moved *somewhere*, and
the places where it is not are the zeros of a holomorphic function.  Those places are nevertheless
confined to finitely many fibres, and the reason is that the product

  `∏ (G (a • y) - G (b • y))`   over the pairs `a ≠ b` of deck transformations

is again a function of moderate growth on the covering, is invariant under the deck group, and is
not identically zero — the ring of functions of a connected covering is a domain, and each factor
is nonzero.  An invariant function of moderate growth is a rational function of the base
coordinate, so it vanishes only over the roots of a polynomial.  Off those roots the product does
not vanish, which says exactly that the function is injective on the fibre.

## Main definitions

* `Rigidity.RET.sepProd` — the product of the differences of the values of a function along a
  fibre.

## Main results

* `Rigidity.RET.sepProd_smul`, `Rigidity.RET.sepProd_mem_coverRing` — it is invariant and of
  moderate growth.
* `Rigidity.RET.exists_sepProd_ne_zero` — on a connected covering it is not identically zero.
* `Rigidity.RET.exists_finset_separating` — a function of moderate growth moved by every nontrivial
  deck transformation separates every fibre over the complement of a finite set.
-/

open Polynomial Topology

noncomputable section

namespace Rigidity.RET

section Domain

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
  {S : Finset ℂ}

/-- **A product of two functions of the covering, neither identically zero, is not identically
zero**: the ring of functions of a connected covering is a domain. -/
theorem exists_mul_ne_zero (hf : IsLocalHomeomorph f) {F G : Y → ℂ}
    (hF : F ∈ coverRing hf S) (hG : G ∈ coverRing hf S) (hFne : ∃ y, F y ≠ 0)
    (hGne : ∃ y, G y ≠ 0) : ∃ y, F y * G y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : (⟨F, hF⟩ : ↥(coverRing hf S)) * ⟨G, hG⟩ = 0 :=
    Subtype.ext (funext fun y => hcon y)
  rcases mul_eq_zero.1 hzero with h | h
  · obtain ⟨y, hy⟩ := hFne
    exact hy (congrFun (congrArg Subtype.val h) y)
  · obtain ⟨y, hy⟩ := hGne
    exact hy (congrFun (congrArg Subtype.val h) y)

/-- **A finite product of functions of the covering, none identically zero, is not identically
zero.** -/
theorem exists_prod_ne_zero (hf : IsLocalHomeomorph f) {ι : Type*} (t : Finset ι) (g : ι → Y → ℂ)
    (hmem : ∀ i ∈ t, g i ∈ coverRing hf S) (hne : ∀ i ∈ t, ∃ y, g i y ≠ 0) :
    ∃ y : Y, ∏ i ∈ t, g i y ≠ 0 := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨Classical.arbitrary Y, by simp⟩
  | insert i t hi ih =>
    have hmem' : ∀ j ∈ t, g j ∈ coverRing hf S := fun j hj =>
      hmem j (Finset.mem_insert_of_mem hj)
    have hne' : ∀ j ∈ t, ∃ y, g j y ≠ 0 := fun j hj => hne j (Finset.mem_insert_of_mem hj)
    obtain ⟨y, hy⟩ := ih hmem' hne'
    obtain ⟨y', hy'⟩ := exists_mul_ne_zero hf (hmem i (Finset.mem_insert_self i t))
      (Subring.prod_mem _ hmem') (hne i (Finset.mem_insert_self i t)) ⟨y, by
        rw [Finset.prod_apply]; exact hy⟩
    refine ⟨y', ?_⟩
    rw [Finset.prod_insert hi]
    rwa [Finset.prod_apply] at hy'

end Domain

/-! ### The product of the differences along a fibre -/

section SepProd

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℂ} {S : Finset ℂ}
variable {H : Type*} [Group H] [Fintype H] [DecidableEq H] [MulAction H Y]

/-- The pairs of distinct elements of the deck group. -/
def sepPairs (H : Type*) [Fintype H] [DecidableEq H] : Finset (H × H) :=
  Finset.univ.filter fun p => p.1 ≠ p.2

omit [Group H] in
theorem mem_sepPairs {p : H × H} : p ∈ sepPairs H ↔ p.1 ≠ p.2 := by
  simp [sepPairs]

/-- **The product of the differences of the values of a function along a fibre.**  It vanishes at a
point exactly when the function fails to separate the fibre through it. -/
def sepProd (H : Type*) [Group H] [Fintype H] [DecidableEq H] [MulAction H Y] (G : Y → ℂ) :
    Y → ℂ :=
  fun y => ∏ p ∈ sepPairs H, (G (p.1 • y) - G (p.2 • y))

omit [TopologicalSpace Y] in
/-- **The product of the differences is invariant under the deck group**: translating the fibre
permutes the pairs of distinct deck transformations. -/
theorem sepProd_smul (G : Y → ℂ) (b : H) (y : Y) :
    sepProd H G (b • y) = sepProd H G y := by
  refine Finset.prod_equiv ((Equiv.mulRight b).prodCongr (Equiv.mulRight b)) (fun p => ?_)
    (fun p _ => ?_)
  · simp only [mem_sepPairs, Equiv.prodCongr_apply, Equiv.coe_mulRight, Prod.map_fst,
      Prod.map_snd, ne_eq, mul_left_inj]
  · simp only [Equiv.prodCongr_apply, Equiv.coe_mulRight, Prod.map_fst, Prod.map_snd, smul_smul]

section Ring

variable [ContinuousConstSMul H Y] [IsOverBase H f]

omit [Fintype H] [DecidableEq H] in
/-- Precomposing with a deck transformation preserves the ring of functions of the covering. -/
theorem mem_coverRing_comp_smul (hf : IsLocalHomeomorph f) (S : Finset ℂ) {F : Y → ℂ}
    (hF : F ∈ coverRing hf S) (a : H) : (fun y => F (a • y)) ∈ coverRing hf S :=
  ⟨hF.1.comp_homeomorph (perm := Homeomorph.smul a) (IsOverBase.smul_eq a),
    hF.2.comp (IsOverBase.smul_eq a)⟩

/-- **The product of the differences is a function of moderate growth on the covering.** -/
theorem sepProd_mem_coverRing (hf : IsLocalHomeomorph f) {G : Y → ℂ}
    (hG : G ∈ coverRing hf S) : sepProd H G ∈ coverRing hf S := by
  have hrw : sepProd H G
      = ∏ p ∈ sepPairs H, (fun y : Y => G (p.1 • y) - G (p.2 • y)) := by
    funext y
    rw [Finset.prod_apply]
    rfl
  rw [hrw]
  exact Subring.prod_mem _ fun p _ => Subring.sub_mem _
    (mem_coverRing_comp_smul hf S hG p.1) (mem_coverRing_comp_smul hf S hG p.2)

end Ring

omit [TopologicalSpace Y] in
/-- **Where the product of the differences does not vanish, the function separates the fibre.** -/
theorem ne_of_sepProd_ne_zero {G : Y → ℂ} {y : Y} (hy : sepProd H G y ≠ 0) (c : H) (hc : c ≠ 1) :
    G (c • y) ≠ G y := by
  have hmem : (c, (1 : H)) ∈ sepPairs H := mem_sepPairs.2 hc
  have := (Finset.prod_ne_zero_iff.1 hy) (c, (1 : H)) hmem
  simpa [sub_ne_zero] using this

/-- **On a connected covering the product of the differences is not identically zero**, as soon as
every nontrivial deck transformation moves the function somewhere. -/
theorem exists_sepProd_ne_zero [Nonempty Y] [PreconnectedSpace Y] [ContinuousConstSMul H Y]
    [IsOverBase H f] (hf : IsLocalHomeomorph f) {G : Y → ℂ} (hG : G ∈ coverRing hf S)
    (hne : ∀ c : H, c ≠ 1 → ∃ y : Y, G (c • y) ≠ G y) : ∃ y : Y, sepProd H G y ≠ 0 := by
  refine exists_prod_ne_zero hf (sepPairs H) (fun p y => G (p.1 • y) - G (p.2 • y))
    (fun p _ => Subring.sub_mem _ (mem_coverRing_comp_smul hf S hG p.1)
      (mem_coverRing_comp_smul hf S hG p.2)) fun p hp => ?_
  have hc : p.1 * p.2⁻¹ ≠ 1 := fun h => (mem_sepPairs.1 hp) (mul_inv_eq_one.1 h)
  obtain ⟨y, hy⟩ := hne _ hc
  refine ⟨p.2⁻¹ • y, ?_⟩
  simp only [smul_smul, mul_inv_cancel, one_smul, sub_ne_zero]
  exact hy

end SepProd

/-! ### Separation off a finite set -/

section Finite

variable {Y : Type*} [TopologicalSpace Y] [Nonempty Y] [PreconnectedSpace Y] {f : Y → ℂ}
  {S : Finset ℂ}
variable {H : Type*} [Group H] [Fintype H] [MulAction H Y] [ContinuousConstSMul H Y]
  [IsOverBase H f]

/-- **A function of moderate growth moved by every nontrivial deck transformation takes distinct
values at the points of every fibre over the complement of a finite set.**

The product of the differences of its values along a fibre is invariant and of moderate growth, so
it is a rational function of the base coordinate; being not identically zero, it vanishes only over
the roots of the numerator, and those are the fibres to discard. -/
theorem exists_finset_separating (hf : IsLocalHomeomorph f)
    (htrans : ∀ y y' : Y, f y = f y' → ∃ c : H, y' = c • y)
    (hrange : Set.range f = ((S : Set ℂ))ᶜ) {G : Y → ℂ} (hG : G ∈ coverRing hf S)
    (hne : ∀ c : H, c ≠ 1 → ∃ y : Y, G (c • y) ≠ G y) :
    ∃ S' : Finset ℂ, S ⊆ S' ∧
      ∀ y : Y, f y ∉ (S' : Set ℂ) → ∀ c : H, c ≠ 1 → G (c • y) ≠ G y := by
  classical
  have hDmem : sepProd H G ∈ coverRing hf S := sepProd_mem_coverRing hf hG
  obtain ⟨p, q, -, hqne, hpq⟩ := exists_eq_div_of_invariant_of_moderate (H := H) hf htrans
    hDmem.1 (fun a y => sepProd_smul G a y) hrange hDmem.2
  obtain ⟨y₁, hy₁⟩ := exists_sepProd_ne_zero hf hG hne
  have hp : p ≠ 0 := by
    intro h0
    exact hy₁ (by rw [hpq y₁, h0, eval_zero, zero_div])
  refine ⟨S ∪ p.roots.toFinset, Finset.subset_union_left, fun y hy c hc => ?_⟩
  refine ne_of_sepProd_ne_zero (H := H) ?_ c hc
  rw [hpq y]
  refine div_ne_zero (fun h0 => hy ?_) (hqne y)
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Multiset.mem_toFinset]
  exact Or.inr ((mem_roots hp).2 h0)

end Finite

end Rigidity.RET

end
