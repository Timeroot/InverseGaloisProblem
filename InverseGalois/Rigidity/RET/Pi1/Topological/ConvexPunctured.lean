/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A convex region with countably many points removed is path connected

Mathlib knows that the complement of a countable set in a real vector space of dimension at least
two is path connected.  The van Kampen induction that computes the fundamental group of a punctured
region needs the same statement inside an open convex region: the two pieces into which a line cuts
a punctured convex region are again punctured convex regions, and van Kampen asks for them to be
path connected.

The proof of the ambient statement carries over.  Two points of the region are joined through an
auxiliary third point `c + t • y`, where `c` is the midpoint, `y` is linearly independent from
`b - a`, and `t` is small.  For distinct `t` the two segments involved meet only at their common
endpoint, so only countably many `t` are spoilt by the removed set; the good `t` are dense, so some
good `t` is small enough for the auxiliary point to lie in the region, and then both segments lie in
the region by convexity.

## Main results

* `Convex.isPathConnected_diff_countable` — an open convex set minus a countable set is path
  connected.
* `Convex.pathConnectedSpace_diff_countable` — the same, as an instance-shaped statement about the
  subtype.
-/

open Set
open scoped Convex

namespace Rigidity.RET

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E]

/-- The auxiliary points `c + t • y` that lie in `W` form an open set of parameters containing
`0`. -/
theorem isOpen_setOf_add_smul_mem {W : Set E} (hW : IsOpen W) (c y : E) :
    IsOpen {t : ℝ | c + t • y ∈ W} :=
  hW.preimage (by fun_prop)

/-- **An open convex set with a countable set removed is path connected.** -/
theorem Convex.isPathConnected_diff_countable (h : 1 < Module.rank ℝ E) {W : Set E}
    (hconv : Convex ℝ W) (hW : IsOpen W) {S : Set E} (hS : S.Countable)
    (hne : (W \ S).Nonempty) : IsPathConnected (W \ S) := by
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  set c := (2 : ℝ)⁻¹ • (a + b) with hc
  set x := (2 : ℝ)⁻¹ • (b - a) with hx
  have Ia : c - x = a := by rw [hc, hx]; module
  have Ib : c + x = b := by rw [hc, hx]; module
  have x_ne_zero : x ≠ 0 := by simpa [hx] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  -- only countably many auxiliary directions are spoilt by `S`
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty, Ib] using hb.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ S).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ S = ∅ := by
      simpa only [singleton_inter_eq_empty, Ia] using ha.2
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  -- and the auxiliary point stays in the region for all small parameters
  have hmem : (0 : ℝ) ∈ {t : ℝ | c + t • y ∈ W} := by
    have hcW : c ∈ W := by
      have := hconv ha.1 hb.1 (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num)
      simpa [hc, smul_add] using this
    simpa using hcW
  obtain ⟨t, htW, ht⟩ :
      ∃ t : ℝ, t ∈ {t : ℝ | c + t • y ∈ W} ∧
        t ∈ ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ S).Nonempty} ∪
          {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ S).Nonempty})ᶜ := by
    obtain ⟨t, ht⟩ := ((A.union B).dense_compl ℝ).inter_open_nonempty _
      (isOpen_setOf_add_smul_mem hW c y) ⟨0, hmem⟩
    exact ⟨t, ht.1, ht.2⟩
  set z := c + t • y with hz
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq,
    not_nonempty_iff_eq_empty] at ht
  have JA : JoinedIn (W \ S) a z := by
    refine JoinedIn.of_segment_subset (fun w hw => ⟨?_, ?_⟩)
    · exact hconv.segment_subset ha.1 htW hw
    · intro hwS
      have : ([c - x -[ℝ] c + t • y] ∩ S).Nonempty := ⟨w, by rwa [Ia], hwS⟩
      rw [ht.2] at this
      exact this.ne_empty rfl
  have JB : JoinedIn (W \ S) b z := by
    refine JoinedIn.of_segment_subset (fun w hw => ⟨?_, ?_⟩)
    · exact hconv.segment_subset hb.1 htW hw
    · intro hwS
      have : ([c + x -[ℝ] c + t • y] ∩ S).Nonempty := ⟨w, by rwa [Ib], hwS⟩
      rw [ht.1] at this
      exact this.ne_empty rfl
  exact JA.trans JB.symm

/-- **An open convex set with a countable set removed is path connected**, as a statement about
the subtype. -/
theorem Convex.pathConnectedSpace_diff_countable (h : 1 < Module.rank ℝ E) {W : Set E}
    (hconv : Convex ℝ W) (hW : IsOpen W) {S : Set E} (hS : S.Countable)
    (hne : (W \ S).Nonempty) : PathConnectedSpace ↥(W \ S) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (Convex.isPathConnected_diff_countable h hconv hW hS hne)

/-- Over `ℂ` the rank hypothesis is automatic. -/
theorem Convex.pathConnectedSpace_diff_countable_complex {W : Set ℂ} (hconv : Convex ℝ W)
    (hW : IsOpen W) {S : Set ℂ} (hS : S.Countable) (hne : (W \ S).Nonempty) :
    PathConnectedSpace ↥(W \ S) := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  exact Convex.pathConnectedSpace_diff_countable hrank hconv hW hS hne

end Rigidity.RET
