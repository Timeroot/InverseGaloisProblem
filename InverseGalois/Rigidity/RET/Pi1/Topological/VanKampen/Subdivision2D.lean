/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Grid subdivision of a square relative to an open cover

The two-dimensional companion of `VanKampen/Subdivision.lean`.  A continuous map `H : I × I → X`
into a space covered by two opens `U ∪ V` can be **chopped into a finite grid of cells, each of
which maps entirely into `U` or entirely into `V`**.  This is the compactness input to the
homotopy-invariance ("staircase") half of the Seifert–van Kampen theorem: applied to a homotopy
`H` of paths, it lets one cross the square one cell at a time, each crossing being a homotopy
supported in a single cover element.

The compactness content is Mathlib's Lebesgue-number partition lemma for the square,
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`.

## Main declarations

* `Rigidity.RET.VanKampen.exists_grid_cover` — a single monotone partition `t : ℕ → I`
  (with `t 0 = 0` and `t m = 1` for `m ≥ N`) of the parameter interval such that every grid cell
  `[tₙ, tₙ₊₁] × [tₘ, tₘ₊₁]` is carried by `H` into `U`, or into `V`.
-/

open Set unitInterval

namespace Rigidity.RET.VanKampen

variable {X : Type*} [TopologicalSpace X]

/-- **Grid subdivision of a homotopy.**  For an open cover `X = U ∪ V` and any continuous
`H : I × I → X`, there is a finite monotone partition `0 = t₀ ≤ t₁ ≤ ⋯` of the parameter interval,
eventually equal to `1`, such that on every grid cell `[tₙ, tₙ₊₁] × [tₘ, tₘ₊₁]` the map `H` takes
values in a single cover element: the image lands in `U`, or lands in `V`.

This is the Lebesgue-number subdivision at the base of the homotopy-invariance half of the
Seifert–van Kampen theorem, exactly parallel to the one-dimensional `exists_subpath_cover`. -/
theorem exists_grid_cover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    (H : C(I × I, X)) :
    ∃ (t : ℕ → I) (N : ℕ), t 0 = 0 ∧ (∀ m, N ≤ m → t m = 1) ∧ Monotone t ∧
      ∀ n m : ℕ, (H '' (Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1))) ⊆ U) ∨
                 (H '' (Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1))) ⊆ V) := by
  -- The two-element open cover of the square, pulled back along `H`.
  set c : Bool → Set (I × I) := fun i => H ⁻¹' (cond i V U) with hc
  have hco : ∀ i, IsOpen (c i) := by
    intro i; cases i
    · exact hU.preimage H.continuous
    · exact hV.preimage H.continuous
  have hcov : (univ : Set (I × I)) ⊆ ⋃ i, c i := by
    intro s _
    have hs : H s ∈ U ∪ V := by rw [hUV]; trivial
    rcases hs with h | h
    · exact mem_iUnion.2 ⟨false, h⟩
    · exact mem_iUnion.2 ⟨true, h⟩
  obtain ⟨t, t0, tmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hco hcov
  refine ⟨t, N, t0, hN, tmono, ?_⟩
  intro n m
  obtain ⟨i, hi⟩ := hsub n m
  have himg : H '' (Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1))) ⊆ cond i V U :=
    Set.image_subset_iff.2 hi
  cases i with
  | false => exact Or.inl himg
  | true => exact Or.inr himg

end Rigidity.RET.VanKampen
