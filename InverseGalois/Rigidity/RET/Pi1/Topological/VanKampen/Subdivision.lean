/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

/-!
# Path subdivision relative to an open cover

The analytic heart of the Seifert–van Kampen theorem: a path in a space covered by two opens
`U ∪ V` can be **chopped into finitely many subpaths, each of which lies entirely in `U` or entirely
in `V`**, and the original path is the concatenation of these pieces (up to homotopy).  This is what
makes every morphism of the fundamental groupoid a composite of morphisms coming from `π(U)` and
`π(V)` — the "generation" half of van Kampen, and the input to the universal functor.

The compactness content is supplied by Mathlib's Lebesgue-number partition lemma
`exists_monotone_Icc_subset_open_cover_unitInterval`; the reassembly up to homotopy is
`Path.Homotopic.concat_subpath`.

## Main declarations

* `Rigidity.RET.VanKampen.exists_subpath_cover` — a partition `0 = t₀ ≤ ⋯ ≤ t_n = 1` of `[0,1]`
  such that each subpath `γ.subpath tₖ tₖ₊₁` has range inside `U` or inside `V`.
-/

open Set unitInterval Path

namespace Rigidity.RET.VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)

/-- **Cover subdivision of a path.**  For an open cover `X = U ∪ V` and any path `γ`, there is a
finite monotone partition `t₀ = 0 ≤ ⋯ ≤ t_n = 1` of the parameter interval such that on every
subinterval `[tₖ, tₖ₊₁]` the path stays inside a single cover element: each subpath
`γ.subpath tₖ tₖ₊₁` has its range contained in `U`, or contained in `V`.

This is the Lebesgue-number subdivision at the base of the Seifert–van Kampen theorem: it exhibits
`γ` as a concatenation of pieces each living in one open set (see `Path.Homotopic.concat_subpath`
for the homotopy reassembly). -/
theorem exists_subpath_cover (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {a b : X} (γ : Path a b) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ k : Fin n, (range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U) ∨
                   (range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ V) := by
  -- The two-element open cover of the parameter interval, pulled back along `γ`.
  set c : Bool → Set I := fun i => γ ⁻¹' (cond i V U) with hc
  have hco : ∀ i, IsOpen (c i) := by
    intro i; cases i
    · exact hU.preimage γ.continuous
    · exact hV.preimage γ.continuous
  have hcov : (univ : Set I) ⊆ ⋃ i, c i := by
    intro s _
    have : γ s ∈ U ∪ V := by rw [hUV]; trivial
    rcases this with h | h
    · exact mem_iUnion.2 ⟨false, h⟩
    · exact mem_iUnion.2 ⟨true, h⟩
  obtain ⟨s, s0, smono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hco hcov
  refine ⟨N, fun k => s k, ?_, ?_, ?_, ?_⟩
  · simpa using s0
  · simpa using hN N le_rfl
  · exact fun i j hij => smono (by exact_mod_cast hij)
  · intro k
    simp only [Fin.val_succ, Fin.val_castSucc]
    obtain ⟨i, hi⟩ := hsub (k : ℕ)
    have hle : s (k : ℕ) ≤ s ((k : ℕ) + 1) := smono (Nat.le_succ _)
    have hrange : range (γ.subpath (s (k : ℕ)) (s ((k : ℕ) + 1)))
        = γ '' Icc (s (k : ℕ)) (s ((k : ℕ) + 1)) :=
      range_subpath_of_le γ _ _ hle
    have himg : γ '' Icc (s (k : ℕ)) (s ((k : ℕ) + 1)) ⊆ cond i V U :=
      (Set.image_mono hi).trans (image_preimage_subset γ (cond i V U))
    cases i with
    | false =>
      exact Or.inl (by rw [hrange]; exact himg)
    | true =>
      exact Or.inr (by rw [hrange]; exact himg)

end Rigidity.RET.VanKampen
