/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.QuotientPi1
import Mathlib.Analysis.Complex.CoveringMap

/-!
# The tame cyclic cover of the punctured plane

The `n`-th power map `z ↦ zⁿ` on `ℂˣ` is a covering map (a *quotient* covering by the group of
`n`-th roots of unity `μₙ = ker(z ↦ zⁿ)`).  Its total space `ℂˣ` is path connected but **not**
simply connected, so it is not the universal cover; it is the degree-`n` cyclic cover of the
once-punctured line.  This is the topological model of **tame ramification** of order `n`: the local
monodromy around a puncture is cyclic of order `n`.

This file records, for that cover:

* `Complex.instPathConnectedSpaceUnits : PathConnectedSpace ℂˣ` — the base (and total) space is path
  connected (the punctured plane is);
* `Complex.npowCover : IsCoveringMap (fun z : ℂˣ ↦ z ^ n)` — the power map is a covering map;
* `Complex.npow_orbitMap_surjective` — the monodromy of `π₁(ℂˣ)` acts **transitively** on each
  fibre (the cover is connected): tame inertia acts transitively;
* `Complex.npow_fibre_card` — each fibre has exactly `n` points (a `μₙ`-torsor), so the tame
  monodromy is cyclic of order `n`.

Together with `π₁(ℂ ∖ 0) ≅ ℤ` (`CircleGroup.lean`), this says the local monodromy of the degree-`n`
tame cover is the reduction `ℤ ↠ ℤ/n ≅ μₙ` — the canonical generator of tame inertia.  It is the
topological shadow of the tame-inertia cyclicity used in the branch-cycle description of `π₁` (link
**C** of `GAGA_DREAM.md`).

The complex-exponential covering (`isAddQuotientCoveringMap_exp`) locally removes the
`Units.mulAction'` instance to avoid a scalar-action diamond on `ℂˣ`; we do the same, confined to a
`section`, so the removal does not leak to importers.
-/

open Topology

namespace Complex

section
-- Match the environment of `Complex.isQuotientCoveringMap_npow`, which removes this instance to
-- pin the `μₙ`-action on `ℂˣ`.  The removal is section-scoped and does not export.
attribute [-instance] Units.mulAction'

/-- The `n`-th power map `z ↦ zⁿ` on `ℂˣ` is a covering map — the degree-`n` cyclic (tame) cover of
the punctured line. -/
noncomputable def npowCover (n : ℕ) [NeZero n] : IsCoveringMap (fun z : ℂˣ ↦ z ^ n) :=
  (Complex.isQuotientCoveringMap_npow n).isCoveringMap

/-- The fibre of the degree-`n` power cover over `e₀ⁿ` is the `μₙ`-orbit of `e₀`: the roots-of-unity
group identifies with the fibre. -/
noncomputable def npowFibreEquiv (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    (powMonoidHom (α := ℂˣ) n).ker ≃ (fun z : ℂˣ ↦ z ^ n) ⁻¹' {e₀ ^ n} :=
  (Complex.isQuotientCoveringMap_npow n).actionEquiv e₀

end

/-- **Tame inertia acts transitively.**  The monodromy of `π₁(ℂˣ)` on the fibre of the degree-`n`
power cover is transitive: every point of the fibre is the endpoint of the lift of some loop from
`e₀`.  (The cover is connected because `ℂˣ` is path connected.) -/
theorem npow_orbitMap_surjective (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Function.Surjective ((npowCover n).orbitMap (e₀ ^ n) ⟨e₀, rfl⟩) :=
  (npowCover n).orbitMap_surjective (e₀ ^ n) ⟨e₀, rfl⟩

/-- **The tame cover has degree `n`.**  Each fibre of `z ↦ zⁿ` on `ℂˣ` has exactly `n` points — it
is a `μₙ`-torsor — so the (cyclic) tame monodromy has order `n`. -/
theorem npow_fibre_card (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Nat.card ((fun z : ℂˣ ↦ z ^ n) ⁻¹' {e₀ ^ n}) = n := by
  rw [← Nat.card_congr (npowFibreEquiv n e₀),
    show (powMonoidHom (α := ℂˣ) n).ker = rootsOfUnity n ℂ from
      (rootsOfUnity_eq_ker (k := n) (M := ℂ)).symm,
    Nat.card_eq_fintype_card, (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).card_rootsOfUnity]

end Complex
