/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Shifting

/-!
# Shifting the degree by an arbitrary amount

A single shift moves the complete cohomology of a representation one degree up, and a single
coshift moves it one degree down.  Iterating either of them therefore moves it by as much as one
likes: the complete cohomology of the `j`-fold shift in a degree is the complete cohomology of the
representation `j` degrees higher, and the complete cohomology of the `j`-fold coshift `j` degrees
higher is the complete cohomology of the representation itself.

The statements are recorded as transfers of the vanishing in both directions, which is the form in
which they are used: a statement about a single degree can be moved to any other degree at the
price of replacing the representation by an iterated shift or coshift of it.

## Main definitions

* `InverseGalois.CFT.Tate.shiftIter`, `InverseGalois.CFT.Tate.coshiftIter`: the iterated shift and
  coshift of a representation.

## Main results

* `InverseGalois.CFT.Tate.isZero_tateModule_shiftIter`,
  `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_shiftIter`: **the iterated shift moves the
  degree up.**
* `InverseGalois.CFT.Tate.isZero_tateModule_coshiftIter`,
  `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_coshiftIter`: **the iterated coshift moves
  the degree down.**

## Tags

Tate cohomology, dimension shifting, iterated shift
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-! ### Transporting the vanishing -/

omit [Group G] [Finite G] in
/-- **A module linearly isomorphic to one with nothing in it has nothing in it.** -/
theorem isZero_of_linearEquiv {M N : ModuleCat.{u} k} (e : M ≃ₗ[k] N) (h : Limits.IsZero N) :
    Limits.IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact e.injective.subsingleton

/-- **The vanishing of the complete cohomology depends only on the degree.** -/
theorem isZero_tateModule_congr {A : Rep k G} {m n : ℤ} (h : m = n)
    (hz : Limits.IsZero (tateModule A m)) : Limits.IsZero (tateModule A n) := h ▸ hz

/-! ### Iterating the shift and the coshift -/

/-- **The shift of a representation, iterated.** -/
def shiftIter (A : Rep k G) : ℕ → Rep k G
  | 0 => A
  | j + 1 => shiftObj (shiftIter A j)

/-- **The coshift of a representation, iterated.** -/
def coshiftIter (A : Rep k G) : ℕ → Rep k G
  | 0 => A
  | j + 1 => coshiftObj (coshiftIter A j)

/-! ### Moving the degree up -/

/-- **Nothing in a degree of a representation means nothing that many degrees lower in its iterated
shift.** -/
theorem isZero_tateModule_shiftIter (A : Rep k G) :
    ∀ (j : ℕ) (n : ℤ), Limits.IsZero (tateModule A (n + j)) →
      Limits.IsZero (tateModule (shiftIter A j) n) := by
  intro j
  induction j with
  | zero => exact fun n h => isZero_tateModule_congr (by simp) h
  | succ j ih =>
    intro n h
    refine isZero_of_linearEquiv (tateShiftEquiv (shiftIter A j) n) ?_
    exact ih (n + 1) (isZero_tateModule_congr (by push_cast; ring) h)

/-- **Nothing in a degree of an iterated shift means nothing that many degrees higher in the
representation.** -/
theorem isZero_tateModule_of_isZero_shiftIter (A : Rep k G) :
    ∀ (j : ℕ) (n : ℤ), Limits.IsZero (tateModule (shiftIter A j) n) →
      Limits.IsZero (tateModule A (n + j)) := by
  intro j
  induction j with
  | zero => exact fun n h => isZero_tateModule_congr (by simp) h
  | succ j ih =>
    intro n h
    have h1 : Limits.IsZero (tateModule (shiftIter A j) (n + 1)) :=
      isZero_of_linearEquiv (tateShiftEquiv (shiftIter A j) n).symm h
    exact isZero_tateModule_congr (by push_cast; ring) (ih (n + 1) h1)

/-! ### Moving the degree down -/

/-- **Nothing in a degree of a representation means nothing that many degrees higher in its
iterated coshift.** -/
theorem isZero_tateModule_coshiftIter (A : Rep k G) :
    ∀ (j : ℕ) (n : ℤ), Limits.IsZero (tateModule A n) →
      Limits.IsZero (tateModule (coshiftIter A j) (n + j)) := by
  intro j
  induction j with
  | zero => exact fun n h => isZero_tateModule_congr (by simp) h
  | succ j ih =>
    intro n h
    refine isZero_tateModule_congr (m := n + (j : ℤ) + 1) (by push_cast; ring) ?_
    exact isZero_of_linearEquiv (tateCoshiftEquiv (coshiftIter A j) (n + j)).symm (ih n h)

/-- **Nothing in a degree of an iterated coshift means nothing that many degrees lower in the
representation.** -/
theorem isZero_tateModule_of_isZero_coshiftIter (A : Rep k G) :
    ∀ (j : ℕ) (n : ℤ), Limits.IsZero (tateModule (coshiftIter A j) (n + j)) →
      Limits.IsZero (tateModule A n) := by
  intro j
  induction j with
  | zero => exact fun n h => isZero_tateModule_congr (by simp) h
  | succ j ih =>
    intro n h
    refine ih n (isZero_of_linearEquiv (tateCoshiftEquiv (coshiftIter A j) (n + j)) ?_)
    exact isZero_tateModule_congr (by push_cast; ring) h

end

end InverseGalois.CFT.Tate
