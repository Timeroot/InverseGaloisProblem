/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.ExistenceLowRank
import InverseGalois.Rigidity.RET.TwoPointCyclic

/-!
# The covers correspondence for at most two branch points

For at most two branch points both directions of the correspondence between covers of the line and
finite quotients of the sphere group are available.

The existence direction is the Kummer cover: a product-one generating tuple of length at most two
generates a cyclic group, and a cyclic group of order `n` is the deck group of the cover
`uⁿ = (T - t₀)ᵃ (T - t₁)ᵇ`.  The completeness direction is the statement that the sphere with at
most two punctures has cyclic fundamental group: no branch point leaves the affine line, which is
simply connected; one branch point leaves the sphere with one puncture, which is simply connected
too; and two branch points leave the sphere with two punctures, whose covers are the Kummer covers.

## Main results

* `Rigidity.RET.geomRET_of_le_two` — the covers correspondence for at most two branch points.
-/

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-- **The covers correspondence for at most two branch points.**

For at most two points of the line, covers of the line unramified outside those points and infinity
correspond to finite quotients of the sphere group: a generating product-one tuple in a finite
group is the tuple of branch cycles of a cover with that deck group, and every cover with that
branch locus has such a tuple of branch cycles. -/
theorem geomRET_of_le_two {r : ℕ} (hr : r ≤ 2) (t : Fin r → k) (ht : Function.Injective t) :
    GeomRET t := by
  refine ⟨fun {_} _ _ h hprod htop => exists_cover_of_le_two hr t ht h hprod htop, ?_⟩
  intro L hS hinf
  interval_cases r
  · exact LineCover.exists_branchCycleGenSystem_empty L t hS hinf
  · exact LineCover.exists_branchCycleGenSystem_singleton L t hS hinf
  · exact LineCover.exists_branchCycleGenSystem_pair L t ht hS hinf

end Rigidity.RET
