/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Local.ProdOneGeneration
import InverseGalois.Rigidity.RET.UniversalTuple

/-!
# The Riemann Existence Theorem for the line, assembled

The correspondence between covers of the line branched over a prescribed tuple of points and
finite quotients of the sphere group has two directions (`RET/GeomRET.lean`).  This file puts them
together into the single statement `Rigidity.RET.geomRET` that the rigidity method consumes, and
records the two forms of the completeness direction used downstream.

The completeness direction is the one obtained from the spider: the names of its loops are
distinguished inertia elements, one at each puncture, generating the deck group and multiplying to
the identity once the name of the loop at infinity is appended — and that last name is the
identity on a cover unramified at infinity.

## Main results

* `Rigidity.RET.geomRET` — the correspondence holds for any injective tuple of points.
* `Rigidity.RET.exists_branchCycleSystem` — the completeness direction.
* `Rigidity.RET.exists_branchCycleGenSystem` — the completeness direction with the branch cycles
  generating the local inertia groups.
-/

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-- **The Riemann Existence Theorem for the line over `ℚ̄`.**

For `r` distinct points of the line, covers of the line unramified outside those points and
infinity correspond to finite quotients of the fundamental group of the `r`-punctured sphere, the
sphere group `Γ_r = ⟨x₀,…,x_{r-1} | x₀⋯x_{r-1} = 1⟩`: a generating product-one tuple in a finite
group `H` is the tuple of branch cycles of a cover with deck group `H`, and every cover with that
branch locus has such a tuple of branch cycles. -/
theorem geomRET {r : ℕ} (t : Fin r → k) (ht : Function.Injective t) : GeomRET t where
  exists_cover := geomRETExistence_of_injective t ht
  exists_cycles := geomRETCompleteness_of_injective ht

/-- **A cover branched only over the given points has branch cycles there.** -/
theorem exists_branchCycleSystem {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (L : LineCover) (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleSystem t g :=
  (geomRETCompleteness_of_injective ht L hS hinf).imp fun _ h => h.toIsBranchCycleSystem

/-- **A cover branched only over the given points has distinguished branch cycles there**: the
branch cycles can be taken to *generate* the local inertia groups, not merely to lie in them. -/
theorem exists_branchCycleGenSystem {r : ℕ} (t : Fin r → k) (ht : Function.Injective t)
    (L : LineCover) (hS : L.IsUnramifiedOutside (Set.range t)) (hinf : L.IsUnramifiedAtInfinity) :
    ∃ g : Fin r → L.deck, L.IsBranchCycleGenSystem t g :=
  geomRETCompleteness_of_injective ht L hS hinf

end Rigidity.RET

end
