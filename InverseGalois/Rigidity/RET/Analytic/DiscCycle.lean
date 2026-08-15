/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.RationalDeck
import InverseGalois.Rigidity.RET.Analytic.RootMonodromy
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleLoop
import InverseGalois.Rigidity.RET.Pi1.Topological.LiftMonodromy

/-!
# The monodromy of the circle loop of a punctured disc

A permutation of a fibre of the root cover is a local monodromy element at a parameter when it is
the monodromy of some generator of the fundamental group of a small punctured disc around that
parameter, read at the global basepoint.  Comparing that permutation with the algebra of the cover
requires an *explicit* loop, and the explicit loop is the circle.  This file names the monodromy of
the circle loop of a punctured disc and records that its order is the order of the monodromy of any
other generator, so nothing is lost by making the loop explicit.

A second, unrelated convenience is collected here: a group of formulas permuting the roots away
from a set of exceptional parameters permutes them away from any larger set of parameters as well.
It is what allows the formulas of a cover, which come with the exceptional parameters of the
formulas themselves, to be read on the punctured plane of a coarser degeneracy set.

## Main definitions

* `Rigidity.RET.Analytic.discCycle` — the monodromy of the circle loop of a punctured disc.
* `Rigidity.RET.Analytic.RationalDeck.mono` — a group of root formulas, read away from a larger set
  of exceptional parameters.

## Main results

* `Rigidity.RET.Analytic.orderOf_discCycle` — the circle loop of a punctured disc has the monodromy
  order of any generator of the fundamental group of the disc.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

variable {P : Polynomial (Polynomial ℂ)} {S : Finset ℂ} {G : Type} [Group G]

/-! ### Enlarging the exceptional set -/

/-- **A group of root formulas, read away from a larger set of exceptional parameters.**  Every
requirement is a statement about the parameters outside the exceptional set, so it only gets
weaker as that set grows. -/
def RationalDeck.mono (D : RationalDeck P S G) {S' : Finset ℂ} (hS : (S : Set ℂ) ⊆ (S' : Set ℂ)) :
    RationalDeck P S' G where
  act := D.act
  continuousOn := fun g => (D.continuousOn g).mono fun _ hq h => hq (hS h)
  isRoot := fun g {_ _} hz hw => D.isRoot g (fun h => hz (hS h)) hw
  act_one := fun {_ _} hz hw => D.act_one (fun h => hz (hS h)) hw
  act_mul := fun g h {_ _} hz hw => D.act_mul g h (fun h' => hz (hS h')) hw
  injOn := fun {_ _} hz hw => D.injOn (fun h => hz (hS h)) hw

theorem RationalDeck.act_mono (D : RationalDeck P S G) {S' : Finset ℂ}
    (hS : (S : Set ℂ) ⊆ (S' : Set ℂ)) : (D.mono hS).act = D.act := rfl

/-! ### The monodromy of the circle loop -/

/-- **The monodromy of the circle loop of a punctured disc**, as a permutation of the fibre of the
root cover above the basepoint of the disc. -/
def discCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {σ : ℂ} {ρ : ℝ}
    (hincl : puncturedDisc σ ρ ⊆ ((S : Set ℂ))ᶜ) (b : ↥(puncturedDisc σ ρ)) :
    Equiv.Perm ↥(puncturedProj P S ⁻¹' {subsetIncl hincl b}) :=
  (isCoveringMap_puncturedProj hP hS).monodromyHom (subsetIncl hincl b)
    (FundamentalGroup.map (subsetIncl hincl) b
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (discLoop σ b))))

/-- **The circle loop of a punctured disc has the monodromy order of any generator** of the
fundamental group of the disc: the two loops generate the same group, so their monodromies generate
the same group of permutations. -/
theorem orderOf_discCycle (hP : P.Monic) (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable) {σ : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ) (hincl : puncturedDisc σ ρ ⊆ ((S : Set ℂ))ᶜ) (b : ↥(puncturedDisc σ ρ))
    {g : FundamentalGroup ↥(puncturedDisc σ ρ) b} (hg : Subgroup.zpowers g = ⊤) :
    orderOf (discCycle hP hS hincl b)
      = orderOf ((isCoveringMap_puncturedProj hP hS).monodromyHom (subsetIncl hincl b)
          (FundamentalGroup.map (subsetIncl hincl) b g)) :=
  orderOf_map_eq_of_zpowers_eq_top
    (((isCoveringMap_puncturedProj hP hS).monodromyHom (subsetIncl hincl b)).comp
      (FundamentalGroup.map (subsetIncl hincl) b))
    (zpowers_discLoop_eq_top σ hρ b) hg

end Rigidity.RET.Analytic

end
