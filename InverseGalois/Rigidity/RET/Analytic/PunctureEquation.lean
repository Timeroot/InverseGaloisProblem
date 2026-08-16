/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.CoverEquation
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverOrdered

/-!
# Functions on the cover realizing a prescribed monodromy are algebraic over the plane

The cover of the punctured plane built from a generating product-one tuple is a covering map onto
an open region, connected, with the deck group acting simply transitively on every fibre.  Those
are exactly the hypotheses under which a holomorphic function on a space over the plane satisfies a
monic equation with analytic coefficients, so the two halves fit together: the cover realizing a
prescribed branch-cycle system carries, for each holomorphic function on it, an equation of degree
the order of the group over the analytic functions of the punctured plane.

## Main results

* `Rigidity.RET.exists_cover_monic_analytic_of_prodOne_ordered` — the cover with prescribed
  monodromy, together with the equation satisfied on it by an arbitrary holomorphic function.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET

/-- **The cover realizing a prescribed branch-cycle system makes every holomorphic function on it
algebraic over the punctured plane.**

The cover is the one produced by `Rigidity.RET.exists_cover_of_prodOne_ordered` — connected, with
monodromy `h i` around the prescribed puncture `pt i` and trivial monodromy at infinity — and the
final clause says that a holomorphic function on its total space satisfies a monic equation of
degree the order of the group whose coefficients are analytic on the punctured plane. -/
theorem exists_cover_monic_analytic_of_prodOne_ordered (S : Finset ℂ) {z₀ : ℂ}
    (hz₀ : z₀ ∈ ((S : Set ℂ))ᶜ) (pt : Fin S.card → ℂ) (hrange : Set.range pt = (S : Set ℂ))
    {H : Type} [Group H] [Fintype H] (h : Fin S.card → H)
    (hprod : (List.ofFn h).prod = 1) (hgen : Subgroup.closure (Set.range h) = ⊤) :
    ∃ (δ : Fin S.card → FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (loopInf : FundamentalGroup ↥((S : Set ℂ))ᶜ ⟨z₀, hz₀⟩)
      (D : MonodromyData (X := ((S : Set ℂ))ᶜ) ⟨z₀, hz₀⟩ H),
      (∀ i : Fin S.card, IsPunctureLoop ((S : Set ℂ))ᶜ (pt i) hz₀ (δ i)) ∧
        IsSupportedAtInfinity ((S : Set ℂ))ᶜ hz₀ loopInf ∧
        IsCoveringMap D.proj ∧ PathConnectedSpace D.Total ∧
        Function.Injective D.deckHom ∧
        (∀ (i : Fin S.card) (s : D.Fib ⟨z₀, hz₀⟩),
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath (δ i)) (D.basePoint s)
            = D.basePoint ((D.fibEquiv (Path.Homotopic.Quotient.refl _)).symm
                (h i * D.fibEquiv (Path.Homotopic.Quotient.refl _) s))) ∧
        (∀ s : D.Fib ⟨z₀, hz₀⟩,
          D.isCoveringMap_proj.monodromy (FundamentalGroup.toPath loopInf) (D.basePoint s)
            = D.basePoint s) ∧
        ∀ g : D.Total → ℂ, IsHolo D.projC g →
          ∃ c : ℕ → ℂ → ℂ, (∀ k y, AnalyticAt ℂ (c k) (D.projC y)) ∧
            ∀ y, g y ^ Fintype.card H
              + ∑ k ∈ Finset.range (Fintype.card H), c k (D.projC y) * g y ^ k = 0 := by
  obtain ⟨δ, loopInf, D, hloop, hinf, hcov, hconn, hinj, htrans, hmon, hmoninf⟩ :=
    exists_cover_of_prodOne_ordered S hz₀ pt hrange h hprod hgen
  refine ⟨δ, loopInf, D, hloop, hinf, hcov, hconn, hinj, hmon, hmoninf, fun g hg => ?_⟩
  exact D.exists_monic_analytic_of_isHolo (S.finite_toSet.isClosed).isOpen_compl hcov htrans hg

end Rigidity.RET

end
