/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.Monodromy

/-!
# Naturality of the monodromy representation

A map of coverings is a pair of continuous maps, one of total spaces and one of bases, commuting
with the two projections.  Lifting a path along the first covering and then pushing the lift
forward produces a lift of the pushed path along the second covering, so by uniqueness of path
lifting the two monodromy actions agree: monodromy is natural.

The case that matters here is the restriction of a covering to a smaller base: the fibres are
unchanged, so the two monodromy representations differ only by relabelling, and if the induced map
of fundamental groups is surjective the two monodromy groups coincide.

## Main results

* `Rigidity.RET.monodromy_naturality` — monodromy commutes with a map of coverings.
* `Rigidity.RET.monodromyHom_naturality` — the same statement for the vertex-group
  representation.
-/

open CategoryTheory Topology unitInterval

noncomputable section

namespace Rigidity.RET

variable {E X E' X' : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace E'] [TopologicalSpace X'] {p : E → X} {p' : E' → X'}

/-- **Monodromy is natural in maps of coverings.**  For continuous maps `F` of total spaces and
`f` of bases with `p' ∘ F = f ∘ p`, the lift of a path along the first covering, pushed forward by
`F`, is the lift of the pushed path along the second covering. -/
theorem monodromy_naturality (cov : IsCoveringMap p) (cov' : IsCoveringMap p') (f : C(X, X'))
    (F : C(E, E')) (hcomm : ∀ e, p' (F e) = f (p e)) {x y : X}
    (q : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x})
    (he : F e.1 ∈ p' ⁻¹' {f x}) :
    (cov'.monodromy (q.map f) ⟨F e.1, he⟩ : E') = F (cov.monodromy q e : E) := by
  obtain ⟨Q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  rw [← Path.Homotopic.Quotient.mk_map, cov.monodromy_mk_val, cov'.monodromy_mk_val]
  have hcomp : F.comp (cov.liftPath Q e.1 (Q.source.trans e.2.symm))
      = cov'.liftPath (Q.map f.continuous) (F e.1)
        ((Q.map f.continuous).source.trans he.symm) := by
    rw [cov'.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t
      show p' (F (cov.liftPath Q e.1 (Q.source.trans e.2.symm) t)) = f (Q t)
      rw [hcomm]
      exact congrArg f (congr_fun (cov.liftPath_lifts Q e.1 (Q.source.trans e.2.symm)) t)
    · show F (cov.liftPath Q e.1 (Q.source.trans e.2.symm) 0) = F e.1
      rw [cov.liftPath_zero]
  rw [← hcomp]
  rfl

/-- The class of a loop pushed forward along a continuous map is the pushed-forward class. -/
theorem toPath_fundamentalGroup_map (f : C(X, X')) (x : X) (γ : FundamentalGroup X x) :
    (FundamentalGroup.map f x γ).toPath = γ.toPath.map f := rfl

/-- **Naturality of the monodromy representation of the fundamental group.** -/
theorem monodromyHom_naturality (cov : IsCoveringMap p) (cov' : IsCoveringMap p') (f : C(X, X'))
    (F : C(E, E')) (hcomm : ∀ e, p' (F e) = f (p e)) {x : X} (γ : FundamentalGroup X x)
    (e : p ⁻¹' {x}) (he : F e.1 ∈ p' ⁻¹' {f x}) :
    (cov'.monodromyHom (f x) (FundamentalGroup.map f x γ) ⟨F e.1, he⟩ : E')
      = F (cov.monodromyHom x γ e : E) :=
  monodromy_naturality cov cov' f F hcomm γ.toPath e he

end Rigidity.RET

end
