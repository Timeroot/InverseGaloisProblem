/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.CoverGalois

/-!
# The monodromy of the cover attached to a monodromy homomorphism is that homomorphism

The cover built from a system of labels is a covering space, so it has a monodromy in the sense of
`IsCoveringMap.monodromy`: the operation of lifting a path and reading off where the lift ends.
The explicit lift of `RET/Pi1/Topological/CoverLift.lean` computes it — the lift of a path from the
label transported along that path ends at the label itself — so the monodromy of the cover is
transport of labels, and on the fibre over the base point it is left translation by the value of
the homomorphism the cover was built from.

That closes the loop the construction was made for: a homomorphism from the fundamental group of a
region to a finite group is realized, as the monodromy of an honest covering space, whose deck
group is the group itself when the homomorphism is onto.

## Main results

* `Rigidity.RET.MonodromyData.monodromy_restrict` — the monodromy is transport of labels.
* `Rigidity.RET.MonodromyData.monodromy_apply` — on the fibre over the base point the monodromy of
  a loop is transport backwards along it.
* `Rigidity.RET.MonodromyData.fibEquiv_monodromy` — read on the group, that is left translation by
  the label of the loop.
* `Rigidity.RET.MonodromyData.fibEquiv_monodromy_ofHom` — for the cover named by a homomorphism out
  of the fundamental group, the translation is by the value of the homomorphism.
-/

open scoped unitInterval

noncomputable section

namespace Rigidity.RET.MonodromyData

variable {X : Set ℂ} {x₀ : ↥X} {H : Type*} [Group H] (D : MonodromyData x₀ H)

/-! ### The monodromy is transport of labels -/

/-- **The monodromy of the cover along a path is transport of labels along it.**  The explicit lift
is continuous, lies over the path and starts at the transported label, and lifts are unique. -/
theorem monodromy_restrict_path {a b : ↥X} (q : Path a b) (e : D.Fib b) :
    D.isCoveringMap_proj.monodromy (Path.Homotopic.Quotient.mk q)
        ⟨⟨a, D.restrict (Path.Homotopic.Quotient.mk q) e⟩, rfl⟩ = ⟨⟨b, e⟩, rfl⟩ := by
  obtain ⟨γ, hsrc, htgt⟩ := q
  subst hsrc
  subst htgt
  refine Subtype.ext ?_
  have hz : (toPath γ : C(I, ↥X)) 0
      = D.proj (⟨γ 0, D.restrict (Path.Homotopic.Quotient.mk (toPath γ)) e⟩ : D.Total) := rfl
  have hlift : D.isCoveringMap_proj.liftPath (toPath γ)
        (⟨γ 0, D.restrict (Path.Homotopic.Quotient.mk (toPath γ)) e⟩ : D.Total) hz
      = (⟨D.lift γ e, D.continuous_lift γ e⟩ : C(I, D.Total)) :=
    ((D.isCoveringMap_proj.eq_liftPath_iff' _).mpr ⟨funext fun _ => rfl, D.lift_zero γ e⟩).symm
  exact (congrArg (fun f : C(I, D.Total) => f 1) hlift).trans (D.lift_one γ e)

/-- **The monodromy of the cover along a homotopy class is transport of labels along it.** -/
theorem monodromy_restrict {a b : ↥X} (c : Path.Homotopic.Quotient a b) (e : D.Fib b) :
    D.isCoveringMap_proj.monodromy c ⟨⟨a, D.restrict c e⟩, rfl⟩ = ⟨⟨b, e⟩, rfl⟩ := by
  induction c using Quotient.inductionOn with
  | h q => exact D.monodromy_restrict_path q e

/-! ### The monodromy on the fibre over the base point -/

/-- **The monodromy of a loop on the fibre over the base point is transport backwards along it.** -/
theorem monodromy_apply (g : Path.Homotopic.Quotient x₀ x₀) (s : D.Fib x₀) :
    D.isCoveringMap_proj.monodromy g ⟨⟨x₀, s⟩, rfl⟩ = ⟨⟨x₀, D.restrict g.symm s⟩, rfl⟩ := by
  have h := D.monodromy_restrict g (D.restrict g.symm s)
  rwa [D.restrict_restrict, Path.Homotopic.Quotient.trans_symm, D.restrict_refl] at h

/-- **Read through the identification of the fibre over the base point with the group, the
monodromy of a loop is left translation by the inverse of its label.** -/
theorem fibEquiv_monodromy (g : Path.Homotopic.Quotient x₀ x₀) (s : D.Fib x₀) :
    D.fibEquiv (Path.Homotopic.Quotient.refl x₀) (D.restrict g.symm s)
      = (D.toFun g)⁻¹ * D.fibEquiv (Path.Homotopic.Quotient.refl x₀) s := by
  rw [D.fibEquiv_restrict, D.map_symm]

/-- **The monodromy of the cover named by a homomorphism out of the fundamental group is that
homomorphism**, acting on the fibre over the base point by left translation. -/
theorem fibEquiv_monodromy_ofHom (hX : IsOpen X) (φ : FundamentalGroup ↥X x₀ →* H)
    (g : Path.Homotopic.Quotient x₀ x₀) (s : (ofHom hX φ).Fib x₀) :
    (ofHom hX φ).fibEquiv (Path.Homotopic.Quotient.refl x₀) ((ofHom hX φ).restrict g.symm s)
      = φ (FundamentalGroup.fromPath g)
        * (ofHom hX φ).fibEquiv (Path.Homotopic.Quotient.refl x₀) s := by
  rw [fibEquiv_monodromy, toFun_ofHom, inv_inv]

end Rigidity.RET.MonodromyData

end
