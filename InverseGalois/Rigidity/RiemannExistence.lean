/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Hilbert.RegularExtension
import InverseGalois.Rigidity.Certificate

/-!
# The Riemann Existence Theorem for rigidity (the analytic bridge, as an axiom)

The classical rigidity method turns a **rigid rational generating tuple** for a centerless finite
group into an actual *regular* Galois extension of `ℚ(T)`.  The mechanism is the **Riemann
Existence Theorem** (RET) together with the **branch cycle argument** descending the field of
definition to `ℚ`.  Neither RET nor the theory of covers of curves / étale `π₁` exists in Mathlib,
and building them is out of scope, so this single analytic step is isolated here as a labelled
**axiom** `riemann_existence_ax`.

Concretely the axiom asserts exactly the hypothesis bundle consumed by
`IsInverseGalois.of_regular_family` for the regular permutation image `H = φ.range` of `G`: a monic
`ℚ(T)`-family `F`, an absolutely irreducible resolvent `G`, finiteness of bad specializations, and
the per-specialization landing / root certificates.  The remaining descent `ℚ(T) → ℚ` is the
**proven** Hilbert-irreducibility content of `of_regular_family`; it is *not* part of the axiom.

## Development workflow

The ATP MCP tooling cannot reason about nonstandard axioms, so during active development the
wrapper `theorem riemann_existence` is left as `sorry` (this file's only `sorry`).  Flipping it to
the labelled axiom is a **one-line change** (see the comment on `riemann_existence`); do so before
running `#print axioms` to confirm the axiom profile.

## Main statements

* `Rigidity.cayley` / `Rigidity.cayley_injective` — the faithful regular (Cayley) representation
  `G ↪ Equiv.Perm (Fin (Nat.card G))`.
* `Rigidity.riemann_existence_ax` — the RET axiom (the analytic bridge).
* `Rigidity.riemann_existence` — the wrapper routed through by `rigidity_realizable`.
-/

open Polynomial

noncomputable section

namespace Rigidity

variable {G : Type*} [Group G] [Finite G]

/-- A chosen bijection `G ≃ Fin (Nat.card G)`, used to model the regular representation inside
`Equiv.Perm (Fin (Nat.card G))`. -/
def eFin (G : Type*) [Finite G] : G ≃ Fin (Nat.card G) := Finite.equivFin G

/-- The **regular (Cayley) representation** of `G` as permutations of `Fin (Nat.card G)`: the
left-multiplication action of `G` on itself, transported along `eFin`. -/
def cayley (G : Type*) [Group G] [Finite G] : G →* Equiv.Perm (Fin (Nat.card G)) :=
  (Equiv.permCongrHom (eFin G)).toMonoidHom.comp (MulAction.toPermHom G G)

/-- The regular representation is faithful. -/
theorem cayley_injective : Function.Injective (cayley G) := by
  rw [cayley, MonoidHom.coe_comp]
  refine (Equiv.permCongrHom (eFin G)).injective.comp ?_
  rw [MulAction.coe_toPermHom]
  exact MulAction.toPerm_injective

/-- **The Riemann Existence Theorem for rigidity (axiom).**

Given a rigidity certificate for a finite group `G` and a faithful permutation representation
`φ : G ↪ Equiv.Perm (Fin n)`, there exists a *regular resolvent family* over `ℚ(T)` for the image
`H = φ.range` — i.e. exactly the hypothesis bundle of `IsInverseGalois.of_regular_family`.

This encapsulates the geometric cover-existence (RET) and the branch cycle rationality descent to
`ℚ(T)`; the further Hilbert descent `ℚ(T) → ℚ` is the *proven* content of `of_regular_family` and
is deliberately **not** bundled here. -/
axiom riemann_existence_ax
    {G : Type*} [Group G] [Finite G] (cert : RigidityCertificate G)
    {n : ℕ} (φ : G →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) :
    ∃ (F Gp : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧
      Gp.Monic ∧ Gp.natDegree = Nat.card φ.range ∧
      Irreducible Gp ∧
      Irreducible (Gp.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, (specialize F t).Separable →
          ∃ g' : (specialize F t).Gal →* φ.range, Function.Injective g') ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize Gp t) = 0)

/-- Wrapper restating `riemann_existence_ax`.  **Everything downstream goes through this theorem.**

DEVELOPMENT FORM (current): the body is `sorry`, because the ATP MCP tooling cannot handle
nonstandard axioms while iterating.

FINAL FORM (for the axiom audit): replace the body with
`riemann_existence_ax cert φ hφ`
and run `#print axioms Rigidity.rigidity_realizable` — it should report `riemann_existence_ax`
alongside `propext`, `Classical.choice`, `Quot.sound` (and no `sorryAx`). -/
theorem riemann_existence {G : Type*} [Group G] [Finite G] (cert : RigidityCertificate G)
    {n : ℕ} (φ : G →* Equiv.Perm (Fin n)) (hφ : Function.Injective φ) :
    ∃ (F Gp : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧
      Gp.Monic ∧ Gp.natDegree = Nat.card φ.range ∧
      Irreducible Gp ∧
      Irreducible (Gp.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, (specialize F t).Separable →
          ∃ g' : (specialize F t).Gal →* φ.range, Function.Injective g') ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize Gp t) = 0) :=
  sorry -- FINAL: `riemann_existence_ax cert φ hφ`

end Rigidity

end
