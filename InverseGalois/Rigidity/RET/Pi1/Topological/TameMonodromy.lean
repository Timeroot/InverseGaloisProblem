/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.CircleGroup
import InverseGalois.Rigidity.RET.Pi1.Topological.TameCover

/-!
# The tame cyclic monodromy: `ℤ` acts transitively on the degree-`n` fibre

Combining the two topological bricks — `π₁(ℂˣ) ≅ ℤ` (`CircleGroup.lean`) and the degree-`n` power
cover `z ↦ zⁿ` (`TameCover.lean`) — gives the monodromy of the tame cover as an action of the
infinite cyclic group `π₁(ℂˣ) ≅ ℤ` on the `n`-element fibre.  Transporting the fundamental group to
the base cover's basepoint `e₀ⁿ` (both live in the path-connected `ℂˣ`), the monodromy becomes a
homomorphism

* `Complex.npowMonodromyInt : Multiplicative ℤ →* Equiv.Perm ((z ↦ zⁿ) ⁻¹' {e₀ⁿ})`,

and this `ℤ`-action is **transitive** on the fibre (`npowMonodromyInt_orbit_surjective`), which has
exactly `n` points (`npow_fibre_card`).  So a generator of `π₁(ℂˣ) ≅ ℤ` maps to an `n`-cycle: the
tame monodromy is the cyclic reduction `ℤ ↠ ℤ/n ≅ μₙ`.  This is the topological realization of the
cyclicity of tame inertia used in the branch-cycle description of `π₁` (link **C** of
`GAGA_DREAM.md`).
-/

open Topology

namespace Complex

/-- The monodromy of the degree-`n` tame cover `z ↦ zⁿ`, expressed as an action of the infinite
cyclic group `π₁(ℂˣ) ≅ ℤ` on the fibre over `e₀ⁿ`.  It is the composite of the basepoint transport
`Multiplicative ℤ ≃ π₁(ℂˣ, exp 0) ≃ π₁(ℂˣ, e₀ⁿ)` with the monodromy representation. -/
noncomputable def npowMonodromyInt (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Multiplicative ℤ →* Equiv.Perm ((fun z : ℂˣ ↦ z ^ n) ⁻¹' {e₀ ^ n}) :=
  ((npowCover n).monodromyHom (e₀ ^ n)).comp
    (((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
          Complex.expUnit (e₀ ^ n)).toMonoidHom).comp
      fundamentalGroupUnits.symm.toMonoidHom)

/-- **Tame monodromy is transitive.**  The `ℤ`-action `npowMonodromyInt` on the degree-`n` fibre is
transitive: starting from the fibre point `e₀`, every point of the fibre is reached by some power of
the monodromy generator.  (The cover `ℂˣ → ℂˣ` is connected because `ℂˣ` is path connected.) -/
theorem npowMonodromyInt_orbit_surjective (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Function.Surjective (fun k : Multiplicative ℤ => npowMonodromyInt n e₀ k ⟨e₀, rfl⟩) := by
  have hφ : Function.Surjective (fun k : Multiplicative ℤ =>
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected Complex.expUnit (e₀ ^ n))
        (fundamentalGroupUnits.symm k)) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
        Complex.expUnit (e₀ ^ n)).surjective.comp fundamentalGroupUnits.symm.surjective
  have ho := (npowCover n).orbitMap_surjective (e₀ ^ n) ⟨e₀, rfl⟩
  have hcomp : (fun k : Multiplicative ℤ => npowMonodromyInt n e₀ k ⟨e₀, rfl⟩)
      = (npowCover n).orbitMap (e₀ ^ n) ⟨e₀, rfl⟩ ∘
          (fun k : Multiplicative ℤ =>
            (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected Complex.expUnit (e₀ ^ n))
              (fundamentalGroupUnits.symm k)) := rfl
  rw [hcomp]
  exact ho.comp hφ

/-- **The tame monodromy realizes `ℤ` acting transitively on `n` points.**  The `ℤ`-monodromy of the
degree-`n` tame cover acts transitively (from `e₀`) on the fibre over `e₀ⁿ`, and that fibre has
exactly `n` elements.  Together: the cyclic group `π₁(ℂˣ) ≅ ℤ` surjects onto a transitive action on
an `n`-element set — the generator is an `n`-cycle, i.e. tame inertia of order `n`. -/
theorem npow_tame_monodromy (n : ℕ) [NeZero n] (e₀ : ℂˣ) :
    Function.Surjective (fun k : Multiplicative ℤ => npowMonodromyInt n e₀ k ⟨e₀, rfl⟩) ∧
      Nat.card ((fun z : ℂˣ ↦ z ^ n) ⁻¹' {e₀ ^ n}) = n :=
  ⟨npowMonodromyInt_orbit_surjective n e₀, npow_fibre_card n e₀⟩

end Complex
