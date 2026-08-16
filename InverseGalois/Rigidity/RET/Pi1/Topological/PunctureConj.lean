/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Pi1.Topological.PunctureFill

/-!
# Conjugating a loop around a puncture

Dragging a loop along a path back to the same basepoint conjugates it, so a loop winding once
around a puncture stays one after conjugation by any loop: the path chosen to reach the puncture is
part of the datum of winding around it, and it may be prefixed by any loop at the basepoint.

That freedom is what makes the loops around the punctures usable in any prescribed order — the
ordered product of a system of puncture loops depends on the order, but only up to conjugacy of the
individual factors.

## Main results

* `Rigidity.RET.fundamentalGroupMulEquivOfPath_loop` — transport along a loop is conjugation by it.
* `Rigidity.RET.IsPunctureLoop.conj` — winding around a point survives conjugation.
-/

noncomputable section

namespace Rigidity.RET

/-- **Dragging a loop along another loop conjugates it.** -/
theorem fundamentalGroupMulEquivOfPath_loop {X : Type*} [TopologicalSpace X] {x₀ : X}
    (ε : Path x₀ x₀) (γ : FundamentalGroup X x₀) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath ε γ
      = FundamentalGroup.fromPath ⟦ε⟧ * γ * (FundamentalGroup.fromPath ⟦ε⟧)⁻¹ := rfl

/-- **Winding once around a point survives conjugation.**  The loop reaching the puncture may be
prefixed by any loop at the basepoint. -/
theorem IsPunctureLoop.conj {X : Set ℂ} {s z₀ : ℂ} {hz₀ : z₀ ∈ X}
    (w : FundamentalGroup ↥X ⟨z₀, hz₀⟩) {γ : FundamentalGroup ↥X ⟨z₀, hz₀⟩}
    (hγ : IsPunctureLoop X s hz₀ γ) : IsPunctureLoop X s hz₀ (w * γ * w⁻¹) := by
  obtain ⟨ε, hε⟩ := Quotient.exists_rep (FundamentalGroup.toPath w)
  have hw : FundamentalGroup.fromPath ⟦ε⟧ = w := hε
  have := hγ.transport ε
  rwa [fundamentalGroupMulEquivOfPath_loop, hw] at this

end Rigidity.RET

end
