/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts

/-!
# Constants of a function field

Two facts about the field of constants of an extension, both prior to any Galois theory.

A rational function algebraic over the field of constants is a constant: an element of `K(T)`
integral over `K` is in particular integral over `K[T]`, and the polynomial ring is integrally
closed in its fraction field, so the element is a polynomial; a polynomial that satisfies a nonzero
equation over `K` composes into that equation to give zero, which for a nonzero outer polynomial
forces the inner one to be constant.  So `K(T) / K` is a regular extension — the base of the whole
regular tower.

Regularity also descends along an arbitrary embedding of fields of characteristic zero: over `ℚ` a
ring homomorphism is automatically a `ℚ`-algebra homomorphism, and an element algebraic over `ℚ`
has an algebraic image, so a subfield of a field without constants has no constants either.

## Main results

* `Rigidity.RET.algebraicClosure_ratFunc_eq_bot` — the constants of `K(T)` are exactly `K`.
* `Rigidity.RET.algebraicClosure_eq_bot_of_ringHom` — regularity over `ℚ` passes to subfields.
-/

open Polynomial

noncomputable section

namespace Rigidity.RET

/-- **A rational function algebraic over the constants is a constant.**  Being integral over `K` it
is integral over `K[T]`, hence a polynomial because `K[T]` is integrally closed in `K(T)`; and a
polynomial satisfying a nonzero equation over `K` composes into it to give zero, which forces the
polynomial to have degree zero. -/
theorem algebraicClosure_ratFunc_eq_bot (K : Type*) [Field K] :
    algebraicClosure K (RatFunc K) = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hint : IsIntegral K x := mem_algebraicClosure_iff'.mp hx
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hint.tower_top (A := Polynomial K))
  have hpint : IsIntegral K p :=
    (isIntegral_algebraMap_iff
      (IsFractionRing.injective (Polynomial K) (RatFunc K))).mp (hp ▸ hint)
  obtain ⟨q, hqmonic, hq⟩ := hpint
  have hcomp : q.comp p = 0 := by
    simpa [Polynomial.comp, Polynomial.algebraMap_eq] using hq
  rcases Polynomial.comp_eq_zero_iff.mp hcomp with h | ⟨-, hpc⟩
  · exact absurd h hqmonic.ne_zero
  · refine IntermediateField.mem_bot.mpr ⟨p.coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K), Polynomial.algebraMap_eq,
      ← hpc]
    exact hp

/-- **Having no constants beyond `ℚ` passes to a subfield.**  A ring homomorphism between fields of
characteristic zero is automatically a `ℚ`-algebra homomorphism, so it neither creates nor destroys
algebraicity over `ℚ`; an element of the source algebraic over `ℚ` therefore has a rational image,
and is rational itself because the homomorphism is injective and commutes with the rationals. -/
theorem algebraicClosure_eq_bot_of_ringHom {E L : Type*} [Field E] [Field L] [Algebra ℚ E]
    [Algebra ℚ L] (i : E →+* L) (h : algebraicClosure ℚ L = ⊥) : algebraicClosure ℚ E = ⊥ := by
  set j : E →ₐ[ℚ] L := i.toRatAlgHom
  refine le_antisymm (fun x hx => ?_) bot_le
  have hxL : j x ∈ algebraicClosure ℚ L := (map_mem_algebraicClosure_iff j).mpr hx
  rw [h] at hxL
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hxL
  refine IntermediateField.mem_bot.mpr ⟨q, ?_⟩
  refine j.toRingHom.injective ?_
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact hq

end Rigidity.RET
