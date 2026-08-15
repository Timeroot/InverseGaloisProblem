/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Rigidity.RET.Pi1.Topological.GroupLoop

/-!
# The power map at an arbitrary basepoint

The `n`-th power map of a topological group raises a loop *based at the unit* to its `n`-th power.
At another basepoint there is no such formula, because a loop based at `b` is not a loop based at
the unit; but translation carries one basepoint to the other, and translation commutes with the
power map when the group is commutative.  What survives is exactly what a degree computation needs:
the image of any loop under the `n`-th power map is an `n`-th power.

## Main definitions

* `Rigidity.RET.mulRightMap` — translation of a topological group, as a continuous map.
* `Rigidity.RET.transHom` — translation of a loop based at the unit.

## Main results

* `Rigidity.RET.surjective_transHom` — every loop is a translate of a loop at the unit.
* `Rigidity.RET.map_npowMap_transHom` — the power map turns a translated loop into the translate of
  a power.
* `Rigidity.RET.exists_eq_pow_map_npowMap` — the `n`-th power map sends every loop to an `n`-th
  power.
-/

noncomputable section

namespace Rigidity.RET

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [ContinuousMul G]

/-! ### Translation -/

/-- **Translation** of a topological group, as a continuous map. -/
def mulRightMap (b : G) : C(G, G) := ⟨fun x => x * b, continuous_id.mul continuous_const⟩

@[simp] theorem mulRightMap_apply (b x : G) : mulRightMap b x = x * b := rfl

/-- **Translating a loop based at the unit** to a loop based at `c`. -/
def transHom (c : G) : FundamentalGroup G 1 →* FundamentalGroup G c :=
  FundamentalGroup.mapOfEq (mulRightMap c) (one_mul c)

theorem transHom_fromPath (c : G) (β : Path (1 : G) 1) :
    transHom c (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β))
      = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((β.map (mulRightMap c).continuous).cast (one_mul c).symm (one_mul c).symm)) :=
  FundamentalGroup.mapOfEq_apply _ _ β

/-! ### Every loop is a translate -/

/-- The translate of a loop back to the unit. -/
def untranslate (b : G) (α : Path b b) : Path (1 : G) 1 :=
  (α.map (mulRightMap b⁻¹).continuous).cast (mul_inv_cancel b).symm (mul_inv_cancel b).symm

@[simp] theorem untranslate_apply (b : G) (α : Path b b) (t : unitInterval) :
    untranslate b α t = α t * b⁻¹ := rfl

/-- **Every loop is the translate of a loop based at the unit.** -/
theorem surjective_transHom (c : G) : Function.Surjective (transHom c) := by
  intro γ
  induction γ using Quotient.inductionOn with
  | h α =>
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (untranslate c α)), ?_⟩
    rw [transHom_fromPath]
    exact congrArg (fun p : Path c c => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
      (Path.ext (funext fun t => inv_mul_cancel_right (α t) c))

/-! ### The power map on a translated loop -/

/-- **The power map turns a translated loop into the translate of a power.** -/
theorem map_npowMap_transHom (n : ℕ) (b : G) (γ : FundamentalGroup G 1) :
    FundamentalGroup.map (npowMap G n) b (transHom b γ) = transHom (b ^ n) (γ ^ n) := by
  induction γ using Quotient.inductionOn with
  | h β =>
    show FundamentalGroup.map (npowMap G n) b
        (transHom b (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))
      = transHom (b ^ n) (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β) ^ n)
    rw [transHom_fromPath, ← fromPath_loopPow, transHom_fromPath]
    refine congrArg
      (fun p : Path (b ^ n) (b ^ n) =>
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) ?_
    exact Path.ext (funext fun t => mul_pow (β t) b n)

/-- **The `n`-th power map of a commutative topological group sends every loop to an `n`-th
power.** -/
theorem exists_eq_pow_map_npowMap (n : ℕ) (b : G) (γ : FundamentalGroup G b) :
    ∃ t : FundamentalGroup G (b ^ n), FundamentalGroup.map (npowMap G n) b γ = t ^ n := by
  obtain ⟨γ', rfl⟩ := surjective_transHom b γ
  exact ⟨transHom (b ^ n) γ', by rw [map_npowMap_transHom, map_pow]⟩

end Rigidity.RET

end
