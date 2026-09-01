/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.InvariantMap
import InverseGalois.CFT.Brauer.LocalInvariantRestrict

/-!
# The invariant map under base change to an unramified extension

Let `M / K` be a finite unramified extension of local fields whose absolute value and normalised
valuation extend those of `K`.  The invariant of a Brauer class over `K` computed over `M` is then
`[M : K]` times the invariant computed over `K`:

`inv_M (res_M x) = [M : K] · inv_K x`.

The invariant map computes the normalised invariant in any unramified splitting field, and two
unramified extensions of `K` inside a fixed algebraic closure have an unramified compositum.  So a
splitting field of the class can be enlarged until it contains a copy of `M`, at which point the
class is split by one and the same extension over `K` and over `M`, and the normalised statement
`InverseGalois.CFT.localInvariant_baseChange` applies to it.

## Main results

* `InverseGalois.CFT.localInvariantHom_baseChange_of_unramified`: **the invariant of a Brauer class
  is multiplied by the degree under base change to a finite unramified extension.**

## Tags

Brauer group, local field, unramified extension, invariant map, base change, class field theory
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 400000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

variable {K M : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K]
variable [Field M] [Valued M ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation M ℤᵐ⁰)] [CompleteSpace M] [ProperSpace M]
variable [Algebra K M] [FiniteDimensional K M] {mK mM : ℤ}

/-- **The invariant of a Brauer class is multiplied by the degree under base change to a finite
unramified extension.**  Enlarging an unramified splitting field of the class by a copy of the
extension makes the two invariants comparable, and the normalised statement then says that the
Frobenius normalisation upstairs is the `[M : K]`-th power of the one downstairs. -/
theorem localInvariantHom_baseChange_of_unramified
    (hnorm : ∀ x : K, ‖algebraMap K M x‖ = ‖x‖)
    (hurM : ∀ z : M, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K M z = ‖c‖)
    (hmK : IsUnitValGen K mK) (hmM : IsUnitValGen M mM)
    (hval : ∀ a : Kˣ,
      unitValDiv hmM (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom a))
        = unitValDiv hmK (Additive.ofMul a))
    (x : BrauerGroup.{0, 0} K) :
    localInvariantHom M hmM (BrauerGroup.baseChangeHom M x)
      = localInvariantHom K hmK x ^ finrank K M := by
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M
  obtain ⟨φ⟩ : Nonempty (M →ₐ[K] AlgebraicClosure K) := ⟨IsAlgClosed.lift⟩
  let e : M ≃ₐ[K] ↥φ.fieldRange := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional K ↥φ.fieldRange := e.toLinearEquiv.finiteDimensional
  let G : UnramifiedSubfield K := ⟨φ.fieldRange, inferInstance, unramified_of_algEquiv e hurM⟩
  obtain ⟨F₀, hF₀⟩ := exists_unramifiedSubfield_mem_relative K x
  let F : UnramifiedSubfield K := F₀.sup G
  have hxF : x ∈ BrauerGroup.relative K ↥F.carrier :=
    BrauerGroup.relative_mono (le_sup_left : F₀.carrier ≤ F₀.carrier ⊔ G.carrier) hF₀
  let ψ : M →ₐ[K] ↥F.carrier :=
    (IntermediateField.inclusion (le_sup_right : G.carrier ≤ F₀.carrier ⊔ G.carrier)).comp
      (e : M →ₐ[K] ↥φ.fieldRange)
  letI : Algebra M ↥F.carrier := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower K M ↥F.carrier :=
    IsScalarTower.of_algebraMap_eq fun y => (ψ.commutes y).symm
  haveI : FiniteDimensional M ↥F.carrier := FiniteDimensional.right K M ↥F.carrier
  haveI : IsGalois M ↥F.carrier :=
    isGalois_of_unramified M ↥F.carrier (unramified_base hnorm F.unramified)
  have h1 : localInvariantHom K hmK x = localInvariant K ↥F.carrier F.unramified hmK ⟨x, hxF⟩ :=
    localInvariantHom_apply_of_unramified hmK F.unramified ⟨x, hxF⟩
  have h2 : localInvariantHom M hmM (BrauerGroup.baseChangeHom M x)
      = localInvariant M ↥F.carrier (unramified_base hnorm F.unramified) hmM
          ⟨BrauerGroup.baseChangeHom M x, baseChangeHom_mem_relative M hxF⟩ :=
    localInvariantHom_apply_of_unramified hmM (unramified_base hnorm F.unramified)
      ⟨BrauerGroup.baseChangeHom M x, baseChangeHom_mem_relative M hxF⟩
  rw [h1, h2]
  exact localInvariant_baseChange hnorm F.unramified hmK hmM hval ⟨x, hxF⟩

end InverseGalois.CFT
