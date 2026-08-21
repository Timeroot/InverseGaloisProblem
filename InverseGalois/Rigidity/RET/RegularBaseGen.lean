/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.RegularBase
import InverseGalois.Rigidity.RET.Statement

/-!
# Regular Galois groups over an arbitrary base are closed under quotients

Closure under quotients does not depend on the base field being `ℚ`.  Over an arbitrary base
`F / k` the argument is the same: the fixed field of the kernel of the surjection is Galois over
`F` with the quotient group, and it is regular over `k` because a subextension of a regular
extension is regular — an element of the subextension that is algebraic over `k` stays algebraic
over `k` in the big extension, hence is already a constant there, and the inclusion is injective.

The only genuinely `ℚ`-flavoured ingredient of the `ℚ`-version is that a ring homomorphism between
fields of characteristic zero is automatically a `ℚ`-algebra homomorphism.  Over a general base
there is no such coincidence, but none is needed: the inclusion of an intermediate field is already
an `F`-algebra homomorphism, and restricting scalars along `k → F` makes it a `k`-algebra
homomorphism.  So the general statements need no hypotheses at all beyond those in the definition
of `IsRegularGaloisGroupOverBase`.

## Main results

* `Rigidity.RET.algebraicClosure_eq_bot_of_algHom` — regularity over `k` passes to a subfield
  along any `k`-algebra homomorphism.
* `IsRegularGaloisGroupOverBase.of_surjective`, `IsRegularGaloisGroupOverBase.quotient` — the class
  of regular Galois groups over a base `F / k` is closed under quotients.
* `IsRegularGaloisGroupOver.of_surjective`, `IsRegularGaloisGroupOver.quotient` — the same over the
  rational function field `K(T)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace Rigidity.RET

/-- **Having no constants beyond `k` passes to a subfield.**  A `k`-algebra homomorphism neither
creates nor destroys algebraicity over `k`, so an element of the source algebraic over `k` has an
image in the base `k`, and is itself in `k` because the homomorphism is injective and commutes with
the base. -/
theorem algebraicClosure_eq_bot_of_algHom {k E L : Type*} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L] (j : E →ₐ[k] L) (h : algebraicClosure k L = ⊥) :
    algebraicClosure k E = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hxL : j x ∈ algebraicClosure k L := (map_mem_algebraicClosure_iff j).mpr hx
  rw [h] at hxL
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hxL
  refine IntermediateField.mem_bot.mpr ⟨q, j.toRingHom.injective ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact hq

end Rigidity.RET

namespace IsRegularGaloisGroupOverBase

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {G Q : Type*} [Group G] [Group Q]

/-- **A quotient of a regular Galois group over `F / k` is a regular Galois group over `F / k`.**
The fixed field of the kernel is Galois over `F` with the quotient group, and it is regular over
`k` because it gains no constants that the big extension does not already have. -/
theorem of_surjective (hG : IsRegularGaloisGroupOverBase k F G) (φ : G →* Q)
    (hφ : Function.Surjective φ) : IsRegularGaloisGroupOverBase k F Q := by
  obtain ⟨L, hfield, halg, hfd, hgal, halgk, htower, hreg, ⟨e⟩⟩ := hG
  letI := hfield
  letI := halg
  letI := hfd
  letI := hgal
  letI := halgk
  letI := htower
  -- the composite surjection from the Galois group onto `Q`, and its kernel
  set ψ : (L ≃ₐ[F] L) →* Q := φ.comp e.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp e.surjective
  set N : Subgroup (L ≃ₐ[F] L) := ψ.ker
  haveI : N.Normal := ψ.normal_ker
  set E : IntermediateField F L := IntermediateField.fixedField N
  -- the fixed field is a regular extension: it gains no new constants
  have hregE : algebraicClosure k (↥E : Type) = ⊥ :=
    Rigidity.RET.algebraicClosure_eq_bot_of_algHom (E.val.restrictScalars k) hreg
  exact ⟨(↥E : Type), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hregE,
    ⟨(IsGalois.normalAutEquivQuotient N).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩

/-- **The quotient of a regular Galois group over `F / k` by a normal subgroup is a regular Galois
group over `F / k`.** -/
theorem quotient (hG : IsRegularGaloisGroupOverBase k F G) (N : Subgroup G) [N.Normal] :
    IsRegularGaloisGroupOverBase k F (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end IsRegularGaloisGroupOverBase

namespace IsRegularGaloisGroupOver

variable {K : Type*} [Field K] {G Q : Type*} [Group G] [Group Q]

/-- **A quotient of a regular Galois group over `K(T)` is a regular Galois group over `K(T)`.** -/
theorem of_surjective (hG : IsRegularGaloisGroupOver K G) (φ : G →* Q)
    (hφ : Function.Surjective φ) : IsRegularGaloisGroupOver K Q :=
  IsRegularGaloisGroupOverBase.of_surjective hG φ hφ

/-- **The quotient of a regular Galois group over `K(T)` by a normal subgroup is a regular Galois
group over `K(T)`.** -/
theorem quotient (hG : IsRegularGaloisGroupOver K G) (N : Subgroup G) [N.Normal] :
    IsRegularGaloisGroupOver K (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end IsRegularGaloisGroupOver

section Consistency

variable {G Q : Type*} [Group G] [Group Q]

/-- Consistency check: the base-general statement specializes to the one over `ℚ`. -/
example (hG : IsRegularInverseGalois G) (φ : G →* Q) (hφ : Function.Surjective φ) :
    IsRegularInverseGalois Q :=
  IsRegularGaloisGroupOver.of_surjective (K := ℚ) hG φ hφ

/-- Consistency check: the base-general quotient statement specializes to the one over `ℚ`. -/
example (hG : IsRegularInverseGalois G) (N : Subgroup G) [N.Normal] :
    IsRegularInverseGalois (G ⧸ N) :=
  IsRegularGaloisGroupOver.quotient (K := ℚ) hG N

end Consistency
