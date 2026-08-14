/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.InstanceShortcuts
import InverseGalois.Rigidity.RET.RegularBase
import InverseGalois.Rigidity.RET.Statement

/-!
# Regular inverse Galois groups are closed under quotients

A subextension of a regular extension is regular: an element of the subextension that is algebraic
over `ℚ` is algebraic over `ℚ` in the big extension, hence already a constant, and a constant of
the big extension lying in the subextension is a constant of the subextension.  Combined with the
fundamental theorem of Galois theory — the fixed field of a normal subgroup is Galois with the
quotient group — this makes the class of regular inverse Galois groups closed under quotients,
exactly as the class of inverse Galois groups over `ℚ` is.

## Main results

* `IsRegularInverseGalois.of_surjective` — a quotient of a regular inverse Galois group is one.
* `IsRegularInverseGalois.quotient` — the same, phrased for a quotient by a normal subgroup.
-/

open Polynomial IntermediateField

noncomputable section

namespace IsRegularInverseGalois

variable {G Q : Type*} [Group G] [Group Q]

set_option synthInstance.maxHeartbeats 400000 in
/-- **A quotient of a regular inverse Galois group is a regular inverse Galois group.**  The fixed
field of the kernel is Galois over `ℚ(T)` with the quotient group, and it is regular because it
gains no constants that the big extension does not already have. -/
theorem of_surjective (hG : IsRegularInverseGalois G) (φ : G →* Q)
    (hφ : Function.Surjective φ) : IsRegularInverseGalois Q := by
  obtain ⟨L, hfield, halg, hfd, hgal, halgQ, htower, hreg, ⟨e⟩⟩ := hG
  letI := hfield
  letI := halg
  letI := hfd
  letI := hgal
  letI := halgQ
  letI := htower
  -- the composite surjection from the Galois group onto `Q`, and its kernel
  set ψ : (L ≃ₐ[RatFunc ℚ] L) →* Q := φ.comp e.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp e.surjective
  set N : Subgroup (L ≃ₐ[RatFunc ℚ] L) := ψ.ker
  haveI : N.Normal := ψ.normal_ker
  set E : IntermediateField (RatFunc ℚ) L := IntermediateField.fixedField N
  -- the rational structure on the fixed field is compatible with the one on the big field
  haveI towerE : IsScalarTower ℚ (RatFunc ℚ) (↥E : Type) := by
    refine ⟨fun x y z => Subtype.ext ?_⟩
    push_cast
    have h := htower.smul_assoc x y (z : L)
    rw [Algebra.smul_def x (y • (z : L)), eq_ratCast (algebraMap ℚ L) x,
      ← Rat.smul_def x (y • (z : L))] at h
    exact h
  -- the fixed field is a regular extension: it gains no new constants
  have hregE : algebraicClosure ℚ (↥E : Type) = ⊥ :=
    Rigidity.RET.algebraicClosure_eq_bot_of_ringHom (E.val : (↥E : Type) →+* L) hreg
  exact ⟨(↥E : Type), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    towerE, hregE,
    ⟨(IsGalois.normalAutEquivQuotient N).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩

/-- **The quotient of a regular inverse Galois group by a normal subgroup is a regular inverse
Galois group.** -/
theorem quotient (hG : IsRegularInverseGalois G) (N : Subgroup G) [N.Normal] :
    IsRegularInverseGalois (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end IsRegularInverseGalois
