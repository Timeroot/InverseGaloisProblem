/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralTwist
import InverseGalois.CFT.RestrictLE

/-!
# Twisting a solution of an embedding problem by a character of an auxiliary field

A solution of a central Frattini embedding problem over a Galois extension `E` of the rationals may
be corrected by a character of an auxiliary Galois extension `F` with values in the kernel: on a
Galois extension `L` containing both, the pointwise product of the inflation of the solution with
the inflation of the character is again a solution.  It lifts the same map on the base field,
because the character takes values in the kernel, and it is again surjective, because the kernel
lies in the Frattini subgroup.

This is the field-theoretic form of the correction step of the Scholz-Reichardt construction: the
auxiliary field is chosen so that the twist cancels the inertia of the solution at a prime where it
is not allowed to ramify.

## Main results

* `InverseGalois.CFT.exists_surjective_hom_twist`: **a solution of a central Frattini embedding
  problem, twisted by a character of an auxiliary Galois extension with values in the kernel, is
  again a solution**, over any Galois extension containing both fields.

## Tags

embedding problem, twist, character, Frattini subgroup, Galois group
-/

namespace InverseGalois.CFT

open IntermediateField

variable {A E F L : IntermediateField ℚ (AlgebraicClosure ℚ)}

set_option synthInstance.maxHeartbeats 400000 in
/-- **A solution of a central Frattini embedding problem, twisted by a character of an auxiliary
Galois extension with values in the kernel, is again a solution.**  Both the solution and the
character are inflated to a common Galois extension and multiplied pointwise; the values of the
character are central, so the product is a homomorphism, and it lifts the same map on the base
field because those values lie in the kernel. -/
theorem exists_surjective_hom_twist [Normal ℚ ↥A] [Normal ℚ ↥E] [Normal ℚ ↥F] [Normal ℚ ↥L]
    (hAE : A ≤ E) (hEL : E ≤ L) (hFL : F ≤ L)
    {G H : Type*} [Group G] [Group H] [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hZ : f.ker ≤ Subgroup.center G) (hfr : f.ker ≤ frattini G)
    {π₀ : Gal(↥A/ℚ) →* H} {ψ : Gal(↥E/ℚ) →* G} (hψ : Function.Surjective ψ)
    (hcomp : ∀ τ, f (ψ τ) = π₀ (galRestrictLE hAE τ))
    (χ : Gal(↥F/ℚ) →* G) (hχ : ∀ x, χ x ∈ f.ker) :
    ∃ ψ' : Gal(↥L/ℚ) →* G, Function.Surjective ψ' ∧
      (∀ τ, f (ψ' τ) = π₀ (galRestrictLE (hAE.trans hEL) τ)) ∧
      ∀ τ, ψ' τ = ψ (galRestrictLE hEL τ) * χ (galRestrictLE hFL τ) := by
  have hcen : ∀ x : Gal(↥L/ℚ), (χ.comp (galRestrictLE hFL)) x ∈ Subgroup.center G :=
    fun _ => hZ (hχ _)
  have hker : ∀ x : Gal(↥L/ℚ), (χ.comp (galRestrictLE hFL)) x ∈ f.ker := fun _ => hχ _
  have hinf : Function.Surjective (ψ.comp (galRestrictLE hEL)) :=
    hψ.comp (galRestrictLE_surjective hEL)
  refine ⟨mulCentral (ψ.comp (galRestrictLE hEL)) (χ.comp (galRestrictLE hFL)) hcen,
    surjective_mulCentral hf hfr hinf hcen hker, fun τ => ?_, fun _ => rfl⟩
  rw [mulCentral_apply, map_mul, MonoidHom.mem_ker.mp (hker τ), mul_one]
  rw [MonoidHom.comp_apply, hcomp (galRestrictLE hEL τ), galRestrictLE_galRestrictLE]

end InverseGalois.CFT
