/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.FrobeniusStabilizer
import InverseGalois.CFT.InertiaSurjective

/-!
# The Frobenius defect of a central step

A central step of a Scholz–Reichardt tower is a surjection `f : G → H` with kernel of prime order,
solved over a normal subextension `F` of a Galois number field `N` by a homomorphism `ψ` from the
Galois group of `N` lifting an isomorphism `e` of the Galois group of `F` with `H`.  The
subextension has split inertia, so at a prime `p` ramified in it the decomposition group downstairs
is already the inertia group; an arithmetic Frobenius upstairs therefore restricts into the inertia
group
downstairs, and restriction maps inertia onto inertia.  Comparing the Frobenius with an element of
the inertia group upstairs having the same restriction measures by how much the image of the
Frobenius fails to lie in the image of the inertia group, and the failure is an element of the
kernel of `f`.

That element is the defect the residue correction has to cancel.  It does not depend on which
arithmetic Frobenius at the prime is chosen, since any two of them differ by an element of the
inertia group.

## Main results

* `InverseGalois.CFT.exists_mem_ker_mul_mem_map_inertia`: **the image of an arithmetic Frobenius
  lies in the image of the inertia group up to a single element of the kernel of `f`, the same
  element for every arithmetic Frobenius at the prime.**

## Tags

Frobenius, inertia subgroup, split inertia, central extension, Scholz–Reichardt
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
/-- **The image of an arithmetic Frobenius lies in the image of the inertia group up to a single
element of the kernel of `f`, the same element for every arithmetic Frobenius at the prime.**  Split
inertia in the subextension makes the restriction of a Frobenius an element of the inertia group
downstairs, restriction maps the inertia group upstairs onto the one downstairs, and an element of
the inertia group upstairs with the same restriction as the Frobenius differs from it by an element
mapping to the identity under `f`. -/
theorem exists_mem_ker_mul_mem_map_inertia (F : IntermediateField ℚ N) [Normal ℚ ↥F]
    (hmem : p ∈ ramifiedSet ↥F) (hsplit : IsSplitInertia ↥F)
    (P : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {G H : Type*} [Group G] [Group H] {f : G →* H} (ψ : Gal(N/ℚ) →* G) (e : Gal(↥F/ℚ) ≃* H)
    (hcomp : ∀ τ, f (ψ τ) = e (AlgEquiv.restrictNormalHom ↥F τ)) :
    ∃ z ∈ f.ker, ∀ σ : Gal(N/ℚ), IsArithFrobAt ℤ σ P →
      ψ σ * z ∈ (Ideal.inertia Gal(N/ℚ) P).map ψ := by
  have hp : p.Prime := hmem.1
  haveI : IsGalois ℚ ↥F := ⟨⟩
  haveI := liesOver_under_intermediateField (p := p) F P
  haveI : Finite (𝓞 N ⧸ P) := finite_quotient_of_ne_bot P (ne_bot_of_liesOver_natCast hp ‹_›)
  haveI : Finite (𝓞 ↥F ⧸ P.under (𝓞 ↥F)) :=
    finite_quotient_of_ne_bot _ (ne_bot_of_liesOver_natCast hp ‹_›)
  -- an arithmetic Frobenius at `P`, and its restriction downstairs
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Gal(N/ℚ), IsArithFrobAt ℤ σ₀ P :=
    ⟨_, IsArithFrobAt.arithFrobAt ℤ Gal(N/ℚ) P⟩
  have hstab : AlgEquiv.restrictNormalHom ↥F σ₀ ∈ Ideal.inertia Gal(↥F/ℚ) (P.under (𝓞 ↥F)) := by
    rw [inertia_eq_stabilizer_of_isSplitInertia hsplit hmem (P.under (𝓞 ↥F))]
    exact mem_stabilizer_of_isArithFrobAt (K := ↥F) (P.under (𝓞 ↥F))
      (isArithFrobAt_restrictNormal F σ₀ P hσ₀)
  rw [← map_inertia_eq_inertia F hp P] at hstab
  obtain ⟨i, hi, hires⟩ := Subgroup.mem_map.mp hstab
  refine ⟨(ψ σ₀)⁻¹ * ψ i, ?_, fun σ hσ => ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hcomp, hcomp, hires, inv_mul_cancel]
  · have hrw : ψ σ * ((ψ σ₀)⁻¹ * ψ i) = ψ (σ * σ₀⁻¹) * ψ i := by
      rw [map_mul, map_inv]
      group
    rw [hrw]
    exact mul_mem (Subgroup.mem_map_of_mem ψ (hσ.mul_inv_mem_inertia hσ₀))
      (Subgroup.mem_map_of_mem ψ hi)

end InverseGalois.CFT
