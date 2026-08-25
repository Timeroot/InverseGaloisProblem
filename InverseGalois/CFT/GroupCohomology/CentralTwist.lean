/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CentralLift

/-!
# Twisting a solution of an embedding problem by a central character

Two solutions of the same embedding problem differ by a homomorphism into the kernel, and
conversely a solution may be multiplied pointwise by any homomorphism with central values and
remains a homomorphism.  When the values lie in the kernel of the surjection being lifted, the
twisted homomorphism lifts the same map, and when the kernel lies inside the Frattini subgroup the
twisted homomorphism is again surjective.

This is the group-theoretic content of the step of the Scholz-Reichardt construction in which a
solution with uncontrolled ramification is corrected, prime by prime, by a character of order `ℓ`.

## Main definitions

* `InverseGalois.CFT.mulCentral`: the pointwise product of a homomorphism with a homomorphism
  taking central values.

## Main results

* `InverseGalois.CFT.comp_mulCentral`: **a twist by a character with values in the kernel lifts the
  same homomorphism.**
* `InverseGalois.CFT.surjective_mulCentral`: **a twist of a solution of an embedding problem with
  kernel inside the Frattini subgroup is again a solution.**

## Tags

embedding problem, central extension, twist, character, Frattini subgroup
-/

namespace InverseGalois.CFT

variable {Γ G H : Type*} [Group Γ] [Group G] [Group H]

/-- **The pointwise product of a homomorphism with a homomorphism taking central values.**  The
values of the second factor commute with everything, so the product of the values at `x` and at `y`
may be rearranged into the value at `x * y`. -/
def mulCentral (φ χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) : Γ →* G where
  toFun x := φ x * χ x
  map_one' := by simp
  map_mul' x y := by
    have hc := (Subgroup.mem_center_iff.mp (hχ x)) (φ y)
    simp only [map_mul]
    rw [mul_assoc (φ x) (χ x) (φ y * χ y), ← mul_assoc (χ x) (φ y) (χ y), ← hc]
    group

@[simp]
theorem mulCentral_apply (φ χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) (x : Γ) :
    mulCentral φ χ hχ x = φ x * χ x :=
  rfl

/-- **A twist by a character with values in the kernel lifts the same homomorphism.** -/
theorem comp_mulCentral {f : G →* H} {φ χ : Γ →* G} (hχ : ∀ x, χ x ∈ Subgroup.center G)
    (hker : ∀ x, χ x ∈ f.ker) : f.comp (mulCentral φ χ hχ) = f.comp φ := by
  ext x
  simp [MonoidHom.mem_ker.mp (hker x)]

/-- **A twist of a solution of an embedding problem by a character with values in a kernel inside
the Frattini subgroup is again a solution.**  The twisted homomorphism still lifts the surjection
onto the quotient, and a lift of a surjection through a surjection with kernel inside the Frattini
subgroup is automatically surjective. -/
theorem surjective_mulCentral [Finite G] {f : G →* H} (hf : Function.Surjective f)
    (hfr : f.ker ≤ frattini G) {φ χ : Γ →* G} (hφ : Function.Surjective φ)
    (hχ : ∀ x, χ x ∈ Subgroup.center G) (hker : ∀ x, χ x ∈ f.ker) :
    Function.Surjective (mulCentral φ χ hχ) :=
  surjective_of_le_frattini hfr (π := f.comp φ) (hf.comp hφ)
    (fun x => congrArg (fun ψ => ψ x) (comp_mulCentral hχ hker))

end InverseGalois.CFT
