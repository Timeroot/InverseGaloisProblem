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
* `InverseGalois.CFT.zpowCentral`: the power of a homomorphism taking central values.

## Main results

* `InverseGalois.CFT.comp_mulCentral`: **a twist by a character with values in the kernel lifts the
  same homomorphism.**
* `InverseGalois.CFT.surjective_mulCentral`: **a twist of a solution of an embedding problem with
  kernel inside the Frattini subgroup is again a solution.**
* `InverseGalois.CFT.exists_zpow_mul_eq_one_of_isCyclic_subgroup`: **on a cyclic subgroup a
  homomorphism is cancelled by a power of a second one whose image on that subgroup contains its
  own** — the choice of exponent made, one prime at a time, when the ramification of a solution is
  corrected.

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

/-! ### Choosing the power of the character -/

/-- **The power of a homomorphism taking central values.**  Its values commute with one another, so
raising them all to a fixed power is again a homomorphism. -/
def zpowCentral (χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) (a : ℤ) : Γ →* G where
  toFun x := χ x ^ a
  map_one' := by simp
  map_mul' x y := by
    have hc : Commute (χ x) (χ y) := ((Subgroup.mem_center_iff.mp (hχ x)) (χ y)).symm
    rw [map_mul, hc.mul_zpow]

@[simp]
theorem zpowCentral_apply (χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) (a : ℤ) (x : Γ) :
    zpowCentral χ hχ a x = χ x ^ a :=
  rfl

/-- A power of a character with values in a subgroup again has values in that subgroup. -/
theorem zpowCentral_mem (χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) (a : ℤ) {K : Subgroup G}
    (hK : ∀ x, χ x ∈ K) (x : Γ) :
    zpowCentral χ hχ a x ∈ K :=
  zpow_mem (hK x) a

/-- A power of a character with central values again has central values. -/
theorem zpowCentral_mem_center (χ : Γ →* G) (hχ : ∀ x, χ x ∈ Subgroup.center G) (a : ℤ) (x : Γ) :
    zpowCentral χ hχ a x ∈ Subgroup.center G :=
  zpow_mem (hχ x) a

/-- **On a cyclic group a homomorphism is cancelled by a power of a central-valued homomorphism
whose image contains its own.**  Everything is determined by the value at a generator, where the
hypothesis exhibits the first value as a power of the second. -/
theorem exists_zpow_mul_eq_one_of_isCyclic {I : Type*} [Group I] [IsCyclic I] (φ χ : I →* G)
    (h : φ.range ≤ χ.range) :
    ∃ a : ℤ, ∀ x : I, φ x * χ x ^ a = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := I)
  obtain ⟨y, hy⟩ := h ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
  have hgk : φ g = χ g ^ k := by rw [← hy, ← hk, map_zpow]
  refine ⟨-k, fun x => ?_⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have hx : φ (g ^ m) * χ (g ^ m) ^ (-k) = χ g ^ (k * m) * χ g ^ (m * (-k)) := by
    rw [map_zpow, map_zpow, hgk, ← zpow_mul, ← zpow_mul]
  have hzero : k * m + m * (-k) = 0 := by ring
  rw [hx, ← zpow_add, hzero, zpow_zero]

/-- The image of a subgroup is the range of the restriction of the homomorphism to it. -/
theorem range_comp_subtype (θ : Γ →* G) (I : Subgroup Γ) :
    (θ.comp I.subtype).range = I.map θ := by
  ext y
  simp [MonoidHom.mem_range, Subgroup.mem_map]

/-- **On a cyclic subgroup a homomorphism is cancelled by a power of a central-valued homomorphism
whose image on that subgroup contains its own.**  This is the choice of exponent made, one prime at
a time, when the ramification of a solution of an embedding problem is corrected. -/
theorem exists_zpow_mul_eq_one_of_isCyclic_subgroup {I : Subgroup Γ} [IsCyclic ↥I] (φ χ : Γ →* G)
    (h : I.map φ ≤ I.map χ) :
    ∃ a : ℤ, ∀ x ∈ I, φ x * χ x ^ a = 1 := by
  obtain ⟨a, ha⟩ := exists_zpow_mul_eq_one_of_isCyclic (φ.comp I.subtype) (χ.comp I.subtype)
    (by rw [range_comp_subtype, range_comp_subtype]; exact h)
  exact ⟨a, fun x hx => ha ⟨x, hx⟩⟩

end InverseGalois.CFT
