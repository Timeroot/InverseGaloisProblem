/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The equivariant divisor carried by one orbit

A group permutes a set of places and acts on a module.  Given a place and a value of the module
fixed by the stabiliser of that place, there is exactly one family supported on the orbit of the
place whose value at a translate is the corresponding translate of the value, and it is
**equivariant**: translating the place translates the value.

This is the shape a prescribed divisor takes in a Kummer assembly.  A value is chosen at one place,
invariant under the decomposition subgroup there because that subgroup must fix the radicand it
will name, and the orbit sum is then forced.  The construction costs nothing arithmetic: the only
hypothesis is that the stabiliser fixes the value, and the only finiteness used is that the orbit
is finite, which follows from the group being finite.

## Main definitions

* `InverseGalois.CFT.orbitDivisor`: the family supported on an orbit carrying a stabiliser
  invariant value.

## Main results

* `InverseGalois.CFT.orbitDivisor_apply_smul`: its value at a translate of the chosen place is the
  corresponding translate of the chosen value.
* `InverseGalois.CFT.orbitDivisor_smul_apply`: **the family is equivariant**, so the divisor it
  names is invariant under the whole group.

## Tags

group action, orbit, stabiliser, divisor, equivariance
-/

namespace InverseGalois.CFT

open MulAction

section OrbitDivisor

variable (Q : Type*) [Group Q] [Finite Q] {X : Type*} [MulAction Q X]
variable {M : Type*} [AddCommGroup M] [DistribMulAction Q M]

/-- The orbit of a point under a finite group is finite. -/
theorem finite_orbit_of_finite (x₀ : X) : (orbit Q x₀).Finite :=
  Set.finite_range _

open scoped Classical in
/-- **The family supported on one orbit carrying a value fixed by the stabiliser.**  At a translate
of the chosen place it is the corresponding translate of the chosen value, and it vanishes off the
orbit. -/
noncomputable def orbitDivisor (x₀ : X) (V : M) : X →₀ M :=
  Finsupp.onFinset (finite_orbit_of_finite Q x₀).toFinset
    (fun x => if h : x ∈ orbit Q x₀ then h.choose • V else 0)
    (fun x hx => by
      by_contra hmem
      rw [Set.Finite.mem_toFinset] at hmem
      exact hx (dif_neg hmem))

theorem orbitDivisor_apply_of_notMem (x₀ : X) (V : M) {x : X} (hx : x ∉ orbit Q x₀) :
    orbitDivisor Q x₀ V x = 0 := by
  classical
  rw [orbitDivisor, Finsupp.onFinset_apply, dif_neg hx]

/-- The value of the orbit family at a translate of the chosen place is the corresponding translate
of the chosen value, provided the stabiliser of the place fixes that value. -/
theorem orbitDivisor_apply_smul (x₀ : X) (V : M) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V) (τ : Q) :
    orbitDivisor Q x₀ V (τ • x₀) = τ • V := by
  classical
  have hmem : τ • x₀ ∈ orbit Q x₀ := ⟨τ, rfl⟩
  rw [orbitDivisor, Finsupp.onFinset_apply, dif_pos hmem]
  have hc : hmem.choose • x₀ = τ • x₀ := hmem.choose_spec
  have hs : τ⁻¹ * hmem.choose ∈ stabilizer Q x₀ := by
    simp only [mem_stabilizer_iff, mul_smul, hc, inv_smul_smul]
  have := hV _ hs
  rw [mul_smul, inv_smul_eq_iff] at this
  exact this

/-- **The orbit family is equivariant**: translating the place translates the value.  Hence the
divisor it names is invariant under the whole group. -/
theorem orbitDivisor_smul_apply (x₀ : X) (V : M) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V) (σ : Q)
    (x : X) : orbitDivisor Q x₀ V (σ • x) = σ • orbitDivisor Q x₀ V x := by
  by_cases hx : x ∈ orbit Q x₀
  · obtain ⟨τ, rfl⟩ := hx
    rw [← mul_smul, orbitDivisor_apply_smul Q x₀ V hV, orbitDivisor_apply_smul Q x₀ V hV, mul_smul]
  · rw [orbitDivisor_apply_of_notMem Q x₀ V hx, orbitDivisor_apply_of_notMem Q x₀ V, smul_zero]
    rintro ⟨g, hg⟩
    have hg' : g • x₀ = σ • x := hg
    refine hx ⟨σ⁻¹ * g, ?_⟩
    show (σ⁻¹ * g) • x₀ = x
    rw [mul_smul, hg', inv_smul_smul]

end OrbitDivisor

end InverseGalois.CFT
