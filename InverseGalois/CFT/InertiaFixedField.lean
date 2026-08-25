/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaGeneration
import InverseGalois.CFT.InertiaSubgroup

/-!
# The ramified primes of the fixed field of a subgroup

Let `N` be a Galois number field.  A rational prime ramifies in the fixed field of a subgroup `H` of
`Gal(N/ℚ)` exactly when some prime of `𝓞 N` above it has inertia subgroup not contained in `H`.
One direction is the statement that the inertia subgroup at a prime unramified in a subextension
fixes that subextension pointwise; the other is the ramification-index computation in the tower
`ℤ ⊆ 𝓞 E ⊆ 𝓞 N`, where `E` is the fixed field.

This is the tool that reads off the ramification of a solution of an embedding problem: a surjection
`ψ : Gal(N/ℚ) →* G` cuts out the fixed field of its kernel, and the primes ramifying there are
exactly those at which `ψ` is nontrivial on inertia.

## Main results

* `InverseGalois.CFT.notMem_ramifiedSet_fixedField`: **a rational prime all of whose inertia
  subgroups lie in a subgroup is unramified in the fixed field of that subgroup.**
* `InverseGalois.CFT.mem_ramifiedSet_fixedField_iff`: **a rational prime ramifies in the fixed field
  of a normal subgroup exactly when the inertia subgroup of some prime above it is not contained in
  that subgroup.**
* `InverseGalois.CFT.notMem_ramifiedSet_fixedField_ker`: **a rational prime at which a homomorphism
  kills every inertia subgroup is unramified in the fixed field of its kernel.**

## Tags

inertia subgroup, fixed field, ramified prime, Galois number field
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

/-- **A rational prime all of whose inertia subgroups lie in a subgroup is unramified in the fixed
field of that subgroup.**  A prime of the fixed field above `p` is the prime below some prime `P` of
`𝓞 N`, and the ramification index of `P` over the fixed field already accounts for the whole inertia
subgroup of `P`, leaving nothing for the layer below. -/
theorem notMem_ramifiedSet_fixedField (H : Subgroup Gal(N/ℚ)) (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 N), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
      Ideal.inertia Gal(N/ℚ) P ≤ H) :
    p ∉ ramifiedSet ↥(IntermediateField.fixedField H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E : IntermediateField ℚ N := IntermediateField.fixedField H with hE
  haveI : NumberField ↥E := ⟨⟩
  rintro ⟨-, Q, ⟨hQprime, hQover⟩, hQe⟩
  haveI := hQprime
  haveI := hQover
  have hQbot : Q ≠ ⊥ := ne_bot_of_liesOver p Q
  obtain ⟨⟨P, hPp, hPo⟩⟩ := Q.nonempty_primesOver (S := 𝓞 N)
  haveI := hPp
  haveI := hPo
  have hQeq : Q = P.under (𝓞 ↥E) := hPo.over
  have hUbot : P.under (𝓞 ↥E) ≠ ⊥ := hQeq ▸ hQbot
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hUbot P
  have hunder : (P.under (𝓞 ↥E)).under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hQeq]
    exact hQover.over.symm
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by rw [← hunder, Ideal.under_under]⟩
  have hunr := isUnramifiedAt_under_fixedField_of_inertia_le H P hPbot (h P hPp inferInstance)
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) hUbot, hunder, ← hQeq] at hunr
  exact hQe hunr

/-- **A rational prime ramifies in the fixed field of a normal subgroup exactly when the inertia
subgroup of some prime above it is not contained in that subgroup.**  The fixed field of a normal
subgroup is Galois over the rationals, so the inertia subgroup at an unramified prime restricts
trivially to it, which is to say that it fixes it pointwise. -/
theorem mem_ramifiedSet_fixedField_iff (H : Subgroup Gal(N/ℚ)) [H.Normal] (hp : p.Prime) :
    p ∈ ramifiedSet ↥(IntermediateField.fixedField H) ↔
      ∃ P : Ideal (𝓞 N), ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(p : ℤ)}),
        ¬ Ideal.inertia Gal(N/ℚ) P ≤ H := by
  constructor
  · intro hmem
    by_contra hc
    push_neg at hc
    exact notMem_ramifiedSet_fixedField H hp (fun P h1 h2 => hc P h1 h2) hmem
  · rintro ⟨P, hPp, hPo, hle⟩
    haveI := hPp
    haveI := hPo
    by_contra hnot
    exact hle ((IntermediateField.fixingSubgroup_fixedField H) ▸
      inertia_le_fixingSubgroup (IntermediateField.fixedField H) hp P hnot)

/-- **A rational prime at which a homomorphism kills every inertia subgroup is unramified in the
fixed field of its kernel.** -/
theorem notMem_ramifiedSet_fixedField_ker {G : Type*} [Group G] (ψ : Gal(N/ℚ) →* G) (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 N), P.IsPrime → P.LiesOver (Ideal.span {(p : ℤ)}) →
      ∀ σ ∈ Ideal.inertia Gal(N/ℚ) P, ψ σ = 1) :
    p ∉ ramifiedSet ↥(IntermediateField.fixedField ψ.ker) :=
  notMem_ramifiedSet_fixedField ψ.ker hp fun P h1 h2 σ hσ => MonoidHom.mem_ker.mpr (h P h1 h2 σ hσ)

end InverseGalois.CFT
