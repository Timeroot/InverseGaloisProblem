/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.InertiaFixedField

/-!
# One prime above each ramified rational prime suffices

The Galois group permutes the primes of a Galois number field above a fixed rational prime
transitively, and conjugation carries the decomposition group and the inertia subgroup of a prime to
those of its image.  A normal subgroup is carried to itself, so the condition that the decomposition
group is absorbed by the inertia subgroup together with a normal subgroup only has to be checked at
one prime above each rational prime.

## Main results

* `InverseGalois.CFT.forall_stabilizer_le_of_stabilizer_le`: **absorption of the decomposition group
  at one prime above `p` gives it at every prime above `p`.**
* `InverseGalois.CFT.isSplitInertia_fixedField_of_exists` and
  `InverseGalois.CFT.isSplitInertia_fixedField_ker_of_exists`: the fixed field of a normal subgroup,
  respectively of the kernel of a homomorphism, has split inertia as soon as the absorption holds at
  one prime above each ramified rational prime.

## Tags

decomposition group, inertia subgroup, fixed field, residue degree, conjugation
-/

open NumberField InverseGalois.NumberTheory

open scoped Pointwise

namespace InverseGalois.CFT

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ}

/-- Conjugation carries a normal subgroup to itself. -/
theorem map_conj_eq_self_of_normal {Γ : Type*} [Group Γ] (H : Subgroup Γ) [hH : H.Normal] (g : Γ) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro - ⟨y, hy, rfl⟩
    exact hH.conj_mem y hy g
  · refine ⟨g⁻¹ * y * g, by simpa using hH.conj_mem y hy g⁻¹, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

/-- **Absorption of the decomposition group at one prime above `p` gives it at every prime above
`p`.**  Conjugation by an automorphism carrying the first prime to the second carries the
decomposition group and the inertia subgroup along with it, and leaves the normal subgroup where it
is. -/
theorem forall_stabilizer_le_of_stabilizer_le (H : Subgroup Gal(N/ℚ)) [H.Normal]
    (P : Ideal (𝓞 N)) [P.IsPrime] (hP : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hle : MulAction.stabilizer Gal(N/ℚ) P ≤ Ideal.inertia Gal(N/ℚ) P ⊔ H)
    (Q : Ideal (𝓞 N)) [Q.IsPrime] (hQ : Q.LiesOver (Ideal.span {(p : ℤ)})) :
    MulAction.stabilizer Gal(N/ℚ) Q ≤ Ideal.inertia Gal(N/ℚ) Q ⊔ H := by
  haveI := hP
  haveI := hQ
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q Gal(N/ℚ)
  subst hσ
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, inertia_smul,
    ← map_conj_eq_self_of_normal H σ]
  simp only [← MulEquiv.toMonoidHom_eq_coe]
  rw [← Subgroup.map_sup]
  exact Subgroup.map_mono hle

/-- **The fixed field of a normal subgroup absorbing the decomposition group at one prime above each
ramified rational prime has split inertia.** -/
theorem isSplitInertia_fixedField_of_exists (H : Subgroup Gal(N/ℚ)) [H.Normal]
    (h : ∀ q ∈ ramifiedSet ↥(IntermediateField.fixedField H), ∃ P : Ideal (𝓞 N), ∃ _ : P.IsPrime,
      ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
        MulAction.stabilizer Gal(N/ℚ) P ≤ Ideal.inertia Gal(N/ℚ) P ⊔ H) :
    IsSplitInertia ↥(IntermediateField.fixedField H) := by
  refine isSplitInertia_fixedField H fun q hq Q hQp hQo => ?_
  obtain ⟨P, hPp, hPo, hle⟩ := h q hq
  haveI := hPp
  haveI := hQp
  exact forall_stabilizer_le_of_stabilizer_le H P hPo hle Q hQo

/-- **The fixed field of the kernel of a homomorphism which sees no more of one decomposition group
above each ramified rational prime than of the corresponding inertia subgroup has split
inertia.** -/
theorem isSplitInertia_fixedField_ker_of_exists {G : Type*} [Group G] (ψ : Gal(N/ℚ) →* G)
    (h : ∀ q ∈ ramifiedSet ↥(IntermediateField.fixedField ψ.ker), ∃ P : Ideal (𝓞 N),
      ∃ _ : P.IsPrime, ∃ _ : P.LiesOver (Ideal.span {(q : ℤ)}),
        (MulAction.stabilizer Gal(N/ℚ) P).map ψ ≤ (Ideal.inertia Gal(N/ℚ) P).map ψ) :
    IsSplitInertia ↥(IntermediateField.fixedField ψ.ker) := by
  refine isSplitInertia_fixedField_of_exists ψ.ker fun q hq => ?_
  obtain ⟨P, hPp, hPo, hle⟩ := h q hq
  exact ⟨P, hPp, hPo, le_sup_ker_of_map_le hle⟩

end InverseGalois.CFT
