/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SqrtNegOne
import InverseGalois.CFT.SubgroupHilbert90
import InverseGalois.CFT.Units.CompletionGalois
import InverseGalois.CFT.Units.LocalEmbedding

/-!
# A local invariant is a sum of two squares

Let `K` be a Galois extension of a number field `k` containing a square root of minus one, and let
`N` be the subgroup of the Galois group fixing that square root.  The two-cochain taking a single
invariant value `c` at pairs of elements outside `N` and the value one elsewhere is a coboundary
in the units of the completion of `K` at a prime exactly when `c` is a norm from the invariants of
`N` there; and a norm from the invariants of `N` is a sum of two squares, since the square root of
minus one turns the norm form of the quadratic subextension into the sum of two squares.

The argument is carried out in the Galois group of the completion over the completion of the base
rather than in the decomposition group.  Every automorphism of the completion restricts to an
element of the decomposition group, and the restriction is compatible with the actions, so a local
coboundary condition stated over the decomposition group pulls back; in the other direction the
elements of the completion fixed by the whole local Galois group are exactly those coming from the
completion of the base, which is what is wanted of the two squares.

## Main definitions

* `InverseGalois.CFT.restrictToStabilizer`: an automorphism of the completion as an element of the
  decomposition group.

## Main results

* `InverseGalois.CFT.exists_sq_add_sq_of_isMulCoboundary₂`: over a field containing a square root
  of minus one, an invariant unit whose inflated cochain is a coboundary is a sum of two squares
  in the base.
* `InverseGalois.CFT.exists_sq_add_sq_adicCompletion`: **an invariant whose inflated cochain is a
  local coboundary is a sum of two squares in the completion of the base.**

## Tags

number field, completion, decomposition group, Hilbert ninety, index two, sum of two squares
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

/-! ### The abstract statement over a Galois extension -/

section Abstract

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **An invariant unit whose inflated cochain is a coboundary is a sum of two squares in the
base**, when the extension contains a square root of minus one.  Either that square root already
lies in the base, and the unit is a sum of two squares because minus one is a square; or it
generates a quadratic subextension, and the unit is a norm from that subextension, which the
square root of minus one turns into a sum of two squares.  In both cases the two summands are
fixed by the whole Galois group, hence lie in the base. -/
theorem exists_sq_add_sq_of_isMulCoboundary₂ (h2 : (2 : E) ≠ 0) {j : E} (hj : j ^ 2 = -1)
    {c : Eˣ} (hc : ∀ g : E ≃ₐ[F] E, g • (c : E) = (c : E))
    (hcob : groupCohomology.IsMulCoboundary₂
      (indexTwoInflation (stabilizer (E ≃ₐ[F] E) j) c)) :
    ∃ x y : F, algebraMap F E (x ^ 2 + y ^ 2) = (c : E) := by
  have hkey : ∃ x y : E, (∀ g : E ≃ₐ[F] E, g • x = x) ∧ (∀ g : E ≃ₐ[F] E, g • y = y) ∧
      (c : E) = x ^ 2 + y ^ 2 := by
    by_cases hall : ∀ g : E ≃ₐ[F] E, g • j = j
    · exact exists_sq_add_sq_of_forall_smul_eq h2 hj hall hc
    · push_neg at hall
      obtain ⟨σ, hσ⟩ := hall
      have hσN : σ ∉ stabilizer (E ≃ₐ[F] E) j := fun h => hσ (mem_stabilizer_iff.mp h)
      have hcov := mem_stabilizer_or_mul_inv_mem hj hσN
      haveI := stabilizer_normal_of_sq_eq_neg_one (Γ := E ≃ₐ[F] E) hj
      obtain ⟨f, hfN, hfc⟩ := exists_smul_mul_eq_of_isMulCoboundary₂_indexTwoInflation hσN hcov
        (fun _ hg => exists_smul_div_eq_of_mem_subgroup _ hg) hcob
      obtain ⟨x, y, hx, hy, hxy⟩ := exists_sq_add_sq_of_smul_mul_eq h2 hj hσN
        (f := (f : E)) fun n hn => congrArg Units.val (hfN n hn)
      exact ⟨x, y, hx, hy, by rw [← hxy]; exact congrArg Units.val hfc.symm⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := hkey
  obtain ⟨x₀, hx₀⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hx
  obtain ⟨y₀, hy₀⟩ := (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  exact ⟨x₀, y₀, by rw [map_add, map_pow, map_pow, hx₀, hy₀, hxy]⟩

end Abstract

/-! ### The local Galois group inside the decomposition group -/

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (w : HeightOneSpectrum (𝓞 K))

variable (k) in
omit [IsGalois k K] in
set_option synthInstance.maxHeartbeats 800000 in
/-- The Galois group of a completion acts on the units of that completion.  Finding this action
from the general theory is expensive, so it is recorded once here, together with the two actions
it induces, and afterwards found by a direct match on the head of the goal. -/
noncomputable instance instMulDistribMulActionAdicCompletionUnits :
    MulDistribMulAction
      (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
      (w.adicCompletion K)ˣ :=
  inferInstance

variable (k) in
omit [IsGalois k K] in
/-- The Galois group of a completion acts on the units of that completion. -/
noncomputable instance instMulActionAdicCompletionUnits :
    MulAction
      (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
      (w.adicCompletion K)ˣ :=
  MulDistribMulAction.toMulAction

variable (k) in
omit [IsGalois k K] in
/-- The Galois group of a completion acts on the units of that completion. -/
noncomputable instance instSemigroupActionAdicCompletionUnits :
    SemigroupAction
      (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
      (w.adicCompletion K)ˣ :=
  MulAction.toSemigroupAction

variable (k) in
omit [IsGalois k K] in
/-- The Galois group of a completion scales the units of that completion. -/
noncomputable instance instSMulAdicCompletionUnits :
    SMul (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
      (w.adicCompletion K)ˣ :=
  SemigroupAction.toSMul

variable (k) in
/-- **An automorphism of the completion as an element of the decomposition group.** -/
noncomputable def restrictToStabilizer
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    ↥(stabilizer Gal(K/k) w) :=
  ⟨restrictToBase k w τ, restrictToBase_mem_stabilizer k w τ⟩

variable (k) in
@[simp]
theorem coe_restrictToStabilizer
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    (restrictToStabilizer k w τ : Gal(K/k)) = restrictToBase k w τ :=
  rfl

variable (k) in
@[simp]
theorem restrictToStabilizer_smul
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
    (z : w.adicCompletion K) : restrictToStabilizer k w τ • z = τ z :=
  adicCompletionAut_restrictToBase k w τ z

variable (k) in
/-- The restriction of an automorphism of the completion to the decomposition group respects
multiplication. -/
theorem restrictToStabilizer_mul
    (τ τ' : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K) :
    restrictToStabilizer k w (τ * τ')
      = restrictToStabilizer k w τ * restrictToStabilizer k w τ' := by
  refine Subtype.ext (AlgEquiv.ext fun x => (toAdicCompletion w).injective ?_)
  rw [coe_restrictToStabilizer, toAdicCompletion_restrictToBase, AlgEquiv.mul_apply,
    show ((restrictToStabilizer k w τ * restrictToStabilizer k w τ' : ↥(stabilizer Gal(K/k) w)) :
        Gal(K/k)) x = restrictToBase k w τ (restrictToBase k w τ' x) from rfl,
    toAdicCompletion_restrictToBase, toAdicCompletion_restrictToBase]

variable (k) in
/-- The restriction of an automorphism of the completion moves an element of the field the same
way the automorphism moves its image. -/
theorem toAdicCompletion_restrictToStabilizer_smul
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
    (x : K) :
    toAdicCompletion w ((restrictToStabilizer k w τ : Gal(K/k)) • x) = τ • toAdicCompletion w x :=
  toAdicCompletion_restrictToBase k w τ x

variable (k) in
/-- The additive action of the restriction of an automorphism of the completion on the units is
the action of the automorphism itself. -/
theorem toMul_smulUnitsAut_restrictToStabilizer
    (τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
    (u : Additive (w.adicCompletion K)ˣ) :
    Additive.toMul (smulUnitsAut (restrictToStabilizer k w τ) u) = τ • Additive.toMul u := by
  refine Units.ext ?_
  rw [coe_smulUnitsAut_apply, restrictToStabilizer_smul]
  rfl

/-! ### The local step -/

variable (k) in
/-- **An invariant whose inflated cochain is a coboundary in the units of a completion is a sum of
two squares in the completion of the base.**  The square root of minus one splits the norm form of
the quadratic subextension it generates into a sum of two squares, and the two summands, being
fixed by the whole local Galois group, come from the completion of the base. -/
theorem exists_sq_add_sq_adicCompletion {ι : K} (hι : ι ^ 2 = -1) {c : Kˣ}
    (hc : ∀ g : Gal(K/k), g • (c : K) = (c : K))
    (hcob : ∃ b : ↥(stabilizer Gal(K/k) w) → Additive (w.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (adicUnitHom w (indexTwoInflation (stabilizer Gal(K/k) ι) c (s.1, t.1)))
          = smulUnitsAut s (b t) - b (s * t) + b s) :
    ∃ x y : (primeUnder (𝓞 k) w).adicCompletion k,
      algebraMap ((primeUnder (𝓞 k) w).adicCompletion k) (w.adicCompletion K) (x ^ 2 + y ^ 2)
        = toAdicCompletion w (c : K) := by
  haveI := isGalois_adicCompletion k w
  have hinj := (toAdicCompletion (K := K) w).injective
  have h2 : (2 : w.adicCompletion K) ≠ 0 := by
    intro h
    exact two_ne_zero (α := K) (hinj (by rw [map_ofNat, map_zero, h]))
  have hj : (toAdicCompletion w ι) ^ 2 = -1 := by
    rw [← map_pow, hι, map_neg, map_one]
  have hmem : ∀ τ : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
        w.adicCompletion K,
      τ ∈ stabilizer (w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
          w.adicCompletion K) (toAdicCompletion w ι)
        ↔ (restrictToStabilizer k w τ : Gal(K/k)) ∈ stabilizer Gal(K/k) ι := by
    intro τ
    rw [mem_stabilizer_iff, mem_stabilizer_iff,
      ← toAdicCompletion_restrictToStabilizer_smul k w τ ι, hinj.eq_iff]
  have hinfl : ∀ τ τ' : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
        w.adicCompletion K,
      adicUnitHom w (indexTwoInflation (stabilizer Gal(K/k) ι) c
          ((restrictToStabilizer k w τ : Gal(K/k)), (restrictToStabilizer k w τ' : Gal(K/k))))
        = indexTwoInflation (stabilizer (w.adicCompletion K
            ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
          (toAdicCompletion w ι)) (adicUnitHom w c) (τ, τ') := by
    intro τ τ'
    by_cases hτ : τ ∈ stabilizer _ (toAdicCompletion w ι)
    · rw [indexTwoInflation_of_mem_left ((hmem τ).mp hτ), indexTwoInflation_of_mem_left hτ,
        map_one]
    · by_cases hτ' : τ' ∈ stabilizer _ (toAdicCompletion w ι)
      · rw [indexTwoInflation_of_mem_right ((hmem τ').mp hτ'), indexTwoInflation_of_mem_right hτ',
          map_one]
      · rw [indexTwoInflation_of_not_mem (fun h => hτ ((hmem τ).mpr h))
          (fun h => hτ' ((hmem τ').mpr h)), indexTwoInflation_of_not_mem hτ hτ']
  obtain ⟨b, hb⟩ := hcob
  have hcobΓ : groupCohomology.IsMulCoboundary₂
      (indexTwoInflation (stabilizer (w.adicCompletion K
          ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k] w.adicCompletion K)
        (toAdicCompletion w ι)) (adicUnitHom w c)) := by
    rw [isMulCoboundary₂_iff]
    refine ⟨fun τ => Additive.toMul (b (restrictToStabilizer k w τ)), funext fun p => ?_⟩
    obtain ⟨τ, τ'⟩ := p
    have h := congrArg Additive.toMul (hb (restrictToStabilizer k w τ)
      (restrictToStabilizer k w τ'))
    simp only [toMul_ofMul, toMul_add, toMul_sub] at h
    rw [coboundary₂_apply, ← hinfl τ τ', h, restrictToStabilizer_mul,
      toMul_smulUnitsAut_restrictToStabilizer]
  have hcE : ∀ g : w.adicCompletion K ≃ₐ[(primeUnder (𝓞 k) w).adicCompletion k]
      w.adicCompletion K, g • ((adicUnitHom w c : (w.adicCompletion K)ˣ) : w.adicCompletion K)
        = ((adicUnitHom w c : (w.adicCompletion K)ˣ) : w.adicCompletion K) := by
    intro g
    show g • toAdicCompletion w (c : K) = toAdicCompletion w (c : K)
    rw [← toAdicCompletion_restrictToStabilizer_smul k w g (c : K), hc]
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_of_isMulCoboundary₂ h2 hj hcE hcobΓ
  exact ⟨x, y, hxy⟩

end InverseGalois.CFT
