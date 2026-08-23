/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.Places

/-!
# The Galois action on the adic completions

An automorphism of a Dedekind domain carries the valuation attached to a height one prime onto the
valuation attached to the image of that prime: it is an isometry from one adic metric to the other.
Being an isometry it is uniformly continuous, so it extends to the completions, and a Galois
automorphism of a number field therefore identifies the completion at a prime with the completion
at the image of the prime.

## Main definitions

* `InverseGalois.CFT.withValGalEquiv`: a Galois automorphism, read as a map from the field with the
  topology of one prime to the field with the topology of the image prime.
* `InverseGalois.CFT.adicCompletionGalEquiv`: **the induced isomorphism of adic completions.**

## Main results

* `InverseGalois.CFT.intValuation_smul`: the valuation of an element of the domain at a prime is
  the valuation of its image at the image of the prime.
* `InverseGalois.CFT.valuation_galSmul`: the same over the field of fractions of the ring of
  integers of a number field.
* `InverseGalois.CFT.valued_adicCompletionGalEquiv`: the isomorphism of completions is an isometry.

## Tags

number field, adic completion, Galois action, valuation, decomposition group
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

open scoped Pointwise

/-! ### The valuation at a moved prime -/

section IntValuation

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]

/-- **The valuation of an element of the domain at a prime is the valuation of its image at the
image of the prime.**  An automorphism carries the powers of a prime onto the powers of its image,
and the valuation is pinned by the powers in which the element lies. -/
theorem intValuation_smul (σ : G) (v : HeightOneSpectrum B) (b : B) :
    (σ • v).intValuation (σ • b) = v.intValuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [smul_zero, map_zero, map_zero]
  have hσb : σ • b ≠ 0 := fun h => hb (by simpa using congrArg (fun y => σ⁻¹ • y) h)
  obtain ⟨a, ea⟩ : ∃ a : ℤ, (σ • v).intValuation (σ • b) = WithZero.exp a :=
    ⟨_, (WithZero.exp_log ((σ • v).intValuation_ne_zero _ hσb)).symm⟩
  obtain ⟨c, ec⟩ : ∃ c : ℤ, v.intValuation b = WithZero.exp c :=
    ⟨_, (WithZero.exp_log (v.intValuation_ne_zero _ hb)).symm⟩
  rw [ea, ec, WithZero.exp_inj]
  have ha0 : a ≤ 0 := by
    refine WithZero.exp_le_exp.mp ?_
    rw [WithZero.exp_zero, ← ea]
    exact (σ • v).intValuation_le_one _
  have hc0 : c ≤ 0 := by
    refine WithZero.exp_le_exp.mp ?_
    rw [WithZero.exp_zero, ← ec]
    exact v.intValuation_le_one _
  have key : ∀ j : ℕ, (a ≤ -(j : ℤ) ↔ c ≤ -(j : ℤ)) := by
    intro j
    have e1 := (σ • v).intValuation_le_pow_iff_mem (σ • b) j
    have e2 := v.intValuation_le_pow_iff_mem b j
    rw [ea, WithZero.exp_le_exp] at e1
    rw [ec, WithZero.exp_le_exp] at e2
    rw [e1, e2, asIdeal_smul, smul_mem_pow_smul_iff]
  have k1 := (key (-a).toNat).mp (by omega)
  have k2 := (key (-c).toNat).mpr (by omega)
  omega

end IntValuation

/-! ### The valuation at a moved prime of a number field -/

section NumberField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

/-- **The valuation of an element of a number field at a prime is the valuation of its image at the
image of the prime.** -/
theorem valuation_galSmul (σ : Gal(K/k)) (x : K) :
    (σ • v).valuation K (σ x) = v.valuation K x := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hdiv : σ (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c)
      = algebraMap (𝓞 K) K (σ • b) / algebraMap (𝓞 K) K (σ • (c : 𝓞 K)) := by
    rw [map_div₀]
    rfl
  rw [hdiv, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul, intValuation_smul]

/-! ### The isometry of the two topologies -/

/-- **A Galois automorphism, read as a map from the field with the topology of one prime to the
field with the topology of the image prime.** -/
def withValGalEquiv (σ : Gal(K/k)) :
    WithVal (v.valuation K) ≃+* WithVal ((σ • v).valuation K) :=
  ((WithVal.equiv (v.valuation K)).trans σ.toRingEquiv).trans
    (WithVal.equiv ((σ • v).valuation K)).symm

theorem withValGalEquiv_apply (σ : Gal(K/k)) (x : WithVal (v.valuation K)) :
    withValGalEquiv v σ x = (WithVal.equiv ((σ • v).valuation K)).symm
      (σ (WithVal.equiv (v.valuation K) x)) := rfl

@[simp]
theorem valued_withValGalEquiv (σ : Gal(K/k)) (x : WithVal (v.valuation K)) :
    Valued.v (withValGalEquiv v σ x) = Valued.v x := by
  rw [← WithVal.apply_equiv, ← WithVal.apply_equiv]
  exact valuation_galSmul v σ _

@[simp]
theorem valued_withValGalEquiv_symm (σ : Gal(K/k)) (y : WithVal ((σ • v).valuation K)) :
    Valued.v ((withValGalEquiv v σ).symm y) = Valued.v y := by
  have h := valued_withValGalEquiv v σ ((withValGalEquiv v σ).symm y)
  rw [(withValGalEquiv v σ).apply_symm_apply] at h
  exact h.symm

end NumberField

/-! ### Uniform continuity of an isometry -/

section Isometry

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {A C : Type*} [Ring A] [Ring C]
  [Valued A Γ₀] [Valued C Γ₀]

/-- **A ring isomorphism that preserves the valuation is uniformly continuous.** -/
theorem uniformContinuous_of_valued_eq (f : A ≃+* C) (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero (f : A →+ C) ?_
  simp_rw [ContinuousAt, AddMonoidHom.coe_coe, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  exact fun γ => ⟨γ, fun x hx => by simpa only [Set.mem_setOf_eq, hf] using hx⟩

end Isometry

/-! ### The isomorphism of the completions -/

section Completion

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

theorem uniformContinuous_withValGalEquiv (σ : Gal(K/k)) :
    UniformContinuous (withValGalEquiv v σ) :=
  uniformContinuous_of_valued_eq _ (valued_withValGalEquiv v σ)

theorem uniformContinuous_withValGalEquiv_symm (σ : Gal(K/k)) :
    UniformContinuous (withValGalEquiv v σ).symm :=
  uniformContinuous_of_valued_eq _ (valued_withValGalEquiv_symm v σ)

/-- **The isomorphism between the completion at a prime and the completion at its image** under a
Galois automorphism. -/
noncomputable def adicCompletionGalEquiv (σ : Gal(K/k)) :
    v.adicCompletion K ≃+* (σ • v).adicCompletion K :=
  UniformSpace.Completion.mapRingEquiv (withValGalEquiv v σ)
    (uniformContinuous_withValGalEquiv v σ).continuous
    (uniformContinuous_withValGalEquiv_symm v σ).continuous

theorem continuous_adicCompletionGalEquiv (σ : Gal(K/k)) :
    Continuous (adicCompletionGalEquiv v σ) :=
  UniformSpace.Completion.continuous_map

@[simp]
theorem adicCompletionGalEquiv_coe (σ : Gal(K/k)) (x : WithVal (v.valuation K)) :
    adicCompletionGalEquiv v σ (x : v.adicCompletion K)
      = ((withValGalEquiv v σ x : WithVal ((σ • v).valuation K)) : (σ • v).adicCompletion K) :=
  UniformSpace.Completion.mapRingHom_coe (uniformContinuous_withValGalEquiv v σ).continuous x

open scoped WithZeroTopology in
/-- **The isomorphism of completions is an isometry.** -/
@[simp]
theorem valued_adicCompletionGalEquiv (σ : Gal(K/k)) (z : v.adicCompletion K) :
    Valued.v (adicCompletionGalEquiv v σ z) = Valued.v z := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (Valued.continuous_valuation.comp (continuous_adicCompletionGalEquiv v σ))
      Valued.continuous_valuation
  · intro x
    rw [adicCompletionGalEquiv_coe, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply,
      valued_withValGalEquiv]

end Completion

/-! ### The action of the decomposition group -/

section Decomposition

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
  (v : HeightOneSpectrum (𝓞 K))

/-- **A Galois automorphism fixing a prime, read as a map of the field with the topology of that
prime.** -/
def withValAut (σ : Gal(K/k)) (_hσ : σ • v = v) :
    WithVal (v.valuation K) ≃+* WithVal (v.valuation K) :=
  ((WithVal.equiv (v.valuation K)).trans σ.toRingEquiv).trans (WithVal.equiv (v.valuation K)).symm

@[simp]
theorem valued_withValAut (σ : Gal(K/k)) (hσ : σ • v = v) (x : WithVal (v.valuation K)) :
    Valued.v (withValAut v σ hσ x) = Valued.v x := by
  have h := valuation_galSmul v σ (WithVal.equiv (v.valuation K) x)
  rw [hσ] at h
  rw [← WithVal.apply_equiv, ← WithVal.apply_equiv]
  exact h

@[simp]
theorem valued_withValAut_symm (σ : Gal(K/k)) (hσ : σ • v = v) (y : WithVal (v.valuation K)) :
    Valued.v ((withValAut v σ hσ).symm y) = Valued.v y := by
  have h := valued_withValAut v σ hσ ((withValAut v σ hσ).symm y)
  rw [(withValAut v σ hσ).apply_symm_apply] at h
  exact h.symm

theorem uniformContinuous_withValAut (σ : Gal(K/k)) (hσ : σ • v = v) :
    UniformContinuous (withValAut v σ hσ) :=
  uniformContinuous_of_valued_eq _ (valued_withValAut v σ hσ)

theorem uniformContinuous_withValAut_symm (σ : Gal(K/k)) (hσ : σ • v = v) :
    UniformContinuous (withValAut v σ hσ).symm :=
  uniformContinuous_of_valued_eq _ (valued_withValAut_symm v σ hσ)

/-- **The automorphism of the completion at a prime induced by a Galois automorphism fixing that
prime.** -/
noncomputable def adicCompletionAut (σ : Gal(K/k)) (hσ : σ • v = v) :
    v.adicCompletion K ≃+* v.adicCompletion K :=
  UniformSpace.Completion.mapRingEquiv (withValAut v σ hσ)
    (uniformContinuous_withValAut v σ hσ).continuous
    (uniformContinuous_withValAut_symm v σ hσ).continuous

theorem continuous_adicCompletionAut (σ : Gal(K/k)) (hσ : σ • v = v) :
    Continuous (adicCompletionAut v σ hσ) :=
  UniformSpace.Completion.continuous_map

@[simp]
theorem adicCompletionAut_coe (σ : Gal(K/k)) (hσ : σ • v = v) (x : WithVal (v.valuation K)) :
    adicCompletionAut v σ hσ (x : v.adicCompletion K)
      = ((withValAut v σ hσ x : WithVal (v.valuation K)) : v.adicCompletion K) :=
  UniformSpace.Completion.mapRingHom_coe (uniformContinuous_withValAut v σ hσ).continuous x

open scoped WithZeroTopology in
/-- **The automorphism of the completion is an isometry.** -/
@[simp]
theorem valued_adicCompletionAut (σ : Gal(K/k)) (hσ : σ • v = v) (z : v.adicCompletion K) :
    Valued.v (adicCompletionAut v σ hσ z) = Valued.v z := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (Valued.continuous_valuation.comp (continuous_adicCompletionAut v σ hσ))
      Valued.continuous_valuation
  · intro x
    rw [adicCompletionAut_coe, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply,
      valued_withValAut]

theorem adicCompletionAut_one (z : v.adicCompletion K) :
    adicCompletionAut v (1 : Gal(K/k)) (one_smul Gal(K/k) v) z = z := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_adicCompletionAut v (1 : Gal(K/k)) (one_smul Gal(K/k) v))
      continuous_id
  · intro x
    rw [adicCompletionAut_coe]
    rfl

theorem adicCompletionAut_mul (σ τ : Gal(K/k)) (hσ : σ • v = v) (hτ : τ • v = v)
    (hστ : (σ * τ) • v = v) (z : v.adicCompletion K) :
    adicCompletionAut v (σ * τ) hστ z
      = adicCompletionAut v σ hσ (adicCompletionAut v τ hτ z) := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (continuous_adicCompletionAut v (σ * τ) hστ)
      ((continuous_adicCompletionAut v σ hσ).comp (continuous_adicCompletionAut v τ hτ))
  · intro x
    rw [adicCompletionAut_coe, adicCompletionAut_coe, adicCompletionAut_coe]
    rfl

/-- **The decomposition group at a prime acts on the completion there.** -/
noncomputable instance instMulSemiringActionAdicCompletion :
    MulSemiringAction ↥(stabilizer Gal(K/k) v) (v.adicCompletion K) where
  smul σ z := adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2) z
  one_smul z := adicCompletionAut_one v z
  mul_smul σ τ z := adicCompletionAut_mul v σ.1 τ.1 _ _ _ z
  smul_zero σ := map_zero (adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_add σ := map_add (adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_one σ := map_one (adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))
  smul_mul σ := map_mul (adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2))

@[simp]
theorem stabilizer_smul_adicCompletion_def (σ : ↥(stabilizer Gal(K/k) v))
    (z : v.adicCompletion K) :
    σ • z = adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2) z := rfl

/-- The decomposition group preserves the valuation on the completion. -/
@[simp]
theorem valued_stabilizer_smul (σ : ↥(stabilizer Gal(K/k) v)) (z : v.adicCompletion K) :
    Valued.v (σ • z) = Valued.v z :=
  valued_adicCompletionAut v σ.1 (mem_stabilizer_iff.mp σ.2) z

/-- The decomposition group preserves the ring of integers of the completion. -/
theorem smul_mem_adicCompletionIntegers (σ : ↥(stabilizer Gal(K/k) v))
    {z : v.adicCompletion K} (hz : z ∈ v.adicCompletionIntegers K) :
    σ • z ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_stabilizer_smul]
  exact hz

end Decomposition

end InverseGalois.CFT
