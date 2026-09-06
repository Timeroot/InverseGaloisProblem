/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.LocalPower
import InverseGalois.CFT.Units.HasseTwoDecomposition

/-!
# Reading a local `p`-th power off a decomposition subgroup of an arbitrary extension

Let `Ω` be an arbitrary Galois extension of a number field containing a primitive `p`-th root of
unity, let `b` be an element of `Ω` whose `p`-th power `a` lies in the base field, and let `P` be a
nonzero prime of the integers of `Ω`, or an archimedean place of `Ω`.  If the decomposition subgroup
there fixes `b`, then `a` is a `p`-th power in the completion of the base field at the place below.

The criterion for an extension of number fields is the local form of Kummer theory, and the passage
to an arbitrary extension is a descent to a level.  The radical generates a finite Galois
subextension; the place of that level below the given prime carries a decomposition group onto which
the decomposition subgroup above maps, so an automorphism of the level fixing that place is the
restriction of an automorphism fixing the prime and therefore fixes the radical.  The place of the
base field below the place of the level is the place of the base field below the given one, so the
completion in which the root is found is the intended one.

The statement is the arithmetic half of the comparison between the two readings of a local
condition on a cohomology class: the profinite reading, that the class dies on a decomposition
subgroup, and the idelic one, that it dies in the units of a completion.

## Main results

* `InverseGalois.CFT.exists_isGalois_level_mem`: **every element of a Galois extension lies in a
  finite Galois level.**
* `InverseGalois.CFT.exists_pow_adicCompletion_of_forall_stabilizer_smul_eq`: **the decomposition
  subgroup at a nonzero prime of the integers of an arbitrary Galois extension fixes a radical only
  if the radicand is a `p`-th power in the completion of the base field below.**
* `InverseGalois.CFT.exists_pow_infiniteCompletion_of_forall_stabilizer_smul_eq`: **the same at an
  archimedean place.**

## Tags

number field, infinite Galois theory, decomposition group, Kummer theory, local power, completion
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### A finite Galois level containing an element -/

section Level

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

variable (k) in
/-- **Every element of a Galois extension lies in a finite Galois level**: the normal closure of the
subfield it generates is finite over the base field and Galois over it. -/
theorem exists_isGalois_level_mem (b : Ω) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k ↥L ∧ IsGalois k ↥L ∧ b ∈ L := by
  refine ⟨(FiniteGaloisIntermediateField.adjoin k ({b} : Set Ω)).toIntermediateField, ?_, ?_, ?_⟩
  · exact (FiniteGaloisIntermediateField.adjoin k ({b} : Set Ω)).finiteDimensional
  · exact (FiniteGaloisIntermediateField.adjoin k ({b} : Set Ω)).isGalois
  · exact FiniteGaloisIntermediateField.subset_adjoin k ({b} : Set Ω) rfl

end Level

/-! ### The finite places -/

section FiniteLevelPower

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {p : ℕ}

/-- **The decomposition subgroup at a nonzero prime of the integers of an arbitrary Galois extension
fixes a radical only if the radicand is a `p`-th power in the completion of the base field below**,
the base field containing the `p`-th roots of unity.  The radical lies in a finite Galois level, the
decomposition group of the level at the place below the prime is the image of the decomposition
subgroup, and the criterion for an extension of number fields applies at that level. -/
theorem exists_pow_adicCompletion_of_forall_stabilizer_smul_eq {P : Ideal (𝓞 Ω)} [P.IsPrime]
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0) {b : Ω} {a : k}
    (ha : algebraMap k Ω a = b ^ p)
    (hfix : ∀ σ : ↥(stabilizer Gal(Ω/k) P), (σ : Gal(Ω/k)) b = b)
    {v : HeightOneSpectrum (𝓞 k)} (hv : v.asIdeal = Ideal.under (𝓞 k) P) :
    ∃ c : v.adicCompletion k, c ^ p = algebraMap k (v.adicCompletion k) a := by
  obtain ⟨L, hLfin, hLgal, hbL⟩ := exists_isGalois_level_mem k b
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  have hunder : Ideal.under (𝓞 k) (Ideal.under (𝓞 ↥L) P) = v.asIdeal := by
    rw [Ideal.under_under, hv]
  have hbot : Ideal.under (𝓞 ↥L) P ≠ ⊥ := by
    intro h
    refine v.ne_bot ?_
    rw [← hunder, h, Ideal.under_def, ← RingHom.ker_eq_comap_bot,
      RingOfIntegers.ker_algebraMap_eq_bot]
  haveI : (Ideal.under (𝓞 ↥L) P).IsPrime := Ideal.IsPrime.under _ P
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 ↥L), w.asIdeal = Ideal.under (𝓞 ↥L) P :=
    ⟨⟨Ideal.under (𝓞 ↥L) P, inferInstance, hbot⟩, rfl⟩
  have hbb : (algebraMap (↥L) Ω) (⟨b, hbL⟩ : ↥L) = b := rfl
  have haL : algebraMap k ↥L a = (⟨b, hbL⟩ : ↥L) ^ p := by
    refine (algebraMap (↥L) Ω).injective ?_
    rw [← IsScalarTower.algebraMap_apply k ↥L Ω, map_pow, hbb, ha]
  have hfixL : ∀ τ : ↥(stabilizer Gal(↥L/k) w), (τ : Gal(↥L/k)) ⟨b, hbL⟩ = ⟨b, hbL⟩ := by
    intro τ
    obtain ⟨σ, rfl⟩ := stabilizerRestrictPrime_surjective L hw τ
    refine Subtype.ext ?_
    rw [coe_stabilizerRestrictPrime, AlgEquiv.restrictNormalHom_apply]
    exact hfix σ
  obtain ⟨c, hc⟩ := (forall_stabilizer_smul_eq_iff_exists_pow w hζ hp haL).1 hfixL
  have hveq : primeUnder (𝓞 k) w = v :=
    HeightOneSpectrum.ext (by rw [primeUnder_asIdeal, hw, hunder])
  subst hveq
  exact ⟨c, hc⟩

end FiniteLevelPower

/-! ### The infinite places -/

section InfiniteLevelPower

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] {p : ℕ}

/-- **The decomposition subgroup at an archimedean place of an arbitrary Galois extension fixes a
radical only if the radicand is a `p`-th power in the completion of the base field below**, the base
field containing the `p`-th roots of unity.  The radical lies in a finite Galois level, the
decomposition group of the level at the place below is the image of the decomposition subgroup, and
the criterion for an extension of number fields applies at that level. -/
theorem exists_pow_infiniteCompletion_of_forall_stabilizer_smul_eq {W : InfinitePlace Ω}
    {ζ : k} (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 0) {b : Ω} {a : k}
    (ha : algebraMap k Ω a = b ^ p)
    (hfix : ∀ σ : ↥(stabilizer Gal(Ω/k) W), (σ : Gal(Ω/k)) b = b)
    {u : InfinitePlace k} (hu : u = W.comap (algebraMap k Ω)) :
    ∃ c : u.Completion, c ^ p = algebraMap k u.Completion a := by
  obtain ⟨L, hLfin, hLgal, hbL⟩ := exists_isGalois_level_mem k b
  haveI := hLfin
  haveI := hLgal
  haveI : NumberField ↥L := NumberField.of_module_finite k ↥L
  obtain ⟨v, hvdef⟩ : ∃ v : InfinitePlace ↥L, v = W.comap (algebraMap ↥L Ω) := ⟨_, rfl⟩
  have hbb : (algebraMap (↥L) Ω) (⟨b, hbL⟩ : ↥L) = b := rfl
  have haL : algebraMap k ↥L a = (⟨b, hbL⟩ : ↥L) ^ p := by
    refine (algebraMap (↥L) Ω).injective ?_
    rw [← IsScalarTower.algebraMap_apply k ↥L Ω, map_pow, hbb, ha]
  have hfixL : ∀ τ : ↥(stabilizer Gal(↥L/k) v), (τ : Gal(↥L/k)) ⟨b, hbL⟩ = ⟨b, hbL⟩ := by
    intro τ
    obtain ⟨σ, rfl⟩ := stabilizerRestrictInfinitePlace_surjective L hvdef τ
    refine Subtype.ext ?_
    rw [coe_stabilizerRestrictInfinitePlace, AlgEquiv.restrictNormalHom_apply]
    exact hfix σ
  obtain ⟨c, hc⟩ := (forall_stabilizer_smul_eq_iff_exists_pow_infinite v hζ hp haL).1 hfixL
  have hvu : v.comap (algebraMap k ↥L) = u := by
    rw [hvdef, ← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq, hu]
  subst hvu
  exact ⟨c, hc⟩

end InfiniteLevelPower

end InverseGalois.CFT
