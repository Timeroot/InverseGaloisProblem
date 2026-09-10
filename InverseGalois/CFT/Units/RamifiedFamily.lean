/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.OpenLevel
import InverseGalois.CFT.Units.InertiaFinite
import InverseGalois.CFT.Units.InfiniteDecomposition

/-!
# The primes at which a smooth homomorphism ramifies form finitely many orbits

A homomorphism of the Galois group of an arbitrary Galois extension of a number field into a
discrete group is smooth exactly when its kernel is open, and an open normal subgroup is the
subgroup fixing a finite Galois level.  Only finitely many places of that level ramify over the
base field, and at a prime of the big extension whose place in the level is unramified the inertia
of the big group already fixes the level, hence is killed by the homomorphism.  So the primes at
which the homomorphism ramifies lie over finitely many places of the base field, and the Galois
group acting transitively on the primes above a place, they form finitely many orbits.

Naming one prime above each of those places therefore names every prime at which the homomorphism
ramifies, up to conjugacy.  This is what turns a condition to be imposed at the primes where a
homomorphism ramifies into a condition at finitely many subgroups, the decomposition subgroups
being permuted by conjugation along with the primes.

## Main results

* `InverseGalois.CFT.mem_stabilizer_smul_iff`, `InverseGalois.CFT.mem_inertia_smul_iff`: the
  decomposition and inertia subgroups of a moved prime are the conjugates of those of the prime.
* `InverseGalois.CFT.exists_ramified_family`: **a finite family of primes containing, up to the
  action of the Galois group, every prime at which a homomorphism with open kernel ramifies.**

## Tags

class field theory, inertia, ramification, decomposition group, level, number field
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Moving a prime -/

section Conjugate

/-- The subgroup fixing a moved point is the conjugate of the subgroup fixing the point. -/
theorem mem_stabilizer_smul_iff {G α : Type*} [Group G] [MulAction G α] {a : α} {ρ x : G} :
    x ∈ stabilizer G (ρ • a) ↔ ρ⁻¹ * x * ρ ∈ stabilizer G a := by
  simp only [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]

/-- The subgroup acting trivially modulo a moved ideal is the conjugate of the subgroup acting
trivially modulo the ideal. -/
theorem mem_inertia_smul_iff {R : Type*} [CommRing R] {M : Type*} [Group M]
    [MulSemiringAction M R] {P : Ideal R} {ρ σ : M} :
    σ ∈ Ideal.inertia M (ρ • P) ↔ ρ⁻¹ * σ * ρ ∈ Ideal.inertia M P := by
  simp only [AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup]
  constructor
  · intro h y
    have hy := h (ρ • y)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa [mul_smul, smul_sub] using hy
  · intro h y
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hy := h (ρ⁻¹ • y)
    simpa [mul_smul, smul_sub] using hy

end Conjugate

/-! ### The ramified primes, up to conjugacy -/

section Ramified

variable {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  {W : Type*} [Group W]

/-- **A finite family of primes containing, up to the action of the Galois group, every prime at
which a homomorphism with open kernel ramifies.**

The kernel fixes a finite Galois level; only finitely many places of that level ramify over the
base field, and one prime of the big extension is named above each of them.  At a prime whose place
in the level does not ramify the inertia of the big group fixes the level and is therefore killed;
at a prime whose place does ramify, the named prime and the given one lie over the same prime of
the base field, so an automorphism carries one to the other. -/
theorem exists_ramified_family {f : Gal(Ω/k) →* W} (hf : IsOpenNormal f.ker) :
    ∃ (t : ℕ) (Pr : Fin t → Ideal (𝓞 Ω)), (∀ ν, (Pr ν).IsPrime) ∧ (∀ ν, Pr ν ≠ ⊥) ∧
      ∀ Q : Ideal (𝓞 Ω), Q.IsPrime → Q ≠ ⊥ → (∃ x ∈ Ideal.inertia Gal(Ω/k) Q, f x ≠ 1) →
        ∃ (ν : Fin t) (ρ : Gal(Ω/k)), Q = ρ • Pr ν := by
  classical
  obtain ⟨K, hfin, hgal, hKker, -⟩ := exists_level_fixingSubgroup_eq hf
  haveI := hfin
  haveI := hgal
  haveI : NumberField ↥K := numberField_of_finiteDimensional K
  have hXfin : {v : HeightOneSpectrum (𝓞 ↥K) | Ideal.inertia Gal(↥K/k) v.asIdeal ≠ ⊥}.Finite :=
    finite_setOf_inertia_ne_bot (k := k) (K := ↥K)
  choose Pf hPfp hPfbot hPfunder using fun v : HeightOneSpectrum (𝓞 ↥K) =>
    exists_stabilizer_prime_restrictNormalHom_eq (K := Ω) K (τ := 1) (v := v) (one_smul _ v)
  refine ⟨hXfin.toFinset.card, fun ν => Pf (hXfin.toFinset.equivFin.symm ν), fun ν => hPfp _,
    fun ν => hPfbot _, fun Q hQp hQbot hram => ?_⟩
  haveI := hQp
  haveI : (Ideal.under (𝓞 ↥K) Q).IsPrime := Ideal.IsPrime.under _ Q
  set w : HeightOneSpectrum (𝓞 ↥K) :=
    ⟨Ideal.under (𝓞 ↥K) Q, inferInstance, Ideal.under_ne_bot _ hQbot⟩ with hwdef
  have hw : w ∈ hXfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    intro hbot
    obtain ⟨x, hx, hfx⟩ := hram
    have hunr := (inertia_eq_bot_iff_isUnramifiedAt_base (k := k) (K := ↥K) w.asIdeal
      w.ne_bot).1 hbot
    have hfix := inertia_le_fixingSubgroup_of_isUnramifiedAt (k := k) (Ω := Ω) K hQbot hunr hx
    rw [hKker, MonoidHom.mem_ker] at hfix
    exact hfx hfix
  have hkk : Ideal.under (𝓞 k) (Pf w) = Ideal.under (𝓞 k) Q := by
    rw [← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) (Pf w),
      ← Ideal.under_under (A := 𝓞 k) (B := 𝓞 ↥K) Q, (hPfunder w).1]
  haveI := hPfp w
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_under_eq_ringOfIntegers (F := k) (K := Ω) (Pf w) Q hkk
  refine ⟨hXfin.toFinset.equivFin ⟨w, hw⟩, ρ, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hρ

end Ramified

end InverseGalois.CFT
