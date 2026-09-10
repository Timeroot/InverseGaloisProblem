/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.KernelPrimeClass
import InverseGalois.Solvable.Shafarevich.LevelOneArith

/-!
# What the prescription asks of a homomorphism assembled out of units

The prescription of the repair asks four things of the homomorphism it wants beyond the values it
names: that it be smooth, that it die along a prescribed finite family of subgroups, that it die on
the decomposition subgroups at the primes the base realization moves the named ones to, and that it
ramify only where it is allowed to.  For a homomorphism assembled out of a family of units of the
level each of those is a statement about one unit at a time, and this file collects the three of
them which are about places rather than about roots.

Two bookkeeping facts carry the reading between the whole extension and the level.  An automorphism
lies in the kernel of the base realization exactly when it fixes the level that kernel cuts out, so
a prime whose place below has trivial decomposition group over the base has its whole decomposition
group inside that kernel — which is one half of what the confinement clause asks at a prime the
homomorphism itself brings in.  And the place below a conjugate of a prime is the conjugate of the
place below it, so the demand at the primes the base realization moves the named ones to is the
demand that the units be local powers at the proper conjugates of the named places.

The ramification clause is the third.  If the assembled homomorphism is nontrivial somewhere on the
inertia subgroup at a prime, then some unit of the family fails to have order divisible by the
exponent at the place below: were they all divisible, the homomorphism would die on inertia away
from the exponent, and above the exponent the units are local powers anyway, so it would die on the
whole decomposition subgroup.

## Main results

* `InverseGalois.Shafarevich.restrictNormalHom_eq_one_iff_mem_ker` — an automorphism lies in the
  kernel of the base realization exactly when it fixes the level that kernel cuts out.
* `InverseGalois.Shafarevich.stabilizer_le_ker_of_stabilizer_placeUnder_eq_bot` — **a prime whose
  place below has trivial decomposition group over the base has its whole decomposition group
  inside the kernel of the base realization.**
* `InverseGalois.Shafarevich.exists_not_dvd_placeValue_of_kummerKernelHom_ne_one` — **where the
  assembled homomorphism is nontrivial on inertia, some unit of the family has order not divisible
  by the exponent at the place below.**

## Tags

Shafarevich's theorem, embedding problem, decomposition group, inertia, Kummer theory
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain IntermediateField MulAction NumberField

open scoped Pointwise

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

/-! ### The kernel of the base realization and the level it cuts out -/

section Restrict

variable {k Ω U : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Group U]
  {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [Normal k ↥K]

omit [IsGalois k Ω] in
/-- **An automorphism lies in the kernel of the base realization exactly when it fixes the level
that kernel cuts out.** -/
theorem restrictNormalHom_eq_one_iff_mem_ker (hKker : K.fixingSubgroup = φ.ker) (y : Gal(Ω/k)) :
    AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y = 1 ↔ y ∈ φ.ker := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, hKker]

end Restrict

/-! ### The place of the level below a prime -/

section Under

variable {k Ω U : Type*} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Group U]
  {φ : Gal(Ω/k) →* U} (K : IntermediateField k Ω) [NumberField ↥K] [IsGalois k ↥K]

omit [IsGalois k Ω] [NumberField ↥K] in
/-- **The place of the level below a conjugate of a prime is the conjugate of the place below
it.** -/
theorem asIdeal_smul_placeUnder {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥) (ρ : Gal(Ω/k)) :
    (AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K ρ • placeUnder K P hP).asIdeal
      = Ideal.under (𝓞 ↥K) (ρ • P) := by
  rw [asIdeal_smul, placeUnder_asIdeal, under_smul_ringOfIntegers ↥K]

variable {K}

omit [IsGalois k Ω] [NumberField ↥K] in
/-- **A prime whose place below has trivial decomposition group over the base has its whole
decomposition group inside the kernel of the base realization.**  An automorphism stabilising the
prime stabilises the place below it, so it fixes the level, and fixing the level is being in the
kernel. -/
theorem stabilizer_le_ker_of_stabilizer_placeUnder_eq_bot (hKker : K.fixingSubgroup = φ.ker)
    {P : Ideal (𝓞 Ω)} [P.IsPrime] (hP : P ≠ ⊥)
    (hst : stabilizer Gal(↥K/k) (placeUnder K P hP) = ⊥) :
    stabilizer Gal(Ω/k) P ≤ φ.ker := by
  intro y hy
  rw [← restrictNormalHom_eq_one_iff_mem_ker hKker]
  have hmem : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥K y ∈
      stabilizer Gal(↥K/k) (placeUnder K P hP) := by
    refine HeightOneSpectrum.ext ?_
    rw [asIdeal_smul, placeUnder_asIdeal, ← under_smul_ringOfIntegers ↥K,
      mem_stabilizer_iff.1 hy]
  rw [hst] at hmem
  exact hmem

end Under

/-! ### Where the assembled homomorphism can ramify -/

section Ramify

variable {ℓ : ℕ} [NeZero ℓ] {k Ω U : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [Group U] {φ : Gal(Ω/k) →* U} {K : IntermediateField k Ω} [NumberField ↥K]
  {ζ : ↥K} {hζ : IsPrimitiveRoot ζ ℓ}

attribute [local instance] zmodTrivialAction

variable (hKker : K.fixingSubgroup = φ.ker)
  (hkd : IsKummerData ↥K Ω (Multiplicative (ZMod ℓ)) (zmodRootHom hζ) ℓ)
  {M : Type*} [CommGroup M] {d : ℕ} (b : Fin d → M) (hb : ∀ t, b t ^ ℓ = 1) (z : Fin d → (↥K)ˣ)

/-- **Where the assembled homomorphism is nontrivial on inertia, some unit of the family has order
not divisible by the exponent at the place below.**  Above the exponent the units of the family are
local powers, so the homomorphism dies on the whole decomposition subgroup there; away from it, a
family all of whose orders are divisible by the exponent makes the homomorphism die on inertia. -/
theorem exists_not_dvd_placeValue_of_kummerKernelHom_ne_one (hℓ : ℓ.Prime) {P : Ideal (𝓞 Ω)}
    [P.IsPrime] (hP : P ≠ ⊥)
    (hpz : ∀ (t : Fin d) (w : HeightOneSpectrum (𝓞 ↥K)), (ℓ : 𝓞 ↥K) ∈ w.asIdeal →
      localClassHom w ℓ (z t) = 1)
    {y : ↥φ.ker} (hy : (y : Gal(Ω/k)) ∈ Ideal.inertia Gal(Ω/k) P)
    (hne : kummerKernelHom hKker hkd b hb z y ≠ 1) :
    ∃ t, ¬ (ℓ : ℤ) ∣ placeValue (placeUnder K P hP) (z t) := by
  by_contra hcon
  push_neg at hcon
  by_cases hℓP : (ℓ : 𝓞 Ω) ∈ P
  · have hin : (ℓ : 𝓞 ↥K) ∈ (placeUnder K P hP).asIdeal := by
      rw [placeUnder_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hℓP
    exact hne (kummerKernelHom_eq_one_of_mem_stabilizer hKker hkd b hb z
      (w := placeUnder K P hP) rfl (fun t => hpz t _ hin)
      (Ideal.inertia_le_stabilizer P hy))
  · exact hne (kummerKernelHom_eq_one_of_mem_inertia hKker hkd b hb z hℓ hℓP
      (w := placeUnder K P hP) rfl hcon hy)

end Ramify

end InverseGalois.Shafarevich
