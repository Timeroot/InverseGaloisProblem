/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.CharPlace
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.PoitouTate.SplitPlaceMember
import InverseGalois.CFT.Units.RootField
import InverseGalois.CFT.Units.SplitPowNorm
import InverseGalois.Solvable.Shafarevich.KernelClauses
import InverseGalois.Solvable.Shafarevich.ReachableDetect

/-!
# Reaching every place of a level from a Kummer independence

The units of a level whose order is divisible by the exponent at every place all have an
exponent-th root in one and the same finite Galois extension of the base, the root field.  Inside
the compositum of the root field with a finite level, finitely many primes of the base splitting
completely in that level force such a root into the level as soon as the unit is a local power at
each of them.

So if the only units of the level having a root in the finite level are the exponent-th powers of
the level itself — a Kummer independence of the finite level from the root field — then those
primes detect the powers, and every place of the level is reached.  Nothing is asked of the class
group, and no unramified class field is constructed.

The passage from the compositum to the closure is by restriction: an automorphism of the closure
stabilising a prime restricts to an automorphism of the compositum stabilising the prime below,
and an automorphism of the compositum fixing the part of it lying in the finite level fixes that
level, because the level lies in the compositum.

## Main results

* `InverseGalois.Shafarevich.isReachablePlace_of_kummerDisjoint`: **every place of a level is
  reached once the only units of the level divisible by the exponent everywhere which become
  exponent-th powers in a finite level are the exponent-th powers already.**
* `InverseGalois.Shafarevich.isReachablePlace_of_inf_le`: the same with the independence read as an
  intersection with a field of roots.
* `InverseGalois.Shafarevich.exists_finite_forall_isReachablePlace`: **one finite Galois extension
  of the base, depending on the level below alone, decides the reachability of every place**.

## Tags

Shafarevich's theorem, place, Kummer theory, radical, completely split, root field
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField NumberTheory Rigidity.RET

open scoped Pointwise

section Kummer

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  [IsAlgClosed Ω]

/-- **Every place of a level is reached once the only units of the level divisible by the exponent
at every place which become exponent-th powers in a finite level are the exponent-th powers
already.**

Every such unit has a root in one fixed finite Galois extension of the base, and inside the
compositum of that extension with the finite level there are finitely many primes of the base,
splitting completely in the level and avoiding the one named, at which being a local power drives
the root into the level.  The independence then makes the unit a power, which is exactly the
detection the reachability of the named place is built from. -/
theorem isReachablePlace_of_kummerDisjoint {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    {K : IntermediateField k Ω} [NumberField ↥K] {E : IntermediateField k Ω}
    [FiniteDimensional k ↥E] [IsGalois k ↥E] (hKE : K ≤ E) {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ)
    (hdisj : ∀ u : (↥K)ˣ, (∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ placeValue v u) →
      ∀ ξ : Ω, algebraMap (↥K) Ω (u : ↥K) = ξ ^ ℓ → ξ ∈ E → ∃ z : (↥K)ˣ, u = z ^ ℓ)
    (w : HeightOneSpectrum (𝓞 ↥K)) :
    IsReachablePlace ℓ K E w := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NumberField ↥E := NumberField.of_module_finite k ↥E
  obtain ⟨M, hKM, hMfin, hMgal, hMroot⟩ := exists_isGalois_forall_exists_pow K hℓ.ne_zero
  haveI := hMfin
  haveI := hMgal
  set N₀ : IntermediateField k Ω := M ⊔ E with hN₀
  haveI : FiniteDimensional k ↥N₀ := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField ↥N₀ := NumberField.of_module_finite k ↥N₀
  haveI : Normal k ↥N₀ := by rw [hN₀]; infer_instance
  haveI : IsGalois k ↥N₀ := ⟨⟩
  have hMN : M ≤ N₀ := le_sup_left
  have hEN : E ≤ N₀ := le_sup_right
  have hKN : K ≤ N₀ := hKM.trans hMN
  letI : Algebra ↥K ↥N₀ := (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  haveI : IsScalarTower k ↥K ↥N₀ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set E' : IntermediateField k ↥N₀ := E.comap N₀.val with hE'
  let e : ↥E' ≃ₐ[k] ↥E :=
    { toFun := fun x => ⟨((x : ↥N₀) : Ω), x.2⟩
      invFun := fun y => ⟨⟨(y : Ω), hEN y.2⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : IsGalois k ↥E' := IsGalois.of_algEquiv e.symm
  haveI : FiniteDimensional k ↥E' := e.symm.toLinearEquiv.finiteDimensional
  haveI : NumberField ↥E' := NumberField.of_module_finite k ↥E'
  obtain ⟨S, hSfin, hSsplit, hforce⟩ :=
    exists_finite_splitsCompletelyIn_mem_of_forall_localPow' (K := ↥K) (N := ↥N₀) E'
      (fun x => hKE x.2) hℓ.ne_zero hζ {primeUnder (𝓞 k) w}
  have hX₀fin : {v : HeightOneSpectrum (𝓞 ↥K) | primeUnder (𝓞 k) v ∈ S}.Finite :=
    finite_setOf_primeUnder_mem (K := ↥K) k hSfin
  refine isReachablePlace_of_detecting hℓ hodd hζ w hX₀fin.toFinset ?_ ?_ ?_
  · rw [Set.Finite.mem_toFinset]
    exact fun hw => (hSsplit _ hw).1 (Finset.mem_singleton_self _)
  · intro v hv P hPprime hPbot hPunder
    rw [Set.Finite.mem_toFinset] at hv
    haveI : P.IsPrime := hPprime
    have hWS : primeUnder (𝓞 k) (placeUnder N₀ P hPbot) ∈ S := by
      have : primeUnder (𝓞 k) (placeUnder N₀ P hPbot) = primeUnder (𝓞 k) v := by
        refine HeightOneSpectrum.ext ?_
        rw [primeUnder_asIdeal, placeUnder_asIdeal, Ideal.under_under, primeUnder_asIdeal,
          ← hPunder, Ideal.under_under]
      rw [this]
      exact hv
    have hle : stabilizer Gal(↥N₀/k) (placeUnder N₀ P hPbot) ≤ E'.fixingSubgroup :=
      stabilizer_le_fixingSubgroup_of_splitsCompletelyIn E' (hSsplit _ hWS).2 rfl
    intro y hy
    have hyP : y • P = P := mem_stabilizer_iff.mp hy
    have hmem : AlgEquiv.restrictNormalHom (F := k) (K₁ := Ω) ↥N₀ y ∈
        stabilizer Gal(↥N₀/k) (placeUnder N₀ P hPbot) :=
      mem_stabilizer_iff.mpr (HeightOneSpectrum.ext (by
        rw [asIdeal_smul_placeUnder N₀ hPbot y, hyP, placeUnder_asIdeal]))
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hmem)
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxE' : (⟨x, hEN hx⟩ : ↥N₀) ∈ E' := hx
    have hstep : y.restrictNormal ↥N₀ ⟨x, hEN hx⟩ = ⟨x, hEN hx⟩ := hfix ⟨x, hEN hx⟩ hxE'
    have hcom := AlgEquiv.restrictNormal_commutes y ↥N₀ ⟨x, hEN hx⟩
    rw [hstep] at hcom
    exact hcom.symm
  · intro u hu hloc
    have hord : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ ord ↥K v (u : ↥K) := by
      intro v
      have := hu v
      rwa [placeValue_eq_neg_ord, dvd_neg] at this
    obtain ⟨y, hyM, hy⟩ := hMroot u hord
    refine hdisj u hu y hy.symm ?_
    have hξ : algebraMap (↥K) ↥N₀ (u : ↥K) = (⟨y, hMN hyM⟩ : ↥N₀) ^ ℓ := Subtype.ext hy.symm
    exact hforce (u : ↥K) ⟨y, hMN hyM⟩ hξ fun W hW => by
      refine (localClassHom_eq_one_iff_exists_pow (primeUnder (𝓞 ↥K) W) u).1 ?_
      refine hloc _ ?_
      rw [Set.Finite.mem_toFinset]
      show primeUnder (𝓞 k) (primeUnder (𝓞 ↥K) W) ∈ S
      have : primeUnder (𝓞 k) (primeUnder (𝓞 ↥K) W) = primeUnder (𝓞 k) W :=
        HeightOneSpectrum.ext (by
          rw [primeUnder_asIdeal, primeUnder_asIdeal, primeUnder_asIdeal, Ideal.under_under])
      rw [this]
      exact hW

/-- **A level meeting a field of roots only in the level below reaches every one of its places.**

An exponent-th root of a unit divisible by the exponent everywhere differs from a root lying in the
field of roots by a root of unity of the level below, so it lies in that field as well; lying also
in the level, it lies in the intersection, which is the level below, and the unit is a power
there. -/
theorem isReachablePlace_of_inf_le {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    {K : IntermediateField k Ω} [NumberField ↥K] {E M : IntermediateField k Ω}
    [FiniteDimensional k ↥E] [IsGalois k ↥E] (hKE : K ≤ E) (hKM : K ≤ M) {ζ : ↥K}
    (hζ : IsPrimitiveRoot ζ ℓ)
    (hM : ∀ u : (↥K)ˣ, (∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ ord ↥K v (u : ↥K)) →
      ∃ y ∈ M, y ^ ℓ = algebraMap (↥K) Ω (u : ↥K))
    (hEM : E ⊓ M ≤ K) (w : HeightOneSpectrum (𝓞 ↥K)) :
    IsReachablePlace ℓ K E w := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine isReachablePlace_of_kummerDisjoint hℓ hodd hKE hζ (fun u hu ξ hξ hξE => ?_) w
  have hune : algebraMap (↥K) Ω (u : ↥K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (↥K) Ω).injective).2 u.ne_zero
  have hord : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ ord ↥K v (u : ↥K) := by
    intro v
    have := hu v
    rwa [placeValue_eq_neg_ord, dvd_neg] at this
  obtain ⟨y, hyM, hy⟩ := hM u hord
  have hyne : y ≠ 0 := fun h => hune (by rw [← hy, h, zero_pow hℓ.ne_zero])
  have hxy : ξ ^ ℓ = y ^ ℓ := by rw [← hξ, hy]
  have hc : (ξ * y⁻¹) ^ ℓ = 1 := by
    rw [mul_pow, inv_pow, hxy, mul_inv_cancel₀ (pow_ne_zero _ hyne)]
  obtain ⟨i, -, hi⟩ :=
    (hζ.map_of_injective (algebraMap (↥K) Ω).injective).eq_pow_of_pow_eq_one hc
  have hξM : ξ ∈ M := by
    have hval : ξ = algebraMap (↥K) Ω (ζ : ↥K) ^ i * y := by
      rw [hi, inv_mul_cancel_right₀ hyne]
    rw [hval]
    exact mul_mem (pow_mem (hKM (ζ : ↥K).2) i) hyM
  have hξK : ξ ∈ K := hEM ⟨hξE, hξM⟩
  have hx : (⟨ξ, hξK⟩ : ↥K) ^ ℓ = (u : ↥K) := by
    refine (algebraMap (↥K) Ω).injective ?_
    rw [_root_.map_pow, hξ]
    rfl
  have hx0 : (⟨ξ, hξK⟩ : ↥K) ≠ 0 := by
    intro h
    rw [h, zero_pow hℓ.ne_zero] at hx
    exact u.ne_zero hx.symm
  exact ⟨Units.mk0 _ hx0, Units.ext (by simpa using hx.symm)⟩

/-- **One finite Galois extension of the base decides the reachability of every place of a level at
once**: any finite level meeting it only in the level below reaches all of them.

The extension is the one holding an exponent-th root of every unit divisible by the exponent at
every place, which depends on the level below alone and not on the level the confinement is read
in. -/
theorem exists_finite_forall_isReachablePlace {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (K : IntermediateField k Ω) [NumberField ↥K] {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) :
    ∃ M : IntermediateField k Ω, K ≤ M ∧ FiniteDimensional k ↥M ∧ IsGalois k ↥M ∧
      ∀ E : IntermediateField k Ω, FiniteDimensional k ↥E → IsGalois k ↥E → K ≤ E → E ⊓ M ≤ K →
        ∀ w : HeightOneSpectrum (𝓞 ↥K), IsReachablePlace ℓ K E w := by
  obtain ⟨M, hKM, hMfin, hMgal, hMroot⟩ := exists_isGalois_forall_exists_pow K hℓ.ne_zero
  refine ⟨M, hKM, hMfin, hMgal, fun E hEfin hEgal hKE hEM w => ?_⟩
  haveI := hEfin
  haveI := hEgal
  exact isReachablePlace_of_inf_le hℓ hodd hKE hKM hζ hMroot hEM w

end Kummer

end InverseGalois.Shafarevich
