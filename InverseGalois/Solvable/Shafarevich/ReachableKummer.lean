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

end Kummer

end InverseGalois.Shafarevich
