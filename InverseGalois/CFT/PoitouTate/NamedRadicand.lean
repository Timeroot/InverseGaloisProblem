/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.InvariantRadicand

/-!
# An invariant radicand prescribed at several named places

A prescription names not one place but a finite family of them, lying in distinct orbits, and asks
for a single radicand whose value is the prescribed one at each.  The one orbit descent answers
each demand separately, and the answers are **added**: the divisors carried by distinct orbits have
disjoint supports, so the sum of the radicands has the prescribed value at every named place and no
value at all away from the named orbits.

Nothing is lost in the addition, because invariance is preserved by it and the divisor of a sum is
the sum of the divisors.  This file records the assembly, for an arbitrary group carrying an
equivariant valuation and for the confined units of a number field.

## Main results

* `InverseGalois.CFT.exists_invariant_tensorVal_eq_of_named`: **an invariant tensor whose value is
  the prescribed one at each of finitely many places in distinct orbits, and zero away from their
  orbits.**
* `InverseGalois.CFT.exists_invariant_confinedTensorVal_eq_of_named`: the same for the units of a
  number field which are local powers at one set of places and have order divisible by the exponent
  outside another.

## Tags

number field, S-unit, tensor product, divisor, orbit, descent, group cohomology
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace InverseGalois.CFT

open CategoryTheory IsDedekindDomain MulAction NumberField TensorProduct groupCohomology

/-! ### The values of the divisor carried by one orbit -/

section Values

variable (Q : Type*) [Group Q] [Finite Q] {X : Type*} [MulAction Q X]
variable {C : Type*} [CommGroup C] [MulDistribMulAction Q C]

/-- The divisor carried by one orbit has no value away from that orbit. -/
theorem orbitRadicand_apply_of_notMem (x₀ : X) (V : C) {x : X} (hx : x ∉ orbit Q x₀) :
    orbitRadicand Q x₀ V x = 0 :=
  letI : DistribMulAction Q (Additive C) := additiveDistribMulAction Q C
  orbitDivisor_apply_of_notMem Q x₀ (Additive.ofMul V) hx

/-- The value of the divisor carried by one orbit at the chosen place is the chosen value. -/
theorem orbitRadicand_apply_self (x₀ : X) (V : C) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V) :
    orbitRadicand Q x₀ V x₀ = Additive.ofMul V := by
  letI : DistribMulAction Q (Additive C) := additiveDistribMulAction Q C
  have h := orbitDivisor_apply_smul Q x₀ (Additive.ofMul V)
    (fun s hs => congrArg Additive.ofMul (hV s hs)) 1
  simpa using h

end Values

/-! ### The radicand prescribed at several places -/

section Named

variable {Q : Type} [Group Q] [Finite Q] {A : Type} [CommGroup A] [MulDistribMulAction Q A]
variable {C C' : Type} [CommGroup C] [CommGroup C'] [MulDistribMulAction Q C]
  [MulDistribMulAction Q C']
variable {X : Type} [MulAction Q X] [DecidableEq X]
variable (g : Additive A →+ (X →₀ ℤ)) (B : Subgroup A) [IsStableSubgroup Q B]

/-- **An invariant tensor whose value is the prescribed one at each of finitely many places lying
in distinct orbits, and zero away from their orbits.**  Each demand is answered on its own orbit by
the one orbit descent, and the answers are added: invariance survives the addition, and the
divisors carried by distinct orbits have disjoint supports, so no demand disturbs another. -/
theorem exists_invariant_tensorVal_eq_of_named
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (φ : C →* C') (hφ : ∀ (σ : Q) (w : C), φ (σ • w) = σ • φ w)
    (hkill : ∀ w : H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)),
      (groupCohomology.map (MonoidHom.id Q) (tensorCoeffRep (A := ↥B) Q φ hφ) 1).hom w = 0)
    {ι : Type} [Fintype ι] (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) :
    ∃ s : Additive A ⊗[ℤ] Additive C',
      (∀ σ : Q, σ • s = s) ∧
      (∀ μ : ι, tensorVal C' g s (x μ) = Additive.ofMul (φ (V μ))) ∧
      ∀ z : X, (∀ μ : ι, z ∉ orbit Q (x μ)) → tensorVal C' g s z = 0 := by
  choose s hs hsval using fun μ : ι =>
    exists_invariant_tensorVal_eq_orbitRadicand_of_kill g B hg hB hgeq φ hφ hkill (x μ) (V μ)
      (hV μ)
  have hzero : ∀ (μ : ι) (z : X), z ∉ orbit Q (x μ) → tensorVal C' g (s μ) z = 0 := by
    intro μ z hz
    rw [hsval μ z, orbitRadicand_apply_of_notMem Q (x μ) (V μ) hz, _root_.toMul_zero,
      _root_.map_one, _root_.ofMul_one]
  refine ⟨∑ μ : ι, s μ, fun σ => ?_, fun ν => ?_, fun z hz => ?_⟩
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun μ _ => hs μ σ
  · rw [_root_.map_sum, Finset.sum_apply']
    refine (Finset.sum_eq_single ν (fun μ _ hμ => hzero μ (x ν) (hdisj ν μ (Ne.symm hμ)))
      (fun hν => absurd (Finset.mem_univ ν) hν)).trans ?_
    rw [hsval ν (x ν), orbitRadicand_apply_self Q (x ν) (V ν) (hV ν)]
    rfl
  · rw [_root_.map_sum, Finset.sum_apply']
    exact Finset.sum_eq_zero fun μ _ => hzero μ z (hz μ)

/-- **An invariant tensor prescribed at finitely many places in distinct orbits, with the
prescribed values read in the module itself.**  When the first cohomology of the group with
coefficients in the kernel of the valuation tensored with the module already vanishes, no shrinking
is needed and the values are the prescribed ones on the nose. -/
theorem exists_invariant_tensorVal_eq_of_named_of_h1
    (hg : Function.Surjective g) (hB : ∀ a : A, a ∈ B ↔ g (Additive.ofMul a) = 0)
    (hgeq : ∀ (σ : Q) (a : A) (x : X),
      g (Additive.ofMul (σ • a)) x = g (Additive.ofMul a) (σ⁻¹ • x))
    (hH1 : ∀ w : H1 (Rep.ofDistribMulAction ℤ Q (Additive ↥B ⊗[ℤ] Additive C)), w = 0)
    {ι : Type} [Fintype ι] (x : ι → X) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Q (x μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → x μ ∉ orbit Q (x ν)) :
    ∃ s : Additive A ⊗[ℤ] Additive C,
      (∀ σ : Q, σ • s = s) ∧
      (∀ μ : ι, tensorVal C g s (x μ) = Additive.ofMul (V μ)) ∧
      ∀ z : X, (∀ μ : ι, z ∉ orbit Q (x μ)) → tensorVal C g s z = 0 :=
  exists_invariant_tensorVal_eq_of_named g B hg hB hgeq (MonoidHom.id C) (fun _ _ => rfl)
    (fun w => by rw [hH1 w, _root_.map_zero]) x V hV hdisj

end Named

/-! ### The confined units of a number field -/

section Confined

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (n : ℕ) (Tz Y Xs : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite ↥Xs] [DecidableEq ↥Xs]
variable [IsGaloisStablePlaces k K Tz] [IsGaloisStablePlaces k K Y]
  [IsGaloisStablePlaces k K Xs]
variable {C C' : Type} [CommGroup C] [CommGroup C']
  [MulDistribMulAction Gal(K/k) C] [MulDistribMulAction Gal(K/k) C']

/-- **An invariant radicand of confined units whose value is the prescribed one at each of finitely
many named places lying in distinct orbits.**  The named places are asked to be among those the
valuation is read at, the prescribed value at each is asked to be fixed by the automorphisms fixing
that place, and nothing else is asked beyond the surjectivity of the valuation and the shrinking of
the module of coefficients. -/
theorem exists_invariant_confinedTensorVal_eq_of_named
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (φ : C →* C') (hφ : ∀ (σ : Gal(K/k)) (w : C), φ (σ • w) = σ • φ w)
    (hkill : ∀ w : H1 (Rep.ofDistribMulAction ℤ Gal(K/k)
        (Additive ↥(confinedSUnits n Tz Y Xs) ⊗[ℤ] Additive C)),
      (groupCohomology.map (MonoidHom.id Gal(K/k))
        (tensorCoeffRep (A := ↥(confinedSUnits n Tz Y Xs)) Gal(K/k) φ hφ) 1).hom w = 0)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C',
      (∀ σ : Gal(K/k), σ • s = s) ∧
      (∀ μ : ι, tensorVal C' (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (φ (V μ))) ∧
      ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
        tensorVal C' (confinedOrd n Tz Y Xs) s z = 0 :=
  exists_invariant_tensorVal_eq_of_named (confinedOrd n Tz Y Xs) (confinedSUnits n Tz Y Xs)
    hsurj (mem_confinedSUnits_iff n Tz Y Xs) (confinedOrd_smul_apply n Tz Y Xs) φ hφ hkill w V
    hV hdisj

/-- **An invariant radicand of confined units with the prescribed values read in the module
itself.**  The named places are enlarged until the units without order at them, tensored with the
module, carry no first cohomology; then the descent costs nothing beyond the surjectivity of the
vector of orders, and the prescribed values are realised on the nose. -/
theorem exists_invariant_confinedTensorVal_eq_of_named_of_h1
    (hsurj : Function.Surjective (confinedOrd n Tz Y Xs))
    (hH1 : ∀ w : H1 (Rep.ofDistribMulAction ℤ Gal(K/k)
      (Additive ↥(confinedSUnits n Tz Y Xs) ⊗[ℤ] Additive C)), w = 0)
    {ι : Type} [Fintype ι] (w : ι → ↥Xs) (V : ι → C)
    (hV : ∀ μ : ι, ∀ s ∈ stabilizer Gal(K/k) (w μ), s • V μ = V μ)
    (hdisj : ∀ μ ν : ι, μ ≠ ν → w μ ∉ orbit Gal(K/k) (w ν)) :
    ∃ s : Additive ↥(confinedUnits K n Tz Y) ⊗[ℤ] Additive C,
      (∀ σ : Gal(K/k), σ • s = s) ∧
      (∀ μ : ι, tensorVal C (confinedOrd n Tz Y Xs) s (w μ) = Additive.ofMul (V μ)) ∧
      ∀ z : ↥Xs, (∀ μ : ι, z ∉ orbit Gal(K/k) (w μ)) →
        tensorVal C (confinedOrd n Tz Y Xs) s z = 0 :=
  exists_invariant_tensorVal_eq_of_named_of_h1 (confinedOrd n Tz Y Xs)
    (confinedSUnits n Tz Y Xs) hsurj (mem_confinedSUnits_iff n Tz Y Xs)
    (confinedOrd_smul_apply n Tz Y Xs) hH1 w V hV hdisj

end Confined

end InverseGalois.CFT
