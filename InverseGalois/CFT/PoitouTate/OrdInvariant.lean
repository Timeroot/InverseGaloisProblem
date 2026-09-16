/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.OrbitDivisor
import InverseGalois.CFT.PoitouTate.TensorInvariant
import InverseGalois.CFT.PoitouTate.TensorOrbit
import InverseGalois.CFT.Units.OrdFinsupp

/-!
# The order vector of a number field as an equivariant valuation

The abstract descent asks for an abelian group carrying an equivariant valuation onto the free
abelian group on a permuted set of places, whose kernel is the coefficient group of the
obstruction.  For a number field the group is the units of the field, the places are the primes
outside a finite set stable under the Galois group, the valuation is the vector of orders, and its
kernel is the group of units for that set.

Everything asked for is already available: the order vector is **onto** once the set carries the
ideal classes, it is **equivariant** because an automorphism moves the order of an element along
the permutation it induces on the primes, and its **kernel** is the group of units for the set.
This file records the three facts in the form the descent consumes, in terms of the action of the
Galois group on the units rather than of the additive automorphism it induces.

## Main results

* `InverseGalois.CFT.ordFinsupp_smul_apply`: **the order vector is equivariant**, in the pointwise
  form the descent asks for.
* `InverseGalois.CFT.mem_sUnits_iff_ordFinsupp_eq_zero`: **the kernel of the order vector is the
  group of units for the set.**
* `InverseGalois.CFT.exists_tensorVal_eq_orbitRadicand`: **a tensor realising the divisor carried
  by one orbit, whose valuation is automatically invariant**, so that it feeds the descent with no
  further hypothesis.

## Tags

number field, height one prime, order, S-unit, Galois action, valuation, descent
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField TensorProduct Rigidity.RET

section Ord

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [NumberField K]
variable (T : Set (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in
/-- The action of an automorphism on a unit of the field is the action on the field itself. -/
theorem coe_galSMul_units (σ : Gal(K/k)) (a : Kˣ) : ((σ • a : Kˣ) : K) = σ (a : K) := rfl

omit [NumberField K] in
/-- The additive automorphism of the units induced by an automorphism of the field is the action
of that automorphism. -/
theorem globalUnitsAut_ofMul (σ : Gal(K/k)) (a : Kˣ) :
    globalUnitsAut σ (Additive.ofMul a) = Additive.ofMul (σ • a) :=
  Additive.toMul.injective (Units.ext rfl)

variable [IsGaloisStablePlaces k K T]

/-- **The order vector is equivariant**: the order of a translated unit at a translated prime is
the order of the unit at the prime. -/
theorem ordFinsupp_smul_apply (σ : Gal(K/k)) (a : Kˣ)
    (y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) :
    ordFinsupp T (Additive.ofMul (σ • a)) (σ • y) = ordFinsupp T (Additive.ofMul a) y := by
  rw [← globalUnitsAut_ofMul, ordFinsupp_globalUnitsAut, inv_smul_smul]

/-- **The kernel of the order vector is the group of units for the set.** -/
theorem mem_sUnits_iff_ordFinsupp_eq_zero (a : Kˣ) :
    a ∈ sUnits K T ↔ ordFinsupp T (Additive.ofMul a) = 0 :=
  (mem_ker_ordFinsupp T (u := Additive.ofMul a)).symm.trans AddMonoidHom.mem_ker

/-- **The group of units for a stable set of primes is carried into itself by the Galois
group.** -/
instance isStableSubgroup_sUnits : IsStableSubgroup Gal(K/k) (sUnits K T) where
  smul_mem σ {a} ha := by
    refine (mem_sUnits_iff_ordFinsupp_eq_zero T (σ • a)).2 (Finsupp.ext fun y => ?_)
    have h := ordFinsupp_smul_apply T σ a (σ⁻¹ • y)
    rw [smul_inv_smul, (mem_sUnits_iff_ordFinsupp_eq_zero T a).1 ha] at h
    simpa using h

end Ord

/-! ### The divisor carried by one orbit, realised by a tensor -/

section Radicand

variable (Q : Type*) [Group Q] [Finite Q] {X : Type*} [MulAction Q X]
variable {C : Type*} [CommGroup C] [MulDistribMulAction Q C]

/-- **The divisor carried by one orbit**, written for a module in multiplicative notation: at a
translate of the chosen place it is the corresponding translate of the chosen value. -/
noncomputable def orbitRadicand (x₀ : X) (V : C) : X →₀ Additive C :=
  letI : DistribMulAction Q (Additive C) := additiveDistribMulAction Q C
  orbitDivisor Q x₀ (Additive.ofMul V)

/-- **The divisor carried by one orbit is equivariant**, in the pointwise form the descent asks
for. -/
theorem orbitRadicand_smul_apply (x₀ : X) (V : C) (hV : ∀ s ∈ stabilizer Q x₀, s • V = V)
    (σ : Q) (x : X) :
    orbitRadicand Q x₀ V (σ • x) = Additive.ofMul (σ • (orbitRadicand Q x₀ V x).toMul) :=
  letI : DistribMulAction Q (Additive C) := additiveDistribMulAction Q C
  orbitDivisor_smul_apply Q x₀ (Additive.ofMul V)
    (fun s hs => congrArg Additive.ofMul (hV s hs)) σ x

end Radicand

/-! ### The realisation -/

section Realise

variable {k K : Type} [Field k] [Field K] [Algebra k K] [NumberField K] [Finite Gal(K/k)]
variable (T : Set (HeightOneSpectrum (𝓞 K))) [IsGaloisStablePlaces k K T]
variable [DecidableEq {v : HeightOneSpectrum (𝓞 K) // v ∉ T}]
variable (C : Type) [CommGroup C] [MulDistribMulAction Gal(K/k) C]

/-- **A tensor realising the divisor carried by one orbit, whose valuation is invariant.**  The
order vector is onto once the set of primes carries the ideal classes, so the divisor is realised;
it is equivariant, and the divisor carried by an orbit is equivariant, so the valuation of the
tensor is invariant with no further hypothesis. -/
theorem exists_tensorVal_eq_orbitRadicand (hT : Function.Surjective (ordFinsupp T))
    (w : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (V : C)
    (hV : ∀ s ∈ stabilizer Gal(K/k) w, s • V = V) :
    ∃ t : Additive Kˣ ⊗[ℤ] Additive C,
      tensorVal C (ordFinsupp T) t = orbitRadicand Gal(K/k) w V ∧
      ∀ σ : Gal(K/k),
        tensorVal C (ordFinsupp T) (σ • t) = tensorVal C (ordFinsupp T) t := by
  obtain ⟨t, ht⟩ := tensorVal_surjective C (ordFinsupp T) hT (orbitRadicand Gal(K/k) w V)
  exact ⟨t, ht, tensorVal_smul_eq_of_eq C (ordFinsupp T) (ordFinsupp_smul_apply T) ht
    (orbitRadicand_smul_apply Gal(K/k) w V hV)⟩

variable (C' : Type) [CommGroup C'] [MulDistribMulAction Gal(K/k) C']

/-- **An invariant radicand realising the divisor carried by one orbit**, once the obstruction it
defines is killed by a homomorphism of the coefficient module.  The realisation is automatic and
its valuation is automatically invariant, so the whole content is the vanishing of the one class
the tensor defines with coefficients in the units for the set. -/
theorem exists_invariant_tensorVal_eq_orbitRadicand (hT : Function.Surjective (ordFinsupp T))
    (w : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}) (V : C)
    {t : Additive Kˣ ⊗[ℤ] Additive C} (ht : tensorVal C (ordFinsupp T) t
      = orbitRadicand Gal(K/k) w V)
    (hinv : ∀ σ : Gal(K/k),
      tensorVal C (ordFinsupp T) (σ • t) = tensorVal C (ordFinsupp T) t)
    (φ : C →* C') (hφ : ∀ (σ : Gal(K/k)) (x : C), φ (σ • x) = σ • φ x)
    (hzero : (groupCohomology.map (MonoidHom.id Gal(K/k))
        (tensorCoeffRep (A := ↥(sUnits K T)) Gal(K/k) φ hφ) 1).hom
      (tensorInvariantClass C (ordFinsupp T) (sUnits K T) hT
        (mem_sUnits_iff_ordFinsupp_eq_zero T) hinv) = 0) :
    ∃ s : Additive Kˣ ⊗[ℤ] Additive C',
      (∀ σ : Gal(K/k), σ • s = s) ∧
      ∀ y : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        tensorVal C' (ordFinsupp T) s y
          = Additive.ofMul (φ (orbitRadicand Gal(K/k) w V y).toMul) := by
  obtain ⟨s, hs, hsval⟩ := exists_invariant_tensorCoeff_of_map_tensorInvariantClass_eq_zero
    (ordFinsupp T) (sUnits K T) hT (mem_sUnits_iff_ordFinsupp_eq_zero T) φ hφ hinv hzero
  exact ⟨s, hs, fun y => by rw [hsval y, ht]⟩

end Realise

end InverseGalois.CFT
