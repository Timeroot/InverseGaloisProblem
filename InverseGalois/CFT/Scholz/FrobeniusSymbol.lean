/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Cyclotomic.Chebotarev
import InverseGalois.CFT.InertiaSubgroup
import InverseGalois.CFT.Scholz.ResidueSymbol

/-!
# The character cut out by a power residue symbol

A character `κ` of the units modulo `Q` with values in a cyclic group of order `ℓ` becomes a
character of the Galois group of any number field containing the `Q`-th roots of unity: restrict an
automorphism to the cyclotomic subfield, read it as a unit modulo `Q`, and apply `κ`.  Two
properties of this character are what the residue correction of the Scholz–Reichardt construction
needs.

At a prime `p` not dividing `Q` the value of the character on an arithmetic Frobenius is the power
residue symbol of `p`, by the reciprocity law for the rational field.  At such a prime the character
also kills the inertia subgroup, because `p` is unramified in the cyclotomic subfield.  So the
character changes the Frobenius by a prescribed amount and leaves the ramification untouched.

## Main results

* `InverseGalois.CFT.restrictNormalHom_eq_one_of_mem_inertia`: inertia at a prime unramified in a
  normal subextension restricts to the identity on that subextension.
* `InverseGalois.CFT.map_galEquivZMod_restrictNormal_of_isArithFrobAt`: **the value of the character
  on an arithmetic Frobenius at a prime not dividing the modulus is the power residue symbol of that
  prime.**

## Tags

power residue symbol, Frobenius, cyclotomic field, reciprocity, inertia subgroup
-/

open NumberField InverseGalois.NumberTheory IsCyclotomicExtension

namespace InverseGalois.CFT

variable {M : Type*} [Field M] [NumberField M] [IsGalois ℚ M] {p : ℕ}

/-- **Inertia at a prime unramified in a normal subextension restricts to the identity there.** -/
theorem restrictNormalHom_eq_one_of_mem_inertia (C : IntermediateField ℚ M) [Normal ℚ ↥C]
    (hp : p.Prime) (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hC : p ∉ ramifiedSet ↥C) {σ : Gal(M/ℚ)} (hσ : σ ∈ Ideal.inertia Gal(M/ℚ) P) :
    AlgEquiv.restrictNormalHom ↥C σ = 1 := by
  haveI : IsGalois ℚ ↥C := ⟨⟩
  haveI := liesOver_under_intermediateField (p := p) C P
  have hmem := restrictNormal_mem_inertia C P hσ
  rw [inertia_eq_bot_of_notMem_ramifiedSet hp (P.under (𝓞 ↥C)) hC] at hmem
  simpa using hmem

/-- **The character reads the power residue symbol off an arithmetic Frobenius.**  At a rational
prime not dividing the modulus, the restriction of an arithmetic Frobenius to the cyclotomic
subfield is the class of the prime in the units modulo the modulus, so the character takes the value
recorded by the power residue symbol. -/
theorem map_galEquivZMod_restrictNormal_of_isArithFrobAt {Q ℓ : ℕ} [NeZero Q]
    (C : IntermediateField ℚ M) [IsCyclotomicExtension {Q} ℚ ↥C] [Normal ℚ ↥C]
    (κ : (ZMod Q)ˣ →* Multiplicative (ZMod ℓ)) (hp : p.Prime) (hpQ : ¬ p ∣ Q) (P : Ideal (𝓞 M))
    [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] {σ : Gal(M/ℚ)} (hσ : IsArithFrobAt ℤ σ P) :
    κ (Rat.galEquivZMod Q ↥C (AlgEquiv.restrictNormalHom ↥C σ)) =
      Multiplicative.ofAdd (powerResidueSymbol κ p) := by
  haveI := liesOver_under_intermediateField (p := p) C P
  have hunder : (P.under (𝓞 ↥C)).under ℤ = Ideal.span {(p : ℤ)} :=
    (Ideal.over_def (P.under (𝓞 ↥C)) (Ideal.span {(p : ℤ)})).symm
  rw [galEquivZMod_eq_of_isArithFrobAt hp hpQ (P.under (𝓞 ↥C)) hunder _
    (isArithFrobAt_restrictNormal C σ P hσ)]
  have hu : IsUnit ((p : ZMod Q)) :=
    ⟨ZMod.unitOfCoprime p (coprime_of_prime_not_dvd Q hp hpQ), ZMod.coe_unitOfCoprime _ _⟩
  rw [powerResidueSymbol, dif_pos hu]
  exact congrArg κ (Units.ext (by rw [ZMod.coe_unitOfCoprime, hu.unit_spec]))

end InverseGalois.CFT
