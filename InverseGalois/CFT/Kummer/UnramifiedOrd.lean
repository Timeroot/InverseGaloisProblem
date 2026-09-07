/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.Unramified
import InverseGalois.CFT.Units.SUnitValuation

/-!
# Radical extensions where the radicands have order a multiple of the exponent

A radical extension of number fields is unramified at a place away from the exponent at which all
the radicands are units.  The hypothesis that a radicand be a unit is stronger than it needs to be:
what matters is only the radicand modulo `p`-th powers of the base field, so it is enough that the
order of each radicand at the place below be a multiple of the exponent.

Indeed a radical may be rescaled by any nonzero scalar of the base field without changing the field
the radicals generate, and rescaling by a power of a coordinate at the place changes the order of
the radicand by the corresponding multiple of the exponent.  Choosing the power to be the order of
the radicand divided by the exponent makes the rescaled radicand a unit at the place, and the
extension is unchanged, so the criterion for units applies to it.

## Main results

* `InverseGalois.CFT.adjoin_range_div_algebraMap`: rescaling each radical by a nonzero scalar of the
  base field leaves the field the radicals generate unchanged.
* `InverseGalois.CFT.isUnramifiedAt_of_radicals_of_dvd_ord`: **a radical extension of number fields
  is unramified at every place away from the exponent at which the order of each radicand is a
  multiple of the exponent.**

## Tags

number field, Kummer theory, radical, unramified, order, uniformizer
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField Rigidity.RET

/-! ### Rescaling the radicals -/

section Rescale

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Rescaling each radical by a nonzero scalar of the base field leaves the field the radicals
generate unchanged**, since each rescaled radical is a quotient of an old one by a scalar and each
old radical is a product of a rescaled one by a scalar. -/
theorem adjoin_range_div_algebraMap {ι : Type*} (α : ι → L) (c : ι → Kˣ) :
    IntermediateField.adjoin K (Set.range fun i => α i / algebraMap K L ((c i : K)))
      = IntermediateField.adjoin K (Set.range α) := by
  have hne : ∀ i, algebraMap K L ((c i : K)) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (algebraMap K L).injective).2 (c i).ne_zero
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact div_mem (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.algebraMap_mem _ _)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hEq : α i = α i / algebraMap K L ((c i : K)) * algebraMap K L ((c i : K)) :=
      (div_mul_cancel₀ _ (hne i)).symm
    rw [hEq]
    exact mul_mem (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.algebraMap_mem _ _)

end Rescale

/-! ### Unramifiedness from the order of the radicands -/

section Radical

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {p : ℕ}

/-- **A radical extension of number fields is unramified at every place away from the exponent at
which the order of each radicand is a multiple of the exponent.**  Dividing each radical by the
power of a coordinate at the place whose exponent is the order of its radicand divided by the
exponent produces radicals generating the same extension whose radicands are units at the place,
where the criterion for units applies. -/
theorem isUnramifiedAt_of_radicals_of_dvd_ord (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {ι : Type*} {α : ι → L} {a : ι → Kˣ}
    (hpow : ∀ i, α i ^ p = algebraMap K L ((a i : K)))
    (hgen : IntermediateField.adjoin K (Set.range α) = ⊤)
    {w : HeightOneSpectrum (𝓞 L)} (hpw : (p : 𝓞 L) ∉ w.asIdeal)
    (hav : ∀ i, (p : ℤ) ∣ ord K (primeUnder (𝓞 K) w) ((a i : K))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  classical
  set v : HeightOneSpectrum (𝓞 K) := primeUnder (𝓞 K) w with hv
  obtain ⟨t, htval⟩ := v.valuation_exists_uniformizer K
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at htval
    exact WithZero.exp_ne_zero htval.symm
  have ht : ord K v t = 1 := by
    rw [valuation_eq_exp_neg_ord K v ht0] at htval
    have hlog := WithZero.exp_injective htval
    omega
  set c : ι → Kˣ := fun i => Units.mk0 t ht0 ^ (ord K v ((a i : K)) / (p : ℤ)) with hc
  have hcval : ∀ i, ((c i : K)) = t ^ (ord K v ((a i : K)) / (p : ℤ)) := by
    intro i
    rw [hc]
    simp
  have hcord : ∀ i, ord K v ((c i : K)) = ord K v ((a i : K)) / (p : ℤ) := by
    intro i
    rw [hcval i, ord_zpow v ht0, ht, mul_one]
  refine isUnramifiedAt_of_radicals hp hζ (α := fun i => α i / algebraMap K L ((c i : K)))
    (a := fun i => ((a i / c i ^ p : Kˣ) : K)) (fun i => ?_) ?_ hpw fun i => ?_
  · have hval : ((a i / c i ^ p : Kˣ) : K) = (a i : K) / ((c i : K)) ^ p := by
      simp
    dsimp only
    rw [div_pow, hpow i, hval, map_div₀, map_pow]
  · rw [adjoin_range_div_algebraMap]
    exact hgen
  · dsimp only
    rw [valuation_eq_one_iff_ord_eq_zero v (Units.ne_zero _)]
    have hval : ((a i / c i ^ p : Kˣ) : K) = (a i : K) / ((c i : K)) ^ p := by
      simp
    rw [hval, ord_div v (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _)),
      ord_pow v (Units.ne_zero _), hcord i, Int.mul_ediv_cancel' (hav i), sub_self]

end Radical

end InverseGalois.CFT
