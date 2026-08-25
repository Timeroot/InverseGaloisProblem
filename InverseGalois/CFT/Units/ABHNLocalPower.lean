/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNCoboundary
import InverseGalois.CFT.GroupCohomology.CyclicSubgroup

/-!
# The local condition of the Albert-Brauer-Hasse-Noether theorem at a place where the values are
local powers

The Albert-Brauer-Hasse-Noether theorem reduces a two-cocycle with values in the units of the base
field to a condition at the ramified finite places: there the cocycle must already be a coboundary
for the decomposition group, with values in the units of the completion.  This file discharges that
condition in the situation an embedding problem produces.

The cocycle takes its values in the roots of unity of the base field, and the decomposition group
fixes them.  When the decomposition group is cyclic, its norm is therefore the power with exponent
the order of the group, so the local condition holds as soon as every such root of unity is, in the
completion, a power with that exponent of a unit fixed by the decomposition group.  Nothing about
the local reciprocity law is needed.

This is exactly the arithmetic input in the Scholz-Reichardt construction: a place whose residue
characteristic is congruent to one modulo a large enough power of the prime already contains the
roots of unity to a matching height, so a root of unity of small order is locally a power of high
exponent even though it is not one globally.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_exists_pow`: **at a finite place with cyclic
  decomposition group, a two-cocycle with values in the units of the base field is a coboundary as
  soon as each of its values is locally a power, with exponent the order of the decomposition
  group, of a unit fixed by that group.**
* `InverseGalois.CFT.exists_isMulCoboundary_of_odd_of_forall_exists_pow`: the resulting form of the
  Albert-Brauer-Hasse-Noether theorem, whose only remaining hypothesis is that local one.

## Tags

number field, Albert-Brauer-Hasse-Noether, decomposition group, coboundary, roots of unity
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [IsGalois k K] in
/-- **At a finite place with cyclic decomposition group, a two-cocycle with values in the units of
the base field is a coboundary as soon as each of its values is locally a power, with exponent the
order of the decomposition group, of a unit fixed by that group.**  The values of the cocycle come
from the base field, so the decomposition group fixes them and the norm of a fixed unit is its
power with that exponent; the second cohomology of a cyclic group is the invariants modulo the
norms, and only the values of the cocycle have to be norms. -/
theorem exists_sub_add_eq_adicUnits_of_exists_pow (v : HeightOneSpectrum (𝓞 K))
    {g : ↥(stabilizer Gal(K/k) v)} (hg : ∀ x : ↥(stabilizer Gal(K/k) v), x ∈ Subgroup.zpowers g)
    {n : ℕ} {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hroot : ∀ z : kˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
      (∀ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K) = y) ∧
        y ^ Nat.card ↥(stabilizer Gal(K/k) v)
          = adicUnitHom v (Units.map (algebraMap k K : k →* K) z)) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  haveI : Fintype ↥(stabilizer Gal(K/k) v) := Fintype.ofFinite _
  set A : AddSubgroup (Additive (v.adicCompletion K)ˣ) :=
    { carrier := {x | ∃ z : kˣ, z ^ n = 1 ∧
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) z)) = x}
      add_mem' := by
        rintro _ _ ⟨z₁, h₁, rfl⟩ ⟨z₂, h₂, rfl⟩
        exact ⟨z₁ * z₂, by rw [mul_pow, h₁, h₂, one_mul], by rw [map_mul, map_mul, ofMul_mul]⟩
      zero_mem' := ⟨1, one_pow n, by rw [map_one, map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨z, h, rfl⟩
        exact ⟨z⁻¹, by rw [inv_pow, h, inv_one], by rw [map_inv, map_inv, ofMul_inv]⟩ } with hAdef
  have hAroot : ∀ x ∈ A, ∃ y : Additive (v.adicCompletion K)ˣ,
      (∀ σ : ↥(stabilizer Gal(K/k) v), smulUnitsAut σ y = y) ∧
        Nat.card ↥(stabilizer Gal(K/k) v) • y = x := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hyinv, hypow⟩ := hroot z hz
    refine ⟨Additive.ofMul y, fun σ => ?_, ?_⟩
    · refine Additive.toMul.injective (Units.ext ?_)
      rw [coe_smulUnitsAut_apply, toMul_ofMul]
      exact hyinv σ
    · rw [← ofMul_pow, hypow]
  have hfA : ∀ s t : ↥(stabilizer Gal(K/k) v),
      Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1))) ∈ A :=
    fun s t => ⟨a s.1 t.1, hpow _ _, rfl⟩
  have hfcoc : ∀ x y z : ↥(stabilizer Gal(K/k) v),
      smulUnitsAut x
          (Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a y.1 z.1))))
        + Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a x.1 (y.1 * z.1))))
      = Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a (x.1 * y.1) z.1)))
        + Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a x.1 y.1))) := by
    intro x y z
    rw [smulUnitsAut_adicUnitHom_algebraMap]
    simp only [← ofMul_mul, ← map_mul]
    rw [ha]
  exact exists_sub_add_eq_of_forall_exists_nsmul
    (smulUnitsAut (G := ↥(stabilizer Gal(K/k) v)) (R := v.adicCompletion K)) hg hAroot hfA hfcoc

/-- **A two-cocycle with values in the units of the base field and killed by an odd integer is the
coboundary of a one-cochain with values in the units of the extension, as soon as at every ramified
finite place its values are local powers with exponent the order of a cyclic decomposition
group.** -/
theorem exists_isMulCoboundary_of_odd_of_forall_exists_pow {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(K/k) v), (∀ x : ↥(stabilizer Gal(K/k) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : kˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
          (∀ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K) = y) ∧
            y ^ Nat.card ↥(stabilizer Gal(K/k) v)
              = adicUnitHom v (Units.map (algebraMap k K : k →* K) z)) :
    ∃ b : Gal(K/k) → Kˣ, ∀ x y : Gal(K/k),
      x • b y / b (x * y) * b x = Units.map (algebraMap k K : k →* K) (a x y) := by
  refine exists_isMulCoboundary_of_odd hn hpow ha fun v hv => ?_
  obtain ⟨g, hg, hroot⟩ := hram v hv
  exact exists_sub_add_eq_adicUnits_of_exists_pow v hg hpow ha hroot

end InverseGalois.CFT
