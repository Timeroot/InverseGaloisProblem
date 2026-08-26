/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNLocalPower

/-!
# The local condition of the Albert-Brauer-Hasse-Noether theorem at a place where the values are
local norms

At a finite place with cyclic decomposition group the second cohomology of the units of the
completion is the invariants modulo the norms.  The values of a two-cocycle coming from the base
field are invariant, so the local condition of the Albert-Brauer-Hasse-Noether theorem holds there
as soon as each of those values is a **norm** from the completion of the extension — the product of
its conjugates under the decomposition group.

This is the sharp form of the condition.  The form already available asks for more, that each value
be a power, with exponent the order of the decomposition group, of a unit the group fixes; such a
unit has itself for each of its conjugates, so its norm is that power and the power form implies
the norm form.  The converse fails: the norms from a ramified extension are not powers.

## Main results

* `InverseGalois.CFT.finprod_smul_eq_pow`: the norm of a unit fixed by the decomposition group is
  its power with exponent the order of that group.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_exists_norm`: **at a finite place with cyclic
  decomposition group, a two-cocycle with values in the units of the base field is a coboundary as
  soon as each of its values is locally a norm.**
* `InverseGalois.CFT.exists_isMulCoboundary_of_coprime_of_forall_exists_norm`,
  `InverseGalois.CFT.exists_isMulCoboundary_of_odd_of_forall_exists_norm`: the resulting form of the
  Albert-Brauer-Hasse-Noether theorem, whose only remaining hypothesis is that local one.

## Tags

number field, Albert-Brauer-Hasse-Noether, decomposition group, coboundary, local norm
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

omit [IsGalois k K] in
/-- **The norm of an element fixed by the decomposition group at a finite place is its power with
exponent the order of that group.**  Each conjugate of a fixed element is the element itself, so the
product of the conjugates is a product of equal factors. -/
theorem finprod_smul_eq_pow (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K}
    (hy : ∀ σ : ↥(stabilizer Gal(K/k) v), σ • y = y) :
    ∏ᶠ σ : ↥(stabilizer Gal(K/k) v), σ • y = y ^ Nat.card ↥(stabilizer Gal(K/k) v) := by
  haveI : Fintype ↥(stabilizer Gal(K/k) v) := Fintype.ofFinite _
  rw [finprod_eq_prod_of_fintype]
  simp only [hy]
  rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

omit [IsGalois k K] in
/-- **At a finite place with cyclic decomposition group, a two-cocycle with values in the units of
the base field is a coboundary as soon as each of its values is locally a norm.**  The values of the
cocycle come from the base field, so the decomposition group fixes them; the second cohomology of a
cyclic group is the invariants modulo the norms, and only the values of the cocycle have to be
norms. -/
theorem exists_sub_add_eq_adicUnits_of_exists_norm (v : HeightOneSpectrum (𝓞 K))
    {g : ↥(stabilizer Gal(K/k) v)} (hg : ∀ x : ↥(stabilizer Gal(K/k) v), x ∈ Subgroup.zpowers g)
    {n : ℕ} {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hnorm : ∀ z : kˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
      ∏ᶠ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K)
        = ((adicUnitHom v (Units.map (algebraMap k K : k →* K) z) : (v.adicCompletion K)ˣ) :
            v.adicCompletion K)) :
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
  have hAinv : ∀ x ∈ A, ∀ σ : ↥(stabilizer Gal(K/k) v), smulUnitsAut σ x = x := by
    rintro _ ⟨z, -, rfl⟩ σ
    exact smulUnitsAut_adicUnitHom_algebraMap v σ z
  have hAnorm : ∀ x ∈ A, ∃ y : Additive (v.adicCompletion K)ˣ,
      ∑ σ : ↥(stabilizer Gal(K/k) v), smulUnitsAut σ y = x := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy⟩ := hnorm z hz
    refine ⟨Additive.ofMul y, Additive.toMul.injective (Units.ext ?_)⟩
    rw [toMul_sum, Units.coe_prod, toMul_ofMul, ← hy, finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun σ _ => coe_smulUnitsAut_apply σ (Additive.ofMul y)
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
  exact exists_sub_add_eq_of_forall_mem
    (smulUnitsAut (G := ↥(stabilizer Gal(K/k) v)) (R := v.adicCompletion K)) hg hAinv hAnorm hfA
    hfcoc

/-- **A two-cocycle with values in the units of the base field and killed by an integer the
archimedean places cost nothing for is the coboundary of a one-cochain with values in the units of
the extension, as soon as at every ramified finite place its values are local norms for a cyclic
decomposition group.** -/
theorem exists_isMulCoboundary_of_coprime_of_forall_exists_norm {n : ℕ} (hn : n ≠ 0)
    (hcop : IsCoprimeAtInfinitePlaces k K n)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(K/k) v), (∀ x : ↥(stabilizer Gal(K/k) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : kˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
          ∏ᶠ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K)
            = ((adicUnitHom v (Units.map (algebraMap k K : k →* K) z) : (v.adicCompletion K)ˣ) :
                v.adicCompletion K)) :
    ∃ b : Gal(K/k) → Kˣ, ∀ x y : Gal(K/k),
      x • b y / b (x * y) * b x = Units.map (algebraMap k K : k →* K) (a x y) := by
  refine exists_isMulCoboundary_of_coprime hn hcop hpow ha fun v hv => ?_
  obtain ⟨g, hg, hnorm⟩ := hram v hv
  exact exists_sub_add_eq_adicUnits_of_exists_norm v hg hpow ha hnorm

/-- **A two-cocycle with values in the units of the base field and killed by an odd integer is the
coboundary of a one-cochain with values in the units of the extension, as soon as at every ramified
finite place its values are local norms for a cyclic decomposition group.** -/
theorem exists_isMulCoboundary_of_odd_of_forall_exists_norm {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ g : ↥(stabilizer Gal(K/k) v), (∀ x : ↥(stabilizer Gal(K/k) v), x ∈ Subgroup.zpowers g) ∧
        ∀ z : kˣ, z ^ n = 1 → ∃ y : (v.adicCompletion K)ˣ,
          ∏ᶠ σ : ↥(stabilizer Gal(K/k) v), σ • (y : v.adicCompletion K)
            = ((adicUnitHom v (Units.map (algebraMap k K : k →* K) z) : (v.adicCompletion K)ˣ) :
                v.adicCompletion K)) :
    ∃ b : Gal(K/k) → Kˣ, ∀ x y : Gal(K/k),
      x • b y / b (x * y) * b x = Units.map (algebraMap k K : k →* K) (a x y) :=
  exists_isMulCoboundary_of_coprime_of_forall_exists_norm hn.pos.ne'
    (IsCoprimeAtInfinitePlaces.of_odd hn) hpow ha hram

end InverseGalois.CFT
