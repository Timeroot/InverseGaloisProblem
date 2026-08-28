/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Units.ABHNArchimedean
import InverseGalois.CFT.Units.ABHNCoboundary

/-!
# Restricting a two-cocycle of the units to a subgroup of the Galois group

The Albert-Brauer-Hasse-Noether theorem imposes a condition at the archimedean places, and over the
rational numbers that condition cannot be met at the prime two: the real place ramifies in every
totally complex extension.  A subgroup of the Galois group offers a way round.  A subgroup is the
Galois group of the extension over its own fixed field, and when that fixed field is totally complex
no archimedean place ramifies over it, so the theorem applies verbatim over the fixed field and
produces a one-cochain trivialising the restriction of the cocycle to the subgroup.

Everything in sight is compatible with restriction of scalars, and in the strongest possible sense:
the action of an automorphism on the primes of the ring of integers, on the units of the field, and
on the units of a completion does not depend on which subfield the automorphism is taken to fix, so
the transport of the local data costs nothing at all.

## Main definitions

* `InverseGalois.CFT.stabilizerRestrictScalars`: an element of the decomposition group over an
  intermediate field, as an element of the decomposition group over the base field.

## Main results

* `InverseGalois.CFT.restrictScalars_smul_heightOneSpectrum`: the action of an automorphism on the
  primes of the ring of integers does not depend on the base field.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_restrictScalars`: the local condition at a finite
  place transports to an intermediate field.
* `InverseGalois.CFT.exists_sub_add_eq_globalUnits_on_subgroup`: **a two-cocycle of the units killed
  by a nonzero integer and a coboundary at every ramified finite place restricts, to a subgroup of
  the Galois group whose fixed field is totally complex, to a coboundary.**
* `InverseGalois.CFT.exists_isMulCoboundary_on_subgroup`: its multiplicative form, for a cocycle
  with values in the units of the base field.

## Tags

number field, Albert-Brauer-Hasse-Noether, two-cocycle, coboundary, base change, fixed field,
totally complex
-/

open IsDedekindDomain MulAction NumberField

namespace InverseGalois.CFT

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  {F : IntermediateField k K}

/-! ### Restriction of scalars leaves the local data unchanged -/

omit [NumberField k] [NumberField K] in
/-- **The action of an automorphism on the primes of the ring of integers does not depend on the
base field** the automorphism is taken to fix. -/
theorem restrictScalars_smul_heightOneSpectrum (φ : Gal(K/↥F)) (v : HeightOneSpectrum (𝓞 K)) :
    (φ.restrictScalars k) • v = φ • v :=
  rfl

omit [NumberField k] [NumberField K] in
/-- The action of an automorphism on the units of the field does not depend on the base field. -/
theorem globalUnitsAut_restrictScalars (φ : Gal(K/↥F)) (u : Additive Kˣ) :
    globalUnitsAut (k := k) (φ.restrictScalars k) u = globalUnitsAut (k := ↥F) φ u :=
  rfl

omit [NumberField k] [NumberField K] in
/-- The action on the units of the field of an automorphism which restricts to a given one. -/
theorem globalUnitsAut_eq_of_restrictScalars {φ : Gal(K/↥F)} {x : Gal(K/k)}
    (hx : φ.restrictScalars k = x) (u : Additive Kˣ) :
    globalUnitsAut x u = globalUnitsAut φ u := by
  subst hx
  rfl

variable (k) in
omit [NumberField k] [NumberField K] in
/-- **An element of the decomposition group over an intermediate field, as an element of the
decomposition group over the base field.** -/
def stabilizerRestrictScalars (v : HeightOneSpectrum (𝓞 K)) (s : ↥(stabilizer Gal(K/↥F) v)) :
    ↥(stabilizer Gal(K/k) v) :=
  ⟨s.1.restrictScalars k, mem_stabilizer_iff.mpr
    ((restrictScalars_smul_heightOneSpectrum s.1 v).trans (mem_stabilizer_iff.mp s.2))⟩

variable (k) in
omit [NumberField k] [NumberField K] in
/-- Restriction of scalars on the decomposition group respects multiplication. -/
theorem stabilizerRestrictScalars_mul (v : HeightOneSpectrum (𝓞 K))
    (s t : ↥(stabilizer Gal(K/↥F) v)) :
    stabilizerRestrictScalars k v (s * t)
      = stabilizerRestrictScalars k v s * stabilizerRestrictScalars k v t :=
  Subtype.ext (AlgEquiv.ext fun _ => rfl)

variable (k) in
omit [NumberField k] in
/-- The action on the units of a completion does not depend on the base field. -/
theorem smulUnitsAut_stabilizerRestrictScalars (v : HeightOneSpectrum (𝓞 K))
    (s : ↥(stabilizer Gal(K/↥F) v)) (u : Additive (v.adicCompletion K)ˣ) :
    smulUnitsAut (stabilizerRestrictScalars k v s) u = smulUnitsAut s u :=
  rfl

variable (k) in
omit [NumberField k] in
/-- **The local condition at a finite place transports to an intermediate field**, the decomposition
group over the intermediate field mapping into the decomposition group over the base field
compatibly with the action on the units of the completion. -/
theorem exists_sub_add_eq_adicUnits_restrictScalars (v : HeightOneSpectrum (𝓞 K))
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (h : ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ c : ↥(stabilizer Gal(K/↥F) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/↥F) v),
        Additive.ofMul
            (adicUnitHom v (a (s.1.restrictScalars k) (t.1.restrictScalars k)).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun s => c (stabilizerRestrictScalars k v s), fun s t => ?_⟩
  have hst := hc (stabilizerRestrictScalars k v s) (stabilizerRestrictScalars k v t)
  rw [← stabilizerRestrictScalars_mul k v s t, smulUnitsAut_stabilizerRestrictScalars k v s] at hst
  exact hst

/-! ### The restriction to a subgroup with totally complex fixed field -/

variable [IsGalois k K]

/-- **A two-cocycle of the units killed by a nonzero integer and a coboundary at every ramified
finite place restricts, to a subgroup of the Galois group whose fixed field is totally complex, to a
coboundary.**  Over the fixed field no archimedean place ramifies, so the
Albert-Brauer-Hasse-Noether theorem applies there with no condition at infinity, and the subgroup is
by Artin's theorem the whole Galois group over that fixed field. -/
theorem exists_sub_add_eq_globalUnits_on_subgroup (N : Subgroup Gal(K/k))
    (hcx : IsTotallyComplex ↥(IntermediateField.fixedField N)) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hpow : ∀ x y : Gal(K/k), n • a x y = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Additive Kˣ,
      ∀ x ∈ N, ∀ y ∈ N, a x y = globalUnitsAut x (b y) - b (x * y) + b x := by
  classical
  haveI := hcx
  haveI : IsUnramifiedAtInfinitePlaces ↥(IntermediateField.fixedField N) K :=
    IsUnramifiedAtInfinitePlaces.of_isTotallyComplex
  have hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
    intro v
    by_cases hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal
    · exact exists_sub_add_eq_adicUnits_of_nsmul_eq_zero v hunr hn hpow ha
    · exact hram v hunr
  have hmul : ∀ φ ψ : Gal(K/↥(IntermediateField.fixedField N)),
      (φ * ψ).restrictScalars k = φ.restrictScalars k * ψ.restrictScalars k :=
    fun _ _ => AlgEquiv.ext fun _ => rfl
  have hAcoc : ∀ φ ψ χ : Gal(K/↥(IntermediateField.fixedField N)),
      globalUnitsAut φ (a (ψ.restrictScalars k) (χ.restrictScalars k))
          + a (φ.restrictScalars k) ((ψ * χ).restrictScalars k)
        = a ((φ * ψ).restrictScalars k) (χ.restrictScalars k)
          + a (φ.restrictScalars k) (ψ.restrictScalars k) := by
    intro φ ψ χ
    rw [hmul, hmul, ← globalUnitsAut_restrictScalars]
    exact ha _ _ _
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits_of_forall_finite
    (a := fun φ ψ : Gal(K/↥(IntermediateField.fixedField N)) =>
      a (φ.restrictScalars k) (ψ.restrictScalars k))
    hAcoc fun v => exists_sub_add_eq_adicUnits_restrictScalars k v (hfin v)
  have hfix : IntermediateField.fixingSubgroup (IntermediateField.fixedField N) = N :=
    IntermediateField.fixingSubgroup_fixedField N
  have hE : ∀ (z : Gal(K/k))
      (hz : z ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N)),
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N)
        ⟨z, hz⟩).restrictScalars k = z :=
    fun _ _ => AlgEquiv.ext fun _ => rfl
  obtain ⟨B, hB⟩ : ∃ B : Gal(K/k) → Additive Kˣ,
      ∀ (z : Gal(K/k))
        (hz : z ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N)),
        B z = b (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N)
          ⟨z, hz⟩) :=
    ⟨fun x => if hx : x ∈ IntermediateField.fixingSubgroup
        (IntermediateField.fixedField N) then
        b (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N) ⟨x, hx⟩)
      else 0, fun _ hz => dif_pos hz⟩
  refine ⟨B, fun x hx y hy => ?_⟩
  have hx' : x ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N) := by
    rw [hfix]; exact hx
  have hy' : y ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N) := by
    rw [hfix]; exact hy
  have hxy' : x * y ∈ IntermediateField.fixingSubgroup (IntermediateField.fixedField N) := by
    rw [hfix]; exact mul_mem hx hy
  have hmulE : IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N)
        ⟨x * y, hxy'⟩
      = IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N) ⟨x, hx'⟩
        * IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N) ⟨y, hy'⟩ := by
    rw [← map_mul]
    rfl
  have h := hb (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N) ⟨x, hx'⟩)
    (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N) ⟨y, hy'⟩)
  rw [hE x hx', hE y hy'] at h
  rw [hB x hx', hB y hy', hB (x * y) hxy', hmulE,
    globalUnitsAut_eq_of_restrictScalars (hE x hx')]
  exact h

/-- **A two-cocycle with values in the units of the base field, killed by a nonzero integer and a
coboundary at every ramified finite place, restricts to a subgroup of the Galois group whose fixed
field is totally complex to a coboundary.**  The values lie in the base field, so the Galois group
fixes them and the inflated additive cocycle identity is the multiplicative one. -/
theorem exists_isMulCoboundary_on_subgroup (N : Subgroup Gal(K/k))
    (hcx : IsTotallyComplex ↥(IntermediateField.fixedField N)) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/k) → Gal(K/k) → kˣ} (hpow : ∀ x y, a x y ^ n = 1)
    (ha : ∀ x y z : Gal(K/k), a y z * a x (y * z) = a (x * y) z * a x y)
    (hram : ∀ v : HeightOneSpectrum (𝓞 K), ¬ Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal →
      ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (Units.map (algebraMap k K : k →* K) (a s.1 t.1)))
          = smulUnitsAut s (c t) - c (s * t) + c s) :
    ∃ b : Gal(K/k) → Kˣ, ∀ x ∈ N, ∀ y ∈ N,
      Units.map (algebraMap k K : k →* K) (a x y) = x • b y / b (x * y) * b x := by
  classical
  set ι : kˣ →* Kˣ := Units.map (algebraMap k K : k →* K) with hι
  set A : Gal(K/k) → Gal(K/k) → Additive Kˣ := fun x y => Additive.ofMul (ι (a x y)) with hA
  have hApow : ∀ x y : Gal(K/k), n • A x y = 0 := by
    intro x y
    rw [hA]
    show n • Additive.ofMul (ι (a x y)) = 0
    rw [← ofMul_pow, ← map_pow, hpow, map_one]
    rfl
  have hAcocycle : ∀ x y z : Gal(K/k),
      globalUnitsAut x (A y z) + A x (y * z) = A (x * y) z + A x y := by
    intro x y z
    have hfixed : (globalUnitsAut x (A y z)) = A y z := by
      refine Additive.toMul.injective ?_
      rw [toMul_globalUnitsAut]
      exact smul_algebraMap_units x (a y z)
    rw [hfixed, hA]
    show Additive.ofMul (ι (a y z)) + Additive.ofMul (ι (a x (y * z)))
      = Additive.ofMul (ι (a (x * y) z)) + Additive.ofMul (ι (a x y))
    rw [← ofMul_mul, ← ofMul_mul, ← map_mul, ← map_mul, ha]
  obtain ⟨b, hb⟩ := exists_sub_add_eq_globalUnits_on_subgroup N hcx hn hApow hAcocycle hram
  refine ⟨fun g => (b g).toMul, fun x hx y hy => ?_⟩
  have h2 := congrArg Additive.toMul (hb x hx y hy)
  rw [toMul_add, toMul_sub, toMul_globalUnitsAut] at h2
  exact h2

end InverseGalois.CFT
