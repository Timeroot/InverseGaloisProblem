/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CoprimeCoboundary
import InverseGalois.CFT.Local.UnramifiedCoboundary
import InverseGalois.CFT.Units.ABHN
import InverseGalois.CFT.Units.IdeleClass
import InverseGalois.CFT.Units.LocalEmbedding

/-!
# A two-cocycle of the units of odd order is controlled by the ramified finite places

The Albert-Brauer-Hasse-Noether theorem reduces the triviality of a two-cocycle with values in the
units of a Galois extension of number fields to its triviality at every place.  For a cocycle killed
by an odd integer almost all of those places are free of charge:

* at an archimedean place the decomposition group has order one or two, hence order coprime to the
  integer killing the cocycle, and a cocycle of coprime order over a finite group is a coboundary;
* at an unramified finite place the local component is a unit of the valuation ring, because its
  valuation is an integer killed by a nonzero integer, and a two-cocycle of the cyclic decomposition
  group with values in those units is a coboundary.

What is left is the ramified finite places, where the arithmetic of the extension genuinely enters.
This is the shape in which the theorem is used to solve central embedding problems with kernel of
odd prime order: the local conditions to be arranged are conditions at the ramified primes only.

## Main results

* `InverseGalois.CFT.smulUnitsAut_adicUnitHom`, `InverseGalois.CFT.smulUnitsAut_infiniteUnitHom`:
  the embedding of the units of a number field into the units of a completion is equivariant for
  the decomposition group at the corresponding place.
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits_of_nsmul_eq_zero`: at an unramified finite place
  the local component of a two-cocycle killed by a nonzero integer is a coboundary.
* `InverseGalois.CFT.exists_sub_add_eq_infiniteUnits_of_odd`: at an archimedean place the local
  component of a two-cocycle killed by an odd integer is a coboundary.
* `InverseGalois.CFT.exists_sub_add_eq_globalUnits_of_odd`: **a two-cocycle of the units killed by
  an odd integer which is a coboundary at every ramified finite place is a coboundary.**

## Tags

number field, idele, Brauer group, group cohomology, two-cocycle, coboundary, decomposition group,
unramified, Albert-Brauer-Hasse-Noether
-/

open IsDedekindDomain MulAction NumberField

open scoped WithZero

namespace InverseGalois.CFT

/-! ### Equivariance of the local embeddings -/

section Equivariance

variable {k K : Type*} [Field k] [Field K] [NumberField K] [Algebra k K]

/-- **The embedding of a number field into the completion at a finite place is equivariant** for
the decomposition group there. -/
theorem smul_adicCoe (v : HeightOneSpectrum (𝓞 K)) (σ : ↥(stabilizer Gal(K/k) v)) (y : K) :
    σ • adicCoe y v = adicCoe (σ.1 y) v := by
  rw [stabilizer_smul_adicCompletion_def, adicCoe, adicCompletionAut_coe]
  rfl

omit [NumberField K] in
/-- **The embedding of a number field into the completion at an archimedean place is equivariant**
for the decomposition group there. -/
theorem smul_infiniteCoe (w : InfinitePlace K) (σ : ↥(stabilizer Gal(K/k) w)) (y : K) :
    σ • infiniteCoe y w = infiniteCoe (σ.1 y) w := by
  rw [stabilizer_smul_infiniteCompletion_def, infiniteCoe, infiniteCompletionAut_coe]
  rfl

/-- **The embedding of the units of a number field into the units of the completion at a finite
place is equivariant** for the decomposition group there. -/
theorem smulUnitsAut_adicUnitHom (v : HeightOneSpectrum (𝓞 K))
    (σ : ↥(stabilizer Gal(K/k) v)) (a : Additive Kˣ) :
    smulUnitsAut σ (Additive.ofMul (adicUnitHom v a.toMul))
      = Additive.ofMul (adicUnitHom v ((globalUnitsAut (k := k) σ.1 a).toMul)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [coe_smulUnitsAut_apply, toMul_ofMul, coe_adicUnitHom, smul_adicCoe]
  rfl

omit [NumberField K] in
/-- **The embedding of the units of a number field into the units of the completion at an
archimedean place is equivariant** for the decomposition group there. -/
theorem smulUnitsAut_infiniteUnitHom (w : InfinitePlace K)
    (σ : ↥(stabilizer Gal(K/k) w)) (a : Additive Kˣ) :
    smulUnitsAut σ (Additive.ofMul (infiniteUnitHom w a.toMul))
      = Additive.ofMul (infiniteUnitHom w ((globalUnitsAut (k := k) σ.1 a).toMul)) := by
  refine Additive.toMul.injective (Units.ext ?_)
  simp only [coe_smulUnitsAut_apply, toMul_ofMul, coe_infiniteUnitHom, smul_infiniteCoe]
  rfl

end Equivariance

/-! ### Torsion units are units of the valuation ring -/

section Torsion

variable {A : Type*} [Field A] [Valued A ℤᵐ⁰]

/-- **A unit killed by a nonzero integer is a unit of the valuation ring**, because its valuation
is an integer killed by that integer. -/
theorem mem_ker_unitVal_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {x : Additive Aˣ}
    (hx : n • x = 0) : x ∈ (unitVal (A := A)).ker := by
  rw [AddMonoidHom.mem_ker]
  have h : n • unitVal x = 0 := by rw [← map_nsmul, hx, map_zero]
  rw [nsmul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) hn
  · exact h

end Torsion

/-! ### The places which cost nothing -/

section Bridge

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **At an unramified finite place the local component of a two-cocycle of the units killed by a
nonzero integer is a coboundary.**  The local component takes its values in the units of the
valuation ring, where the second cohomology of the cyclic decomposition group vanishes. -/
theorem exists_sub_add_eq_adicUnits_of_nsmul_eq_zero (v : HeightOneSpectrum (𝓞 K))
    (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal) {n : ℕ} (hn : n ≠ 0)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hpow : ∀ x y : Gal(K/k), n • a x y = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → Additive (v.adicCompletion K)ˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) v),
        Additive.ofMul (adicUnitHom v (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  set ι : Additive Kˣ →+ Additive (v.adicCompletion K)ˣ :=
    MonoidHom.toAdditive (adicUnitHom v) with hι
  have hιapp : ∀ x : Additive Kˣ, ι x = Additive.ofMul (adicUnitHom v x.toMul) := fun _ => rfl
  have hmem : ∀ x y : Gal(K/k), ι (a x y) ∈ (unitVal (A := v.adicCompletion K)).ker := by
    intro x y
    refine mem_ker_unitVal_of_nsmul_eq_zero hn ?_
    rw [← map_nsmul, hpow, map_zero]
  set f : ↥(stabilizer Gal(K/k) v) → ↥(stabilizer Gal(K/k) v) →
      ↥(unitVal (A := v.adicCompletion K)).ker :=
    fun s t => ⟨ι (a s.1 t.1), hmem s.1 t.1⟩ with hf
  have hcocycle : ∀ x y z : ↥(stabilizer Gal(K/k) v),
      kerUnitValAutHom (valued_smul_adicCompletion v) x (f y z) + f x (y * z)
        = f (x * y) z + f x y := by
    intro x y z
    refine Subtype.ext ?_
    show smulUnitsAut x (ι (a y.1 z.1)) + ι (a x.1 (y.1 * z.1))
      = ι (a (x.1 * y.1) z.1) + ι (a x.1 y.1)
    rw [hιapp, smulUnitsAut_adicUnitHom, ← hιapp, ← map_add, ← map_add, ha]
  obtain ⟨c, hc⟩ := exists_sub_add_eq_adicUnits v hunr hcocycle
  refine ⟨fun t => (c t : Additive (v.adicCompletion K)ˣ), fun s t => ?_⟩
  exact congrArg (Subtype.val (p := fun x => x ∈ (unitVal (A := v.adicCompletion K)).ker)) (hc s t)

omit [IsGalois k K] in
/-- **At an archimedean place the local component of a two-cocycle of the units killed by an odd
integer is a coboundary.**  The decomposition group there has order one or two, hence order coprime
to that integer. -/
theorem exists_sub_add_eq_infiniteUnits_of_odd (w : InfinitePlace K) {n : ℕ} (hn : Odd n)
    {a : Gal(K/k) → Gal(K/k) → Additive Kˣ}
    (hpow : ∀ x y : Gal(K/k), n • a x y = 0)
    (ha : ∀ x y z : Gal(K/k),
      globalUnitsAut x (a y z) + a x (y * z) = a (x * y) z + a x y) :
    ∃ c : ↥(stabilizer Gal(K/k) w) → Additive w.Completionˣ,
      ∀ s t : ↥(stabilizer Gal(K/k) w),
        Additive.ofMul (infiniteUnitHom w (a s.1 t.1).toMul)
          = smulUnitsAut s (c t) - c (s * t) + c s := by
  classical
  haveI : Fintype ↥(stabilizer Gal(K/k) w) := Fintype.ofFinite _
  set ι : Additive Kˣ →+ Additive w.Completionˣ :=
    MonoidHom.toAdditive (infiniteUnitHom w) with hι
  have hιapp : ∀ x : Additive Kˣ, ι x = Additive.ofMul (infiniteUnitHom w x.toMul) := fun _ => rfl
  have hcop : Nat.Coprime (Nat.card ↥(stabilizer Gal(K/k) w)) n := by
    rcases InfinitePlace.nat_card_stabilizer_eq_one_or_two k w with h | h
    · rw [h]; exact Nat.coprime_one_left n
    · rw [h]
      exact Nat.coprime_two_left.mpr hn
  refine exists_sub_add_eq_of_coprime (smulUnitsAut (G := ↥(stabilizer Gal(K/k) w))
    (R := w.Completion)) hcop (f := fun s t => ι (a s.1 t.1)) ?_ ?_
  · intro x y z
    show smulUnitsAut x (ι (a y.1 z.1)) + ι (a x.1 (y.1 * z.1))
      = ι (a (x.1 * y.1) z.1) + ι (a x.1 y.1)
    rw [hιapp, smulUnitsAut_infiniteUnitHom, ← hιapp, ← map_add, ← map_add, ha]
  · intro x y
    rw [← map_nsmul, hpow, map_zero]

/-- **A two-cocycle of the units killed by an odd integer which is a coboundary at every ramified
finite place is a coboundary.**  The archimedean places and the unramified finite places impose no
condition, so the Albert-Brauer-Hasse-Noether theorem applies. -/
theorem exists_sub_add_eq_globalUnits_of_odd {n : ℕ} (hn : Odd n)
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
      ∀ x y : Gal(K/k), a x y = globalUnitsAut x (b y) - b (x * y) + b x := by
  refine exists_sub_add_eq_globalUnits ha
    (fun w => exists_sub_add_eq_infiniteUnits_of_odd w hn hpow ha) (fun v => ?_)
  by_cases hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal
  · exact exists_sub_add_eq_adicUnits_of_nsmul_eq_zero v hunr hn.pos.ne' hpow ha
  · exact hram v hunr

end Bridge

end InverseGalois.CFT
