/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Approximation.PowClass
import InverseGalois.CFT.Units.Idele

/-!
# The ideles that are local powers at a finite set of places

An idele of a number field whose component is an `n`-th power at every infinite place and at
finitely many chosen finite places forms a subgroup of the ideles.  Approximation says that this
subgroup together with the principal ideles is everything: an element of the field close enough to
the given components at the chosen places differs from them there by `n`-th powers, so dividing the
idele by that element lands in the subgroup.

This is the topology-free replacement for the statement that the principal ideles together with the
ideles that are trivial at the chosen places are dense.  Both are used in the same way, to feed a
norm criterion; the difference is that the subgroup here is large enough for the exact equality to
hold, which is what makes the topology unnecessary.

## Main definitions

* `InverseGalois.CFT.nsmulSubgroup`: the multiples of `n` in an additive commutative group.
* `InverseGalois.CFT.localPowIdele`: **the ideles whose component is an `n`-th power at every
  infinite place and at each chosen finite place.**

## Main results

* `InverseGalois.CFT.exists_units_sub_diag_eq_nsmul`: **prescribed local units at all the infinite
  places and at finitely many primes agree with a single unit of the field up to `n`-th powers.**
* `InverseGalois.CFT.ideleDiag_range_sup_localPowIdele_eq_top`: **the principal ideles together with
  the ideles that are local `n`-th powers at the chosen places are all the ideles.**

## Tags

number field, idele, approximation, power, place
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

/-! ### Dividing by an approximating element -/

section Ratio

variable {R : Type*} [Field R]

/-- **Two units of a field that differ by an `n`-th power differ by an `n`-th power of a unit**, an
`n`-th power carrying one unit to another being nonzero. -/
theorem exists_units_sub_eq_nsmul {n : ℕ} (hn : n ≠ 0) {A B : Rˣ} {z : R}
    (hz : z ^ n * (A : R) = (B : R)) :
    ∃ Z : Rˣ, Additive.ofMul A - Additive.ofMul B = n • Additive.ofMul Z := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn, zero_mul] at hz
    exact B.ne_zero hz.symm
  have hZ : Units.mk0 z hz0 ^ n * A = B := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hz
  refine ⟨(Units.mk0 z hz0)⁻¹, ?_⟩
  rw [sub_eq_iff_eq_add, ← ofMul_pow, ← ofMul_mul]
  refine congrArg Additive.ofMul ?_
  rw [← hZ, inv_pow, inv_mul_cancel_left]

end Ratio

/-! ### Approximation up to local powers -/

section Approx

variable {K : Type*} [Field K] [NumberField K] {Y : Type*} [Finite Y]
  {ι : Y → HeightOneSpectrum (𝓞 K)}

/-- **Prescribed local units at all the infinite places and at finitely many primes agree with a
single unit of the field up to `n`-th powers.**  Approximation places a unit of the field near each
of the prescribed ones, and near enough means differing by an `n`-th power. -/
theorem exists_units_sub_diag_eq_nsmul {n : ℕ} (hn : n ≠ 0) (hinj : Function.Injective ι)
    (a : ∀ w : InfinitePlace K, Additive w.Completionˣ)
    (c : ∀ y : Y, Additive ((ι y).adicCompletion K)ˣ) :
    ∃ b : Kˣ,
      (∀ w : InfinitePlace K, ∃ z : Additive w.Completionˣ,
        a w - Additive.ofMul (infiniteUnitHom w b) = n • z) ∧
      ∀ y : Y, ∃ z : Additive ((ι y).adicCompletion K)ˣ,
        c y - Additive.ofMul (adicUnitHom (ι y) b) = n • z := by
  obtain ⟨b, hb0, hbA, hbC⟩ := exists_ne_zero_pow_mul_eq_completion hn hinj
    (fun w => ((Additive.toMul (a w) : w.Completionˣ) : w.Completion))
    (fun w => Units.ne_zero _)
    (fun y => ((Additive.toMul (c y) : ((ι y).adicCompletion K)ˣ) : (ι y).adicCompletion K))
    (fun y => Units.ne_zero _)
  refine ⟨Units.mk0 b hb0, fun w => ?_, fun y => ?_⟩
  · obtain ⟨z, hz⟩ := hbA w
    obtain ⟨Z, hZ⟩ := exists_units_sub_eq_nsmul (A := Additive.toMul (a w))
      (B := infiniteUnitHom w (Units.mk0 b hb0)) hn (by
        rw [coe_infiniteUnitHom, Units.val_mk0]
        exact hz)
    exact ⟨Additive.ofMul Z, hZ⟩
  · obtain ⟨z, hz⟩ := hbC y
    obtain ⟨Z, hZ⟩ := exists_units_sub_eq_nsmul (A := Additive.toMul (c y))
      (B := adicUnitHom (ι y) (Units.mk0 b hb0)) hn (by
        rw [coe_adicUnitHom, Units.val_mk0]
        exact hz)
    exact ⟨Additive.ofMul Z, hZ⟩

end Approx

/-! ### The subgroup of local powers -/

section LocalPowIdele

/-- **The multiples of `n` in an additive commutative group.** -/
def nsmulSubgroup (A : Type*) [AddCommGroup A] (n : ℕ) : AddSubgroup A where
  carrier := {x | ∃ z, x = n • z}
  add_mem' := fun ⟨z, hz⟩ ⟨z', hz'⟩ => ⟨z + z', by rw [hz, hz', smul_add]⟩
  zero_mem' := ⟨0, (smul_zero n).symm⟩
  neg_mem' := fun ⟨z, hz⟩ => ⟨-z, by rw [hz, smul_neg]⟩

theorem mem_nsmulSubgroup {A : Type*} [AddCommGroup A] {n : ℕ} {x : A} :
    x ∈ nsmulSubgroup A n ↔ ∃ z, x = n • z := Iff.rfl

variable (k : Type*) [Field k] [NumberField k]

/-- **The ideles whose component is an `n`-th power at every infinite place and at each chosen
finite place.** -/
def localPowIdele (S : Set (HeightOneSpectrum (𝓞 k))) (n : ℕ) : AddSubgroup ↥(idele k) where
  carrier := {x | (∀ w : InfinitePlace k, (x : FullIdele k).1 w ∈ nsmulSubgroup _ n) ∧
    ∀ v ∈ S, (x : FullIdele k).2 v ∈ nsmulSubgroup _ n}
  add_mem' hx hy :=
    ⟨fun w => add_mem (hx.1 w) (hy.1 w), fun v hv => add_mem (hx.2 v hv) (hy.2 v hv)⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => zero_mem _⟩
  neg_mem' hx := ⟨fun w => neg_mem (hx.1 w), fun v hv => neg_mem (hx.2 v hv)⟩

variable {k} in
theorem mem_localPowIdele {S : Set (HeightOneSpectrum (𝓞 k))} {n : ℕ} {x : ↥(idele k)} :
    x ∈ localPowIdele k S n ↔ (∀ w : InfinitePlace k, (x : FullIdele k).1 w ∈ nsmulSubgroup _ n) ∧
      ∀ v ∈ S, (x : FullIdele k).2 v ∈ nsmulSubgroup _ n := Iff.rfl

/-- **The principal ideles together with the ideles that are local `n`-th powers at the chosen
places are all the ideles.**  A unit of the field agreeing at the chosen places with the given idele
up to `n`-th powers exists by approximation, and dividing the idele by it lands in the subgroup. -/
theorem ideleDiag_range_sup_localPowIdele_eq_top {S : Set (HeightOneSpectrum (𝓞 k))}
    (hS : S.Finite) {n : ℕ} (hn : n ≠ 0) :
    (ideleDiag k).range ⊔ localPowIdele k S n = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  haveI := hS.to_subtype
  obtain ⟨b, hbA, hbC⟩ := exists_units_sub_diag_eq_nsmul (ι := (Subtype.val : ↥S → _)) hn
    Subtype.val_injective (fun w => (x : FullIdele k).1 w) (fun y => (x : FullIdele k).2 y)
  refine AddSubgroup.mem_sup.mpr ⟨ideleDiag k (Additive.ofMul b), ⟨Additive.ofMul b, rfl⟩,
    x - ideleDiag k (Additive.ofMul b), ⟨fun w => ?_, fun v hv => ?_⟩, by abel⟩
  · obtain ⟨z, hz⟩ := hbA w
    exact ⟨z, hz⟩
  · obtain ⟨z, hz⟩ := hbC ⟨v, hv⟩
    exact ⟨z, hz⟩

end LocalPowIdele

end InverseGalois.CFT
