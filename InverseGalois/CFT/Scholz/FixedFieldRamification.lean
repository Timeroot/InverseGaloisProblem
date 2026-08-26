/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.SplitCompositum
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Ramification at the fixed field of a subgroup

Let `N` be a Galois number field and `U` a subgroup of its Galois group, with fixed field `F`.  A
prime `P` of `N` above a rational prime `p` then lies over a prime `𝔮` of `F`, and the order of the
decomposition group of `P` over `F` is the product of the ramification index and the residue degree
of `P` over `𝔮`.  Comparing with the same statement over `ℚ` and the multiplicativity of the two
invariants in a tower, the product of the ramification index and the residue degree of `𝔮` over `p`
is the index of the decomposition group of `P` intersected with `U` in the whole decomposition
group.

This is the tool that reads the local behaviour of an intermediate field off the position of its
subgroup relative to the decomposition group: an intermediate field whose subgroup contains the
decomposition group is unramified with residue degree one below `P`, and one whose subgroup is
small has correspondingly large ramification.

## Main results

* `InverseGalois.CFT.card_stabilizer_eq_mul_base`: **the order of the decomposition group over an
  arbitrary base** is the ramification index times the residue degree.
* `InverseGalois.CFT.card_stabilizer_fixedField`: the decomposition group over the fixed field of a
  subgroup is the intersection of the decomposition group with that subgroup.
* `InverseGalois.CFT.card_stabilizer_eq_card_inf_mul`: **the ramification index times the residue
  degree of the prime below a fixed field** is the index of the intersection of the decomposition
  group with the subgroup.
* `InverseGalois.CFT.ramificationIdx_eq_one_of_stabilizer_le`: **a subgroup containing the
  decomposition group has an unramified prime of residue degree one** below.

## Tags

number field, decomposition group, ramification index, residue degree, fixed field
-/

namespace InverseGalois.CFT

open scoped Pointwise

open NumberField IntermediateField

/-! ### The decomposition group over an arbitrary base -/

section Base

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K]

/-- **The order of the decomposition group over an arbitrary base** is the ramification index of
the prime over the prime below it times the residue degree. -/
theorem card_stabilizer_eq_mul_base (P : Ideal (𝓞 K)) [P.IsPrime] (hP : P ≠ ⊥) :
    Nat.card ↥(MulAction.stabilizer Gal(K/k) P) =
      Ideal.ramificationIdx (algebraMap (𝓞 k) (𝓞 K)) (P.under (𝓞 k)) P *
        (P.under (𝓞 k)).inertiaDeg P := by
  haveI := isMaximal_of_ne_bot_base P hP
  haveI := isMaximal_under_of_ne_bot_base (k := k) P hP
  haveI := isSeparable_residue_of_ne_bot_base (k := k) P hP
  haveI : Module.Finite (𝓞 k) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 k) (𝓞 K)
  haveI : IsGaloisGroup Gal(K/k) (𝓞 k) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/k) (𝓞 k) (𝓞 K) k K
  rw [Ideal.card_stabilizer_eq (G := Gal(K/k)) _ (under_ne_bot_base (k := k) P hP) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ P Gal(K/k),
    Ideal.inertiaDegIn_eq_inertiaDeg _ P Gal(K/k)]

end Base

/-! ### The Galois group over the fixed field of a subgroup -/

section FixedField

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] (U : Subgroup Gal(N/ℚ))

/-- **The Galois group over the fixed field of a subgroup, inside the whole Galois group.** -/
noncomputable def fixedFieldHom : Gal(N/↥(fixedField U)) →* Gal(N/ℚ) :=
  U.subtype.comp (IntermediateField.subgroupEquivAlgEquiv U).symm.toMonoidHom

omit [IsGalois ℚ N] in
@[simp]
theorem fixedFieldHom_apply (σ : Gal(N/↥(fixedField U))) (x : N) : fixedFieldHom U σ x = σ x := rfl

omit [IsGalois ℚ N] in
theorem fixedFieldHom_injective : Function.Injective (fixedFieldHom U) := by
  intro σ τ h
  ext x
  have := congrArg (fun ρ : Gal(N/ℚ) => ρ x) h
  simpa using this

omit [IsGalois ℚ N] in
@[simp]
theorem fixedFieldHom_range : (fixedFieldHom U).range = U := by
  rw [fixedFieldHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (IntermediateField.subgroupEquivAlgEquiv U).symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [IsGalois ℚ N] in
/-- The two actions on the ideals of the ring of integers agree. -/
theorem fixedFieldHom_smul (σ : Gal(N/↥(fixedField U))) (P : Ideal (𝓞 N)) :
    (fixedFieldHom U σ) • P = σ • P := by
  simp only [Ideal.pointwise_smul_def]
  congr 1

omit [IsGalois ℚ N] in
/-- **The decomposition group over the fixed field of a subgroup** is the intersection of the
decomposition group with that subgroup. -/
theorem card_stabilizer_fixedField (P : Ideal (𝓞 N)) :
    Nat.card ↥(MulAction.stabilizer Gal(N/↥(fixedField U)) P) =
      Nat.card ↥(MulAction.stabilizer Gal(N/ℚ) P ⊓ U) := by
  have hcomap : (MulAction.stabilizer Gal(N/ℚ) P).comap (fixedFieldHom U) =
      MulAction.stabilizer Gal(N/↥(fixedField U)) P := by
    ext σ
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, fixedFieldHom_smul]
  rw [← hcomap]
  refine (Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (fixedFieldHom_injective U)).toEquiv).trans ?_
  rw [Subgroup.map_comap_eq, fixedFieldHom_range, inf_comm]

end FixedField

/-! ### The prime below the fixed field -/

section Tower

variable {N : Type*} [Field N] [NumberField N] [IsGalois ℚ N] (U : Subgroup Gal(N/ℚ))
  {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 N)) [P.IsPrime] [hover : P.LiesOver (Ideal.span {(p : ℤ)})]

include hp in
/-- **The ramification index times the residue degree of the prime below the fixed field of a
subgroup** is the index of the intersection of the decomposition group with the subgroup. -/
theorem card_stabilizer_eq_card_inf_mul :
    Nat.card ↥(MulAction.stabilizer Gal(N/ℚ) P) =
      Nat.card ↥(MulAction.stabilizer Gal(N/ℚ) P ⊓ U) *
        (Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥(fixedField U))) (Ideal.span {(p : ℤ)})
            (P.under (𝓞 ↥(fixedField U))) *
          (Ideal.span {(p : ℤ)}).inertiaDeg (P.under (𝓞 ↥(fixedField U)))) := by
  set F := fixedField U with hF
  haveI : IsGalois ↥F N := IsGalois.tower_top_of_isGalois ℚ ↥F N
  set 𝔮 := P.under (𝓞 ↥F) with h𝔮
  have hspan : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_natCast hp hover
  haveI := isMaximal_span_prime hp
  haveI : P.IsMaximal := isMaximal_of_ne_bot_base P hP0
  haveI : 𝔮.IsMaximal := isMaximal_under_of_ne_bot_base (k := ↥F) P hP0
  have h𝔮0 : 𝔮 ≠ ⊥ := under_ne_bot_base (k := ↥F) P hP0
  -- the two invariants are multiplicative in the tower
  have hle : 𝔮.map (algebraMap (𝓞 ↥F) (𝓞 N)) ≤ P := Ideal.map_comap_le
  have hg0 : 𝔮.map (algebraMap (𝓞 ↥F) (𝓞 N)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot h𝔮0
  have hfg : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 N)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hspan
  have hetower := Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 ↥F) (T := 𝓞 N)
    (p := Ideal.span {(p : ℤ)}) (P := 𝔮) (Q := P) hg0 hfg hle
  have hftower := Ideal.inertiaDeg_algebra_tower (R := ℤ) (S := 𝓞 ↥F) (T := 𝓞 N)
    (Ideal.span {(p : ℤ)}) 𝔮 P
  rw [card_stabilizer_eq_mul N hp P, hetower, hftower, ← card_stabilizer_fixedField U P,
    card_stabilizer_eq_mul_base (k := ↥F) P hP0]
  ring

include hp in
/-- **A subgroup containing the decomposition group has an unramified prime of residue degree one
below it.**  The index of the intersection of the decomposition group with the subgroup is then
one, and the two invariants are positive. -/
theorem ramificationIdx_eq_one_of_stabilizer_le (hU : MulAction.stabilizer Gal(N/ℚ) P ≤ U) :
    Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥(fixedField U))) (Ideal.span {(p : ℤ)})
        (P.under (𝓞 ↥(fixedField U))) = 1 ∧
      (Ideal.span {(p : ℤ)}).inertiaDeg (P.under (𝓞 ↥(fixedField U))) = 1 := by
  have hkey := card_stabilizer_eq_card_inf_mul U hp P
  rw [inf_of_le_left hU] at hkey
  have hone : Nat.card ↥(MulAction.stabilizer Gal(N/ℚ) P) * 1 =
      Nat.card ↥(MulAction.stabilizer Gal(N/ℚ) P) *
        (Ideal.ramificationIdx (algebraMap ℤ (𝓞 ↥(fixedField U))) (Ideal.span {(p : ℤ)})
            (P.under (𝓞 ↥(fixedField U))) *
          (Ideal.span {(p : ℤ)}).inertiaDeg (P.under (𝓞 ↥(fixedField U)))) := by
    rw [mul_one]
    exact hkey
  have hef := (Nat.eq_of_mul_eq_mul_left Nat.card_pos hone).symm
  exact ⟨Nat.eq_one_of_mul_eq_one_right hef, Nat.eq_one_of_mul_eq_one_left hef⟩

end Tower

end InverseGalois.CFT
