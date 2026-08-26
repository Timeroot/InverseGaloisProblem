/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.CyclotomicCompositum
import InverseGalois.CFT.InertiaSurjective
import InverseGalois.CFT.Scholz.FrattiniInertia
import InverseGalois.CFT.Scholz.FrattiniInertiaSmall
import InverseGalois.CFT.Scholz.FrattiniSolution

/-!
# The Frattini bound on inertia at the residue characteristic

The local dichotomy at a cyclotomic place bounds the image of inertia in the Frattini quotient of
the abelianized decomposition group, but it is stated for a field containing a primitive `ℓ`-th
root of unity.  A Galois number field whose Galois group is an `ℓ`-group contains no such root for
odd `ℓ`, so the bound is obtained by adjoining one: the compositum with the `ℓ`-th cyclotomic field
is again Galois, restriction carries its decomposition group into the decomposition group
downstairs and its inertia subgroup onto the inertia subgroup downstairs, and the bound transports
along that homomorphism.  Note that the compositum is no longer an `ℓ`-extension; the transport
only needs the inertia subgroup itself to be an `ℓ`-group, which it is because it is a subgroup of
the Galois group downstairs.

## Main results

* `InverseGalois.CFT.isFrattiniInertiaSmallAt`: **for an odd prime `ℓ`, the image of the abelianized
  inertia subgroup in the Frattini quotient of the abelianized decomposition group has order at
  most `ℓ`** at every prime above `ℓ` of every Galois number field whose Galois group is an
  `ℓ`-group.
* `InverseGalois.CFT.isAbelianInertiaCyclicAt`: **the abelianized inertia subgroup at a prime above
  an odd prime `ℓ` is cyclic**.
* `InverseGalois.CFT.isInertiaRankOneAt`: **the rank one condition at an odd prime**.
* `InverseGalois.CFT.isCentralStepSolvable`: **the central embedding step of the Scholz–Reichardt
  induction is solvable at every odd prime**.

## Tags

inertia subgroup, decomposition group, Frattini quotient, cyclotomic field, Scholz–Reichardt
-/

open NumberField InverseGalois.NumberTheory IntermediateField

open scoped Pointwise

namespace InverseGalois.CFT

set_option synthInstance.maxHeartbeats 800000

variable {ℓ : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The image of the abelianized inertia subgroup in the Frattini quotient of the abelianized
decomposition group has order at most `ℓ`**, at every prime above an odd prime `ℓ` of every Galois
number field whose Galois group is an `ℓ`-group.  Adjoining a primitive `ℓ`-th root of unity puts
the situation within reach of the local dichotomy at a cyclotomic place, and the bound descends
along the restriction homomorphism. -/
theorem isFrattiniInertiaSmallAt (hℓ : ℓ.Prime) (hodd : Odd ℓ) : IsFrattiniInertiaSmallAt ℓ := by
  haveI := Fact.mk hℓ
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hodd2 : ℓ ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  intro A _ _ hM P _ _
  -- the compositum with the `ℓ`-th cyclotomic field
  set M : IntermediateField ℚ (AlgebraicClosure ℚ) := A ⊔ cycSubfield ℓ with hMdef
  haveI : NumberField ↥M := ⟨⟩
  haveI : IsGalois ℚ ↥M := inferInstance
  -- the root of unity, seen inside the compositum
  have hroot : cycRoot ℓ ∈ M :=
    (le_sup_right : cycSubfield ℓ ≤ M)
      (IntermediateField.subset_adjoin ℚ {cycRoot ℓ} rfl)
  have hζ : IsPrimitiveRoot (⟨cycRoot ℓ, hroot⟩ : ↥M) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥M (AlgebraicClosure ℚ))
      (cycRoot_spec ℓ) (algebraMap ↥M (AlgebraicClosure ℚ)).injective
  -- the copy of the given field inside the compositum
  set A₀ : IntermediateField ℚ ↥M :=
    IntermediateField.restrict (le_sup_left : A ≤ M) with hA₀def
  haveI : Normal ℚ ↥A₀ :=
    Normal.of_algEquiv (IntermediateField.restrict_algEquiv (le_sup_left : A ≤ M))
  haveI : NumberField ↥A₀ := ⟨⟩
  set eA : ↥A₀ ≃ₐ[ℚ] ↥A :=
    (IntermediateField.restrict_algEquiv (le_sup_left : A ≤ M)).symm with heA
  -- a prime of the compositum above the given one
  set P₀ : Ideal (𝓞 ↥A₀) := Ideal.comap (mapAlgEquivInt (eA : ↥A₀ ≃+* ↥A)) P with hP₀def
  haveI : P₀.IsPrime := Ideal.comap_isPrime _ _
  haveI : P₀.LiesOver (Ideal.span {(ℓ : ℤ)}) := liesOver_comap_mapAlgEquivInt (p := ℓ) eA P
  obtain ⟨⟨P', hP'prime, hP'over⟩⟩ : Nonempty (Ideal.primesOver P₀ (𝓞 ↥M)) := inferInstance
  haveI : P'.IsPrime := hP'prime
  haveI : P'.LiesOver P₀ := hP'over
  haveI : P'.LiesOver (Ideal.span {(ℓ : ℤ)}) :=
    Ideal.LiesOver.trans P' P₀ (Ideal.span {(ℓ : ℤ)})
  have hunder : P'.under (𝓞 ↥A₀) = P₀ := hP'over.over.symm
  -- restriction carries the decomposition group and the inertia subgroup downstairs
  have hD : ∀ x ∈ MulAction.stabilizer Gal(↥M/ℚ) P',
      (AlgEquiv.autCongr eA) (AlgEquiv.restrictNormalHom ↥A₀ x) ∈
        MulAction.stabilizer Gal(↥A/ℚ) P := by
    intro x hx
    refine (mem_stabilizer_autCongr_iff eA P _).mpr ?_
    have hres := restrictNormal_mem_stabilizer A₀ P' hx
    rwa [hunder] at hres
  have hI : (Ideal.inertia Gal(↥M/ℚ) P').map
      ((AlgEquiv.autCongr eA).toMonoidHom.comp (AlgEquiv.restrictNormalHom ↥A₀)) =
      Ideal.inertia Gal(↥A/ℚ) P := by
    rw [← Subgroup.map_map, map_inertia_eq_inertia A₀ hℓ P', hunder, hP₀def]
    exact map_inertia_autCongr eA P
  exact card_map_abelianization_le_of_primitiveRoot (D := MulAction.stabilizer Gal(↥A/ℚ) P)
    (I := Ideal.inertia Gal(↥A/ℚ) P) hℓ hodd2 hζ P'
    ((AlgEquiv.autCongr eA).toMonoidHom.comp (AlgEquiv.restrictNormalHom ↥A₀))
    (hM.to_subgroup _) hD hI

/-- **The abelianized inertia subgroup at a prime above an odd prime `ℓ` is cyclic** in every
Galois number field whose Galois group is an `ℓ`-group. -/
theorem isAbelianInertiaCyclicAt (hℓ : ℓ.Prime) (hodd : Odd ℓ) : IsAbelianInertiaCyclicAt ℓ :=
  isAbelianInertiaCyclicAt_of_isFrattiniInertiaSmallAt hℓ hodd (isFrattiniInertiaSmallAt hℓ hodd)

/-- **The rank one condition at an odd prime.**  A homomorphism of an `ℓ`-group Galois group whose
values on inertia at a prime over `ℓ` lie in a group of order `ℓ` is determined there by a single
element. -/
theorem isInertiaRankOneAt (hℓ : ℓ.Prime) (hodd : Odd ℓ) : IsInertiaRankOneAt ℓ :=
  isInertiaRankOneAt_of_isAbelianInertiaCyclicAt hℓ (isAbelianInertiaCyclicAt hℓ hodd)

/-- **The central embedding step of the Scholz–Reichardt induction is solvable at every odd prime,
for kernels inside the Frattini subgroup.** -/
theorem isFrattiniCentralStepSolvable (hℓ : ℓ.Prime) (hodd : Odd ℓ) :
    IsFrattiniCentralStepSolvable ℓ :=
  isFrattiniCentralStepSolvable_of_isInertiaRankOneAt hℓ hodd (isInertiaRankOneAt hℓ hodd)

/-- **The central embedding step of the Scholz–Reichardt induction is solvable at every odd
prime.** -/
theorem isCentralStepSolvable (hℓ : ℓ.Prime) (hodd : Odd ℓ) : IsCentralStepSolvable ℓ :=
  isCentralStepSolvable_of_isInertiaRankOneAt hℓ hodd (isInertiaRankOneAt hℓ hodd)

end InverseGalois.CFT
