/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Brauer.LocalInvariant
import InverseGalois.CFT.Brauer.UnramifiedCompositum

/-!
# The invariant map of a local field

Every Brauer class over a local field is split by a finite unramified extension, the normalised
invariant of a class computed in one unramified splitting field agrees with the invariant computed
in a larger one, and the compositum of two unramified extensions is unramified.  Placing the
splitting fields inside a fixed algebraic closure therefore makes the family of unramified
splitting fields of a class directed, and the normalised invariant of a class does not depend on
which one is used to compute it.

The resulting map is **the invariant map** of the local field: a homomorphism from the whole Brauer
group to the rationals modulo the integers, computing the normalised invariant of every unramified
extension at once.

## Main definitions

* `InverseGalois.CFT.UnramifiedSubfield`: a finite unramified extension of a local field inside a
  fixed algebraic closure.
* `InverseGalois.CFT.localInvariantHom`: **the invariant map of a local field.**

## Main results

* `InverseGalois.CFT.unramified_of_algEquiv`: an extension isomorphic to an unramified extension is
  unramified.
* `InverseGalois.CFT.UnramifiedSubfield.invariant_eq`: **the normalised invariant does not depend on
  the unramified splitting field.**
* `InverseGalois.CFT.exists_unramifiedSubfield_mem_relative`: **every Brauer class over a local
  field is split by a finite unramified extension inside a fixed algebraic closure.**
* `InverseGalois.CFT.localInvariantHom_apply_of_unramified`: **the invariant map computes the
  normalised invariant of every unramified extension.**

## Tags

Brauer group, local field, unramified extension, invariant map, class field theory
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open Module

open scoped Valued WithZero

/-! ### Transporting unramifiedness along an isomorphism -/

section Transport

universe u

variable {K L L' : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
variable [Field L] [Algebra K L] [FiniteDimensional K L] [Field L'] [Algebra K L']

/-- **An extension isomorphic to an unramified extension is unramified.**  An isomorphism is a
tower of height one, and the absolute value of an intermediate field of a tower is the restriction
of the absolute value of the top field. -/
theorem unramified_of_algEquiv (e : L ≃ₐ[K] L')
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖) :
    ∀ z : L', z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L' z = ‖c‖ := by
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  letI : Algebra L L' := (e : L →ₐ[K] L').toRingHom.toAlgebra
  haveI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  intro z hz
  obtain ⟨c, hc, hcz⟩ := hur (e.symm z) (by simpa using hz)
  refine ⟨c, hc, ?_⟩
  have hz' : algebraMap L L' (e.symm z) = z := e.apply_symm_apply z
  rw [← hz', divisionNorm_algebraMap_tower, hcz]

end Transport

variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰)] [CompleteSpace K] [ProperSpace K] {m : ℤ}

/-! ### The unramified subextensions of an algebraic closure -/

variable (K) in
/-- A finite unramified extension of a local field inside a fixed algebraic closure. -/
structure UnramifiedSubfield where
  /-- The underlying intermediate field of the algebraic closure. -/
  carrier : IntermediateField K (AlgebraicClosure K)
  /-- The extension is finite. -/
  finiteDimensional : FiniteDimensional K carrier
  /-- Every absolute value of the extension is an absolute value of the base field. -/
  unramified : ∀ z : ↥carrier, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K ↥carrier z = ‖c‖

attribute [instance] UnramifiedSubfield.finiteDimensional

namespace UnramifiedSubfield

instance isGalois (F : UnramifiedSubfield K) : IsGalois K ↥F.carrier :=
  isGalois_of_unramified K ↥F.carrier F.unramified

/-- The compositum of two finite unramified extensions inside a fixed algebraic closure. -/
def sup (F G : UnramifiedSubfield K) : UnramifiedSubfield K where
  carrier := F.carrier ⊔ G.carrier
  finiteDimensional := inferInstance
  unramified := unramified_sup F.carrier G.carrier F.unramified G.unramified

omit [CompleteSpace K] in
@[simp]
theorem sup_carrier (F G : UnramifiedSubfield K) : (F.sup G).carrier = F.carrier ⊔ G.carrier := rfl

/-! ### The invariant computed in one unramified splitting field -/

/-- The normalised invariant of a Brauer class split by a finite unramified extension inside a
fixed algebraic closure. -/
noncomputable def invariant (F : UnramifiedSubfield K) (hm : IsUnitValGen K m) :
    ↥(BrauerGroup.relative K ↥F.carrier) →* Multiplicative QModZ :=
  localInvariant K ↥F.carrier F.unramified hm

/-- **The invariant computed in a larger unramified extension agrees with the invariant computed in
a smaller one.** -/
theorem invariant_mono {F G : UnramifiedSubfield K} (h : F.carrier ≤ G.carrier)
    (hm : IsUnitValGen K m) (x : ↥(BrauerGroup.relative K ↥F.carrier)) :
    G.invariant hm ⟨(x : BrauerGroup K), BrauerGroup.relative_mono h x.2⟩ = F.invariant hm x := by
  letI : Algebra ↥F.carrier ↥G.carrier := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K ↥F.carrier ↥G.carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localInvariant_tower G.unramified hm x

/-- **The normalised invariant does not depend on the unramified splitting field.**  Two unramified
splitting fields both sit inside their compositum, which is again unramified. -/
theorem invariant_eq (F G : UnramifiedSubfield K) (hm : IsUnitValGen K m) (x : BrauerGroup K)
    (hF : x ∈ BrauerGroup.relative K ↥F.carrier) (hG : x ∈ BrauerGroup.relative K ↥G.carrier) :
    F.invariant hm ⟨x, hF⟩ = G.invariant hm ⟨x, hG⟩ := by
  rw [← invariant_mono (F := F) (G := F.sup G) le_sup_left hm ⟨x, hF⟩,
    ← invariant_mono (F := G) (G := F.sup G) le_sup_right hm ⟨x, hG⟩]

end UnramifiedSubfield

/-! ### Every class has an unramified splitting field in the algebraic closure -/

omit [CompleteSpace K] in
variable (K) in
/-- **Every Brauer class over a local field is split by a finite unramified extension inside a
fixed algebraic closure.**  The class is split by some unramified extension, and an extension of a
local field is algebraic, so it embeds into the algebraic closure; unramifiedness and the splitting
are carried along the embedding. -/
theorem exists_unramifiedSubfield_mem_relative (x : BrauerGroup K) :
    ∃ F : UnramifiedSubfield K, x ∈ BrauerGroup.relative K ↥F.carrier := by
  obtain ⟨L, hLfield, hLalg, hLfin, -, -, hval, hmem⟩ := exists_cyclic_unramified_mem_relative K x
  letI : Field L := hLfield
  letI : Algebra K L := hLalg
  haveI : FiniteDimensional K L := hLfin
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖ := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := hval z hz
    exact ⟨c, hc, by rw [divisionNorm_eq_spectralNorm, hcz]⟩
  obtain ⟨φ⟩ : Nonempty (L →ₐ[K] AlgebraicClosure K) := ⟨IsAlgClosed.lift⟩
  let e : L ≃ₐ[K] ↥φ.fieldRange := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional K ↥φ.fieldRange := e.toLinearEquiv.finiteDimensional
  letI : Algebra L ↥φ.fieldRange := (e : L →ₐ[K] ↥φ.fieldRange).toRingHom.toAlgebra
  haveI : IsScalarTower K L ↥φ.fieldRange :=
    IsScalarTower.of_algebraMap_eq fun y => (e.commutes y).symm
  exact ⟨⟨φ.fieldRange, inferInstance, unramified_of_algEquiv e hur⟩,
    BrauerGroup.relative_le_relative K L ↥φ.fieldRange hmem⟩

/-! ### The invariant map -/

variable (K) in
/-- **The invariant of a Brauer class over a local field**: the normalised invariant computed in
any finite unramified splitting field inside a fixed algebraic closure. -/
noncomputable def localInvariantMap (hm : IsUnitValGen K m) (x : BrauerGroup K) :
    Multiplicative QModZ :=
  (exists_unramifiedSubfield_mem_relative K x).choose.invariant hm
    ⟨x, (exists_unramifiedSubfield_mem_relative K x).choose_spec⟩

/-- **The invariant of a Brauer class is computed by any unramified splitting field.** -/
theorem localInvariantMap_eq (hm : IsUnitValGen K m) (F : UnramifiedSubfield K) (x : BrauerGroup K)
    (hx : x ∈ BrauerGroup.relative K ↥F.carrier) :
    localInvariantMap K hm x = F.invariant hm ⟨x, hx⟩ :=
  UnramifiedSubfield.invariant_eq _ _ hm x _ hx

/-- The invariant of the trivial class is trivial. -/
theorem localInvariantMap_one (hm : IsUnitValGen K m) : localInvariantMap K hm 1 = 1 := by
  obtain ⟨F, -⟩ := exists_unramifiedSubfield_mem_relative K 1
  rw [localInvariantMap_eq hm F 1 (one_mem _)]
  exact map_one (F.invariant hm)

/-- **The invariant of a product of Brauer classes is the product of the invariants**, because two
classes are split by a common unramified extension, namely the compositum of two splitting
fields. -/
theorem localInvariantMap_mul (hm : IsUnitValGen K m) (x y : BrauerGroup.{0, 0} K) :
    localInvariantMap K hm (x * y) = localInvariantMap K hm x * localInvariantMap K hm y := by
  obtain ⟨F, hF⟩ := exists_unramifiedSubfield_mem_relative K x
  obtain ⟨G, hG⟩ := exists_unramifiedSubfield_mem_relative K y
  have hx : x ∈ BrauerGroup.relative K ↥(F.sup G).carrier :=
    BrauerGroup.relative_mono le_sup_left hF
  have hy : y ∈ BrauerGroup.relative K ↥(F.sup G).carrier :=
    BrauerGroup.relative_mono le_sup_right hG
  have hprod : (⟨x * y, mul_mem hx hy⟩ : ↥(BrauerGroup.relative K ↥(F.sup G).carrier))
      = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hmap : (F.sup G).invariant hm (⟨x, hx⟩ * ⟨y, hy⟩)
      = (F.sup G).invariant hm ⟨x, hx⟩ * (F.sup G).invariant hm ⟨y, hy⟩ :=
    map_mul ((F.sup G).invariant hm) _ _
  rw [localInvariantMap_eq hm (F.sup G) x hx, localInvariantMap_eq hm (F.sup G) y hy,
    localInvariantMap_eq hm (F.sup G) (x * y) (mul_mem hx hy), hprod, hmap]

variable (K) in
/-- **The invariant map of a local field**: the invariant of a Brauer class, as a homomorphism on
the whole Brauer group. -/
noncomputable def localInvariantHom (hm : IsUnitValGen K m) :
    BrauerGroup.{0, 0} K →* Multiplicative QModZ where
  toFun := localInvariantMap K hm
  map_one' := localInvariantMap_one hm
  map_mul' := localInvariantMap_mul hm

@[simp]
theorem localInvariantHom_apply (hm : IsUnitValGen K m) (x : BrauerGroup.{0, 0} K) :
    localInvariantHom K hm x = localInvariantMap K hm x := rfl

/-- **The invariant map computes the normalised invariant of every unramified extension.**  An
unramified extension embeds into the algebraic closure, and the invariant does not change along an
isomorphism because an isomorphism is a tower of height one. -/
theorem localInvariantHom_apply_of_unramified {L : Type} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hm : IsUnitValGen K m)
    (hur : ∀ z : L, z ≠ 0 → ∃ c : K, c ≠ 0 ∧ divisionNorm K L z = ‖c‖)
    (x : ↥(BrauerGroup.relative K L)) :
    localInvariantHom K hm (x : BrauerGroup K) = localInvariant K L hur hm x := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨φ⟩ : Nonempty (L →ₐ[K] AlgebraicClosure K) := ⟨IsAlgClosed.lift⟩
  let e : L ≃ₐ[K] ↥φ.fieldRange := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional K ↥φ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois K ↥φ.fieldRange :=
    isGalois_of_unramified K ↥φ.fieldRange (unramified_of_algEquiv e hur)
  letI : Algebra L ↥φ.fieldRange := (e : L →ₐ[K] ↥φ.fieldRange).toRingHom.toAlgebra
  haveI : IsScalarTower K L ↥φ.fieldRange :=
    IsScalarTower.of_algebraMap_eq fun y => (e.commutes y).symm
  show localInvariantMap K hm (x : BrauerGroup K) = _
  refine (localInvariantMap_eq hm ⟨φ.fieldRange, inferInstance, unramified_of_algEquiv e hur⟩
    (x : BrauerGroup K) (BrauerGroup.relative_le_relative K L ↥φ.fieldRange x.2)).trans ?_
  exact localInvariant_tower (unramified_of_algEquiv e hur) hm x

end InverseGalois.CFT
