/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Scholz.AuxPrimeField
import InverseGalois.CFT.Scholz.DyadicClassStep
import InverseGalois.CFT.Scholz.DyadicShrink

/-!
# The data of a rung of the dyadic induction

A turn of the dyadic Scholz–Reichardt induction starts from a strong Scholz realization of the free
object of one class and a field above it realising the free object of the next class, ramifying
harmlessly over the realization: every prime it ramifies at is either ramified below or congruent
to one modulo the level and split completely below.  That package is what the shrinking process and
the residue correction consume, and it is what the uncorrected solution of the rung produces.

Shrinking acts on the whole package at once.  A vector of bits collapses the free object of rank
`d * r` onto the free object of rank `d`, at both classes at the same time and compatibly with the
projection between them, so it cuts a subfield out of the realization and a subfield out of the
field above it, the first inside the second.  Harmless ramification survives: a prime ramified in
the shrunken solution is ramified in the large realization or split completely in it, and in the
first case it splits completely in the shrunken realization because the large realization has split
inertia, while in the second it splits completely there because splitting completely descends to
subfields.

## Main definitions

* `InverseGalois.CFT.ClassStepData`: a strong Scholz realization together with a field above it
  realising the free object of the next class and ramifying harmlessly over it.
* `InverseGalois.CFT.solutionCollapse`: the homomorphism cutting the shrunken solution out of the
  field above.
* `InverseGalois.CFT.ClassStepData.shrink`: **the shrinking of a rung along a vector of bits.**

## Main results

* `InverseGalois.CFT.nonempty_classStepData`: **the uncorrected solution of the rung is a rung of
  the induction.**

## Tags

Scholz–Reichardt, `2`-class, free object, shrinking, harmless ramification, Shafarevich
-/

open NumberField InverseGalois.NumberTheory

namespace InverseGalois.CFT

/-! ### A rung of the induction -/

/-- **A rung of the dyadic Scholz–Reichardt induction**: a strong Scholz realization of the free
object of rank `d` and `2`-class `c`, together with a field above it realising the free object of
`2`-class `c + 1` over it and ramifying harmlessly over it. -/
structure ClassStepData (d c N : ℕ) where
  /-- The strong Scholz realization the rung stands on. -/
  base : StrongScholzRealization d c N
  /-- The field realising the free object of the next class. -/
  top : IntermediateField ℚ (AlgebraicClosure ℚ)
  [numberField : NumberField ↥top]
  [isGalois : IsGalois ℚ ↥top]
  /-- The field above contains the realization below. -/
  le : base.carrier ≤ top
  /-- The field above ramifies harmlessly over the realization below. -/
  ramified : IsScholzOver 2 N ↥base.carrier ↥top
  /-- The Galois group of the field above is the free object of the next class. -/
  galEquiv : Gal(↥top/ℚ) ≃* FreePClass 2 d (c + 1)
  /-- The identification is compatible with the projection of the tower of free objects. -/
  comp : ∀ τ, FreePClass.proj 2 d c (galEquiv τ) = base.galEquiv (galRestrictLE le τ)

attribute [instance] ClassStepData.numberField ClassStepData.isGalois

/-- **The uncorrected solution of the rung is a rung of the induction.**  It ramifies nowhere
outside the realization it stands on, which is harmless ramification of the crudest kind. -/
theorem nonempty_classStepData {δ c N : ℕ} (hc : 1 ≤ c)
    (hdvd : Nat.card (FreePClass 2 δ c) ∣ 2 ^ N) (R : StrongScholzRealization δ c (N + 1)) :
    Nonempty (ClassStepData δ c (N + 1)) := by
  obtain ⟨L, hAL, hNF, hGal, hram, -, ψ, hcomp⟩ := exists_uncorrected_classStep hc hdvd R
  haveI := hNF
  haveI := hGal
  exact ⟨{ base := R, top := L, le := hAL, ramified := IsScholzOver.of_subset hram,
           galEquiv := ψ, comp := hcomp }⟩

/-! ### Collapsing the field above -/

/-- The homomorphism onto the free object of the smaller rank whose fixed field carries the
shrunken solution. -/
noncomputable def solutionCollapse {d r n : ℕ} {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [NumberField ↥L] [IsGalois ℚ ↥L] (ψ : Gal(↥L/ℚ) ≃* FreePClass 2 (d * r) (n + 1 + 1))
    (a : Fin r → ZMod 2) : Gal(↥L/ℚ) →* FreePClass 2 d (n + 1 + 1) :=
  (FreePClass.collapse a).comp ψ.toMonoidHom

theorem solutionCollapse_apply {d r n : ℕ} {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [NumberField ↥L] [IsGalois ℚ ↥L] (ψ : Gal(↥L/ℚ) ≃* FreePClass 2 (d * r) (n + 1 + 1))
    (a : Fin r → ZMod 2) (σ : Gal(↥L/ℚ)) :
    solutionCollapse ψ a σ = FreePClass.collapse a (ψ σ) := rfl

theorem solutionCollapse_surjective {d r n : ℕ} {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [NumberField ↥L] [IsGalois ℚ ↥L] (ψ : Gal(↥L/ℚ) ≃* FreePClass 2 (d * r) (n + 1 + 1))
    (a : Fin r → ZMod 2) {j₀ : Fin r} (hj₀ : a j₀ = 1) :
    Function.Surjective (solutionCollapse (d := d) ψ a) :=
  (FreePClass.collapse_surjective hj₀).comp ψ.surjective

/-! ### Shrinking a rung -/

namespace ClassStepData

variable {d r n N : ℕ} (D : ClassStepData (d * r) (n + 1) N) (a : Fin r → ZMod 2)

/-- **The shrunken realization lies inside the shrunken solution.**  An automorphism of the field
above killed by the collapse restricts to an automorphism of the realization below killed by the
collapse, because the collapse commutes with the projection of the tower. -/
theorem shrink_le : kerField (D.base.collapseHom a) ≤ kerField (solutionCollapse D.galEquiv a) := by
  refine kerField_le_kerField D.le (D.base.collapseHom a) (solutionCollapse D.galEquiv a)
    (FreePClass.proj 2 d (n + 1)) fun τ => ?_
  show FreePClass.collapse a (D.base.galEquiv (galRestrictLE D.le τ))
    = FreePClass.proj 2 d (n + 1) (FreePClass.collapse a (D.galEquiv τ))
  rw [← D.comp τ]
  exact (DFunLike.congr_fun (FreePClass.proj_comp_collapse n d r a) (D.galEquiv τ)).symm

/-- **The shrunken solution ramifies harmlessly over the shrunken realization.**  A prime ramified
in it is ramified in the field above, hence either ramified in the realization below — where split
inertia makes it split completely in the shrunken realization it does not ramify in — or already
split completely in the realization below, hence in every subfield of it. -/
theorem shrink_ramified : IsScholzOver 2 N ↥(kerField (D.base.collapseHom a))
    ↥(kerField (solutionCollapse D.galEquiv a)) := by
  intro q hq
  have hqL : q ∈ ramifiedSet ↥D.top :=
    ramifiedSet_of_le (kerField_le (solutionCollapse D.galEquiv a)) hq
  by_cases hK : q ∈ ramifiedSet ↥(kerField (D.base.collapseHom a))
  · exact Or.inl hK
  · refine Or.inr ?_
    rcases D.ramified q hqL with hB | ⟨hmod, hsplit⟩
    · exact ⟨D.base.isScholz.1 q hB,
        splitsCompletely_of_notMem_ramifiedSet_of_le (kerField_le (D.base.collapseHom a))
          D.base.isScholz.2 hB hK⟩
    · exact ⟨hmod, splitsCompletely_of_le (kerField_le (D.base.collapseHom a)) hq.1 hsplit⟩

/-- **The identification of the Galois group of the shrunken solution is compatible with the
projection of the tower**, over the shrunken realization. -/
theorem shrink_comp {j₀ : Fin r} (hj₀ : a j₀ = 1)
    (τ : Gal(↥(kerField (solutionCollapse D.galEquiv a))/ℚ)) :
    FreePClass.proj 2 d (n + 1) (galEquivKerField (solutionCollapse D.galEquiv a)
        (solutionCollapse_surjective D.galEquiv a hj₀) τ)
      = (D.base.shrink a hj₀).galEquiv (galRestrictLE (D.shrink_le a) τ) := by
  obtain ⟨σ, rfl⟩ := galRestrictLE_surjective (kerField_le (solutionCollapse D.galEquiv a)) τ
  have hK : galRestrictLE (D.shrink_le a)
        (galRestrictLE (kerField_le (solutionCollapse D.galEquiv a)) σ)
      = galRestrictLE (D.base.shrink_carrier_le a hj₀) (galRestrictLE D.le σ) := by
    rw [galRestrictLE_galRestrictLE, galRestrictLE_galRestrictLE]
    rfl
  rw [galEquivKerField_galRestrictLE, hK, D.base.shrink_galEquiv_galRestrictLE a hj₀, ← D.comp σ]
  exact DFunLike.congr_fun (FreePClass.proj_comp_collapse n d r a) (D.galEquiv σ)

/-- **The shrinking of a rung along a vector of bits**: the fixed field of the collapse inside the
realization below, and the fixed field of the collapse inside the field above. -/
noncomputable def shrink {j₀ : Fin r} (hj₀ : a j₀ = 1) : ClassStepData d (n + 1) N where
  base := D.base.shrink a hj₀
  top := kerField (solutionCollapse D.galEquiv a)
  le := D.shrink_le a
  ramified := D.shrink_ramified a
  galEquiv := galEquivKerField (solutionCollapse D.galEquiv a)
    (solutionCollapse_surjective D.galEquiv a hj₀)
  comp := D.shrink_comp a hj₀

@[simp] theorem shrink_base {j₀ : Fin r} (hj₀ : a j₀ = 1) :
    (D.shrink a hj₀).base = D.base.shrink a hj₀ := rfl

@[simp] theorem shrink_top {j₀ : Fin r} (hj₀ : a j₀ = 1) :
    (D.shrink a hj₀).top = kerField (solutionCollapse D.galEquiv a) := rfl

end ClassStepData

end InverseGalois.CFT
