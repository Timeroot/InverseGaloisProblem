/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Genus.Chart

/-!
# Inertia is a property of the place, not of the chart

The inertia group at a prime of a chart is defined by an ideal of that chart: it collects the
symmetries acting trivially modulo the prime.  The prime, however, is only the shadow in one chart
of an intrinsic object, the place of the field it determines, and the inertia group is the shadow
of an intrinsic condition on the place: a symmetry is inertial there when it moves every function
regular at the place by a function vanishing at it.

That the two agree is the content of this file.  In one direction a symmetry inertial at the place
moves an element of the chart by an element of the chart vanishing at the place, and the functions
of the chart vanishing at a place are exactly its prime.  In the other, a function regular at the
place is a fraction of elements of the chart whose denominator does not vanish there, and the
numerator of the difference of its two conjugates is built from differences of conjugates in the
chart, so it vanishes at the place while the denominator does not.

The consequence is that inertia may be compared across charts: two primes, in possibly different
charts of the same field, that determine the same place have the same inertia group.  This is what
lets the ramification of a cover be discussed without first fixing a coordinate.

## Main definitions

* `Rigidity.RET.IsInertialAtPlace` — a symmetry is inertial at a place when it moves every function
  regular there by a function vanishing there.

## Main results

* `Rigidity.RET.mem_inertia_iff_isInertialAtPlace` — the inertia group of a prime of a chart
  consists of the symmetries inertial at its place.
* `Rigidity.RET.inertia_eq_of_placeSubring_eq` — primes of two charts determining the same place
  have the same inertia group.
-/

open IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section


namespace Rigidity.RET

section PlaceInertia

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]

/-- **A symmetry is inertial at a place** when it moves every function regular there by a function
vanishing there: the induced map of the residue field is the identity. -/
def IsInertialAtPlace (A : ValuationSubring F) (σ : G) : Prop :=
  ∀ x ∈ A, A.valuation (σ • x - x) < 1

variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B F] [IsFractionRing B F]
  [MulSemiringAction G B]

/-- The prime of a chart under the place of that prime is the prime itself. -/
theorem underPrime_placeSubring (v : HeightOneSpectrum B) :
    underPrime (placeSubring F v) (algebraMap_mem_placeSubring F v) = v.asIdeal :=
  congrArg HeightOneSpectrum.asIdeal (underPlace_placeSubring (F := F) v)

/-- An element of the chart vanishes at the place of a prime exactly when it lies in the prime. -/
theorem valuation_lt_one_iff_mem (v : HeightOneSpectrum B) (b : B) :
    (placeSubring F v).valuation (algebraMap B F b) < 1 ↔ b ∈ v.asIdeal := by
  rw [← underPrime_placeSubring (F := F) v]
  exact mem_underPrime.symm

variable (hcomm : ∀ (σ : G) (b : B), algebraMap B F (σ • b) = σ • algebraMap B F b)

include hcomm

/-- A symmetry inertial at the place of a prime lies in the inertia group of that prime: it moves
an element of the chart by an element of the chart vanishing at the place. -/
theorem mem_inertia_of_isInertialAtPlace {v : HeightOneSpectrum B} {σ : G}
    (h : IsInertialAtPlace (placeSubring F v) σ) : σ ∈ Ideal.inertia G v.asIdeal := by
  intro b
  show σ • b - b ∈ v.asIdeal
  rw [← valuation_lt_one_iff_mem (F := F) v, map_sub, hcomm]
  exact h _ (algebraMap_mem_placeSubring F v b)

/-- A symmetry in the inertia group of a prime is inertial at its place: a function regular at the
place is a fraction over the chart with denominator not vanishing there, and the numerator of the
difference of its conjugates vanishes there. -/
theorem isInertialAtPlace_of_mem_inertia {v : HeightOneSpectrum B} {σ : G}
    (h : σ ∈ Ideal.inertia G v.asIdeal) : IsInertialAtPlace (placeSubring F v) σ := by
  set A := placeSubring F v with hA
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  -- write the function as a fraction over the chart with denominator not vanishing at the place
  obtain ⟨a, s, hs, hsa⟩ :=
    exists_den_notMem_of_ord_nonneg F v ((mem_placeSubring F v hx0).mp hx)
  -- the conjugate is the fraction of the conjugates
  have hsa' : algebraMap B F (σ • s) * (σ • x) = algebraMap B F (σ • a) := by
    rw [hcomm, hcomm, ← smul_mul', hsa]
  -- the denominator of the difference does not vanish at the place
  have hσs : σ • s ∉ v.asIdeal := by
    intro hmem
    exact hs (by simpa using v.asIdeal.sub_mem hmem (h s))
  have hd : (σ • s) * s ∉ v.asIdeal := fun hmem =>
    (v.isPrime.mem_or_mem hmem).elim hσs hs
  -- the numerator of the difference vanishes at the place
  have hn : (σ • a) * s - a * (σ • s) ∈ v.asIdeal := by
    have : (σ • a) * s - a * (σ • s) = (σ • a - a) * s - a * (σ • s - s) := by ring
    rw [this]
    exact v.asIdeal.sub_mem (v.asIdeal.mul_mem_right _ (h a)) (v.asIdeal.mul_mem_left _ (h s))
  -- clear denominators in the difference of the conjugates
  have hkey : algebraMap B F ((σ • s) * s) * (σ • x - x)
      = algebraMap B F ((σ • a) * s - a * (σ • s)) := by
    rw [map_sub, map_mul, map_mul, map_mul, mul_sub]
    rw [show algebraMap B F (σ • s) * algebraMap B F s * (σ • x)
        = (algebraMap B F (σ • s) * (σ • x)) * algebraMap B F s by ring, hsa']
    rw [show algebraMap B F (σ • s) * algebraMap B F s * x
        = algebraMap B F (σ • s) * (algebraMap B F s * x) by ring, hsa]
    ring
  -- the denominator is a unit of the place, so the difference has the valuation of the numerator
  have hdval : A.valuation (algebraMap B F ((σ • s) * s)) = 1 := by
    refine le_antisymm (A.valuation_le_one ⟨_, algebraMap_mem_placeSubring F v _⟩) ?_
    exact not_lt.mp fun hlt => hd ((valuation_lt_one_iff_mem (F := F) v _).mp hlt)
  have hval := congrArg A.valuation hkey
  rw [Valuation.map_mul, hdval, one_mul] at hval
  rw [hval]
  exact (valuation_lt_one_iff_mem (F := F) v _).mpr hn

/-- **The inertia group of a prime of a chart consists of the symmetries inertial at its place.**
The prime is the shadow of the place in the chart, and the inertia group is the shadow of an
intrinsic condition. -/
theorem mem_inertia_iff_isInertialAtPlace (v : HeightOneSpectrum B) (σ : G) :
    σ ∈ Ideal.inertia G v.asIdeal ↔ IsInertialAtPlace (placeSubring F v) σ :=
  ⟨isInertialAtPlace_of_mem_inertia hcomm, mem_inertia_of_isInertialAtPlace hcomm⟩

end PlaceInertia

/-! ## Comparing inertia across charts -/

section TwoCharts

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]
  {B₁ B₂ : Type*} [CommRing B₁] [IsDedekindDomain B₁] [Algebra B₁ F] [IsFractionRing B₁ F]
  [MulSemiringAction G B₁] [CommRing B₂] [IsDedekindDomain B₂] [Algebra B₂ F]
  [IsFractionRing B₂ F] [MulSemiringAction G B₂]

/-- **Primes of two charts determining the same place have the same inertia group.**  Ramification
is a property of the place, so it may be read in whichever chart contains it. -/
theorem inertia_eq_of_placeSubring_eq
    (h₁ : ∀ (σ : G) (b : B₁), algebraMap B₁ F (σ • b) = σ • algebraMap B₁ F b)
    (h₂ : ∀ (σ : G) (b : B₂), algebraMap B₂ F (σ • b) = σ • algebraMap B₂ F b)
    (v₁ : HeightOneSpectrum B₁) (v₂ : HeightOneSpectrum B₂)
    (hv : placeSubring F v₁ = placeSubring F v₂) :
    Ideal.inertia G v₁.asIdeal = Ideal.inertia G v₂.asIdeal := by
  ext σ
  rw [mem_inertia_iff_isInertialAtPlace h₁, mem_inertia_iff_isInertialAtPlace h₂, hv]

/-- **A prime whose place contains a second chart has the inertia group of a prime of that chart.**
The place is visible in both charts, and inertia is read off the place. -/
theorem exists_inertia_eq_of_mem_placeSubring
    (h₁ : ∀ (σ : G) (b : B₁), algebraMap B₁ F (σ • b) = σ • algebraMap B₁ F b)
    (h₂ : ∀ (σ : G) (b : B₂), algebraMap B₂ F (σ • b) = σ • algebraMap B₂ F b)
    (v₂ : HeightOneSpectrum B₂)
    (hsub : ∀ b : B₁, algebraMap B₁ F b ∈ placeSubring F v₂) :
    ∃ v₁ : HeightOneSpectrum B₁, Ideal.inertia G v₁.asIdeal = Ideal.inertia G v₂.asIdeal :=
  ⟨underPlace _ hsub (placeSubring_ne_top F v₂),
    inertia_eq_of_placeSubring_eq h₁ h₂ _ v₂
      (placeSubring_underPlace _ hsub (placeSubring_ne_top F v₂))⟩

end TwoCharts

/-! ## Integrality puts a chart inside a place -/

section Integral

variable {F : Type*} [Field F]

/-- **A valuation subring contains everything integral over a ring mapping into it.** -/
theorem mem_of_isIntegral_algebraMap {A : ValuationSubring F} {R : Type*} [CommRing R]
    [Algebra R F] (hR : ∀ r : R, algebraMap R F r ∈ A) {x : F} (hx : IsIntegral R x) : x ∈ A := by
  letI : Algebra R ↥(algebraMap R F).range := (algebraMap R F).rangeRestrict.toAlgebra
  haveI : IsScalarTower R ↥(algebraMap R F).range F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine mem_of_isIntegral (R := (algebraMap R F).range) (fun y hy => ?_) hx.tower_top
  obtain ⟨r, rfl⟩ := hy
  exact hR r

end Integral

end Rigidity.RET
