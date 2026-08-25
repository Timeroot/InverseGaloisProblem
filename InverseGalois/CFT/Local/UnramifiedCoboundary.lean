/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicCoboundary
import InverseGalois.CFT.Local.AdicHerbrand
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Units.FrobeniusPlace

/-!
# Two-cocycles of the decomposition group at an unramified place

At a finite place of a Galois extension of number fields which is unramified over the base, the
decomposition group is cyclic and the norm map on the units of the valuation ring of the completion
is surjective onto the units of the base.  The second cohomology of a finite cyclic group is the
quotient of the invariants by the norms, so it vanishes there: **every two-cocycle of the
decomposition group with values in the units of the valuation ring of the completion is a
coboundary.**

This is the local ingredient which makes all but finitely many places invisible when a global class
is reconstructed from its local components, the places that are left being the ramified ones and
those where the class itself fails to be a unit.

The statement is proved first for an abstract complete valued field carrying a faithful action of a
finite cyclic group which fixes a uniformizer, and then specialised to the completion of a number
field at a finite place.

## Main definitions

* `InverseGalois.CFT.kerUnitValAutHom`: the action on the units of the valuation ring, as a
  homomorphism to the additive automorphisms.

## Main results

* `InverseGalois.CFT.exists_sub_add_eq_kerUnitVal`: **a two-cocycle with values in the units of the
  valuation ring of an unramified extension is a coboundary.**
* `InverseGalois.CFT.exists_sub_add_eq_adicUnits`: **a two-cocycle of the decomposition group at an
  unramified finite place, with values in the units of the valuation ring of the completion there,
  is a coboundary.**

## Tags

local field, unramified, decomposition group, group cohomology, two-cocycle, coboundary
-/

open IsDedekindDomain MulAction NumberField

open scoped WithZero

namespace InverseGalois.CFT

section Hom

variable {G A : Type*} [Group G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

/-- The action on the units of the valuation ring, as a homomorphism to the additive
automorphisms. -/
def kerUnitValAutHom : G →* AddAut ↥(unitVal (A := A)).ker where
  toFun := kerUnitValAut hv
  map_one' := by
    refine AddEquiv.ext fun x => Subtype.ext ?_
    show smulUnitsAut (R := A) (1 : G) (x : Additive Aˣ) = (x : Additive Aˣ)
    rw [map_one]
    rfl
  map_mul' σ τ := by
    refine AddEquiv.ext fun x => Subtype.ext ?_
    show smulUnitsAut (R := A) (σ * τ) (x : Additive Aˣ)
      = smulUnitsAut (R := A) σ (smulUnitsAut (R := A) τ (x : Additive Aˣ))
    rw [map_mul]
    rfl

@[simp]
theorem kerUnitValAutHom_apply (σ : G) (x : ↥(unitVal (A := A)).ker) :
    kerUnitValAutHom hv σ x = kerUnitValAut hv σ x := rfl

end Hom

section Unramified

variable {G A : Type} [Group G] [Fintype G] [Field A] [Valued A ℤᵐ⁰] [MulSemiringAction G A]
  [FaithfulSMul G A] [CompleteSpace A] [∀ j : ℤ, Finite (gradedAdd A j)] {p e : ℕ}
  (hv : ∀ (σ : G) (x : A), Valued.v (σ • x) = Valued.v x)

/-- **A two-cocycle with values in the units of the valuation ring of an unramified extension is a
coboundary.** -/
theorem exists_sub_add_eq_kerUnitVal (h : HasResidueChar A p e) {σ : G}
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) {d : ℕ} [NeZero d] (hσ : σ ^ d = 1)
    (hcard : Nat.card G = d) (π : Aˣ) (hπfix : ∀ g : G, g • (π : A) = (π : A))
    (hπval : unitVal (Additive.ofMul π) = 1)
    {f : G → G → ↥(unitVal (A := A)).ker}
    (hf : ∀ x y z : G, kerUnitValAutHom hv x (f y z) + f x (y * z) = f (x * y) z + f x y) :
    ∃ c : G → ↥(unitVal (A := A)).ker,
      ∀ x y : G, f x y = kerUnitValAutHom hv x (c y) - c (x * y) + c x :=
  exists_sub_add_eq_of_forall_exists_normHom (kerUnitValAutHom hv) hgen hcard
    (fun a ha => exists_normHom_kerUnitVal hv h hgen hσ hcard π hπfix hπval a (ha σ)) hf

end Unramified

section Adic

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (v : HeightOneSpectrum (𝓞 K))

/-- **A two-cocycle of the decomposition group at an unramified place with values in the units of
the valuation ring of the completion is a coboundary.** -/
theorem exists_sub_add_eq_adicUnits (hunr : Algebra.IsUnramifiedAt (𝓞 k) v.asIdeal)
    {f : ↥(stabilizer Gal(K/k) v) → ↥(stabilizer Gal(K/k) v) →
      ↥(unitVal (A := v.adicCompletion K)).ker}
    (hf : ∀ x y z : ↥(stabilizer Gal(K/k) v),
      kerUnitValAutHom (valued_smul_adicCompletion v) x (f y z) + f x (y * z)
        = f (x * y) z + f x y) :
    ∃ c : ↥(stabilizer Gal(K/k) v) → ↥(unitVal (A := v.adicCompletion K)).ker,
      ∀ x y : ↥(stabilizer Gal(K/k) v),
        f x y = kerUnitValAutHom (valued_smul_adicCompletion v) x (c y) - c (x * y) + c x := by
  classical
  haveI : Fintype ↥(stabilizer Gal(K/k) v) := Fintype.ofFinite _
  haveI hcyc : IsCyclic ↥(stabilizer Gal(K/k) v) := isCyclic_stabilizer_of_isUnramifiedAt v hunr
  obtain ⟨σ, hgen⟩ := hcyc.exists_generator
  obtain ⟨p, e, hres⟩ := exists_hasResidueChar_adicCompletion v
  obtain ⟨π, hπfix, hπval⟩ := exists_fixedUniformizer_of_isUnramifiedAt (k := k) v hunr
  set d : ℕ := Nat.card ↥(stabilizer Gal(K/k) v) with hd
  haveI : NeZero d := ⟨Nat.card_pos.ne'⟩
  exact exists_sub_add_eq_kerUnitVal (valued_smul_adicCompletion v) hres hgen
    (pow_card_eq_one' (G := ↥(stabilizer Gal(K/k) v))) rfl π hπfix hπval hf

end Adic

end InverseGalois.CFT
