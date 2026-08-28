/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Local.AdicUnramified
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.IdeleClass

/-!
# The first inequality of class field theory

For a cyclic extension of number fields the Herbrand quotient of the idele class group is the
degree.  The computation of that quotient needs a finite set of places, invariant under the Galois
group, that is large enough in two independent ways: it must contain the finitely many ramified
places, so that everywhere outside it the local units contribute nothing to the cohomology, and it
must contain the finitely many places needed to represent the ideal classes, so that outside it
every system of orders is realised by an element of the field.  Both sets are finite and both can
be enlarged to invariant sets, so a set with both properties exists.

The inequality itself is the immediate consequence: the order of the zeroth Tate group of the idele
class group is the degree times the order of the other one, hence at least the degree.

## Main results

* `InverseGalois.CFT.exists_finite_stable_superset`: every finite subset of a set with a finite
  group action is contained in a finite invariant one.
* `InverseGalois.CFT.exists_ramification_and_class_set`: **a finite invariant set of places
  containing the ramified places and representing the ideal classes.**
* `InverseGalois.CFT.herbrand_ideleClassAut_eq_degree`: **the idele class group of a cyclic
  extension has Herbrand quotient the degree.**
* `InverseGalois.CFT.first_inequality`: **the first inequality**, that the order of the zeroth Tate
  group of the idele class group is at least the degree.

## Tags

class field theory, first inequality, idele class group, Herbrand quotient, cyclic extension
-/

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField Rigidity.RET

/-! ### Invariant finite sets -/

section Stable

variable {G X : Type*} [Group G] [MulAction G X] [Finite G]

/-- **Every finite subset is contained in a finite invariant one**, namely the union of its
translates. -/
theorem exists_finite_stable_superset (S : Set X) (hS : S.Finite) :
    ∃ T : Set X, S ⊆ T ∧ T.Finite ∧ ∀ (g : G) (x : X), g • x ∈ T ↔ x ∈ T := by
  refine ⟨⋃ g : G, (fun x => g • x) '' S,
    fun x hx => Set.mem_iUnion.mpr ⟨1, x, hx, one_smul G x⟩,
    Set.finite_iUnion fun g => hS.image _, fun g x => ?_⟩
  constructor
  · rintro hgx
    obtain ⟨s, w, hw, hwx⟩ := Set.mem_iUnion.mp hgx
    refine Set.mem_iUnion.mpr ⟨g⁻¹ * s, w, hw, ?_⟩
    show (g⁻¹ * s) • w = x
    rw [mul_smul, show s • w = g • x from hwx, inv_smul_smul]
  · rintro hx
    obtain ⟨s, w, hw, hwx⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨g * s, w, hw, ?_⟩
    show (g * s) • w = g • x
    rw [mul_smul, show s • w = x from hwx]

/-- The action of the group on an invariant subset. -/
def stableAction {T : Set X} (hT : ∀ (g : G) (x : X), g • x ∈ T ↔ x ∈ T) : MulAction G ↥T where
  smul g x := ⟨g • (x : X), (hT g (x : X)).mpr x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : X))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : X))

end Stable

/-! ### A set of places carrying the ramification and the ideal classes -/

section GoodSet

variable (k : Type*) {K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Finite Gal(K/k)]

/-- **A finite invariant set of places containing the ramified places and representing the ideal
classes.**  Only finitely many places fail to carry a uniformizer fixed by the decomposition group,
and finitely many places suffice to represent every system of orders; enlarging the union of the
two to the union of its translates keeps it finite and makes it invariant. -/
theorem exists_ramification_and_class_set :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      (∀ (g : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), g • v ∈ T ↔ v ∈ T) ∧
      (∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
        (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
        ∃ a : Kˣ, ∀ v ∉ T, ord K v (a : K) = m v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T →
        ∃ π : (v.adicCompletion K)ˣ,
          (∀ g : ↥(stabilizer Gal(K/k) v),
              g • (π : v.adicCompletion K) = (π : v.adicCompletion K))
            ∧ unitVal (Additive.ofMul π) = 1) := by
  obtain ⟨T₀, hT₀fin, hT₀stable, hT₀repr⟩ := exists_finite_stable_ord_repr (k := k) (K := K)
  obtain ⟨T₁, hT₁sub, hT₁fin, hT₁stable⟩ := exists_finite_stable_superset (G := Gal(K/k)) _
    (finite_setOf_not_exists_fixedUniformizer k (K := K))
  refine ⟨T₀ ∪ T₁, hT₀fin.union hT₁fin, fun g v => ?_, fun m hm => ?_, fun v hv => ?_⟩
  · rw [Set.mem_union, Set.mem_union, hT₀stable, hT₁stable]
  · obtain ⟨a, ha⟩ := hT₀repr m hm
    exact ⟨a, fun v hv => ha v fun h => hv (Or.inl h)⟩
  · exact not_not.mp fun h => (fun hh => hv (Or.inr hh)) (hT₁sub h)

end GoodSet

/-! ### The Herbrand quotient of the idele class group -/

section Cyclic

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [IsGalois k K] (σ : Gal(K/k)) {n : ℕ} (hn : Nat.card Gal(K/k) = n) [NeZero n]
  (hgen : ∀ g : Gal(K/k), g ∈ Subgroup.zpowers σ)

include hn hgen

/-- **The idele class group of a cyclic extension of number fields has Herbrand quotient the degree
of the extension.** -/
theorem herbrand_ideleClassAut_eq_degree :
    herbrand (ideleClassAut (k := k) (K := K) σ) n = n := by
  classical
  obtain ⟨T, hTfin, hTstable, hTrepr, hTunram⟩ := exists_ramification_and_class_set k (K := K)
  letI : MulAction Gal(K/k) ↥T := stableAction hTstable
  letI : Fintype ↥T := hTfin.fintype
  letI : Fintype (orbitRel.Quotient Gal(K/k) ↥T) := Fintype.ofFinite _
  have hrange : Set.range (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)) = T := Subtype.range_coe
  refine herbrand_ideleClassAut (ι := (Subtype.val : ↥T → HeightOneSpectrum (𝓞 K)))
    (fun _ _ => rfl) σ hn ?_ Subtype.val_injective ?_ hgen
  · rw [hrange]
    exact hTrepr
  · rw [hrange]
    exact hTunram

/-- **The first inequality of class field theory**: for a cyclic extension of number fields the
order of the zeroth Tate group of the idele class group is at least the degree.  Its order is the
degree times the order of the other Tate group, and both are finite because the quotient of the two
is a positive rational. -/
theorem first_inequality :
    n ≤ Nat.card (tateH0 (ideleClassAut (k := k) (K := K) σ) n) := by
  have hq := herbrand_ideleClassAut_eq_degree σ hn hgen
  have hne : herbrand (ideleClassAut (k := k) (K := K) σ) n ≠ 0 := by
    rw [hq]
    exact_mod_cast (NeZero.ne n)
  obtain ⟨h0, h1⟩ := finite_tate_of_herbrand_ne_zero _ n hne
  have hpos : 0 < Nat.card (tateHm1 (ideleClassAut (k := k) (K := K) σ) n) :=
    Nat.card_pos (α := tateHm1 (ideleClassAut (k := k) (K := K) σ) n)
  rw [herbrand, div_eq_iff (by exact_mod_cast hpos.ne')] at hq
  have : (n : ℚ) * 1 ≤ (n : ℚ) * Nat.card (tateHm1 (ideleClassAut (k := k) (K := K) σ) n) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
    exact_mod_cast hpos
  rw [mul_one, ← hq] at this
  exact_mod_cast this

end Cyclic

end InverseGalois.CFT
