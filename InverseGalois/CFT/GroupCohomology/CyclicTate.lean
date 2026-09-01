/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicH1
import InverseGalois.CFT.GroupCohomology.CyclicH2
import InverseGalois.CFT.Tate.Basic

/-!
# The second cohomology of a cyclic group and the Tate group of a generator

Two descriptions of the same subquotient are in use.  A representation of a finite cyclic group on
an abelian group has a second cohomology group, and the classical computation identifies it with
the invariants modulo the norms.  A single additive automorphism of an abelian group, together with
an exponent killing it, has a Tate group in degree zero, the fixed points modulo the image of the
norm operator.  For the automorphism by which a generator acts, and for the exponent the order of
the group, the two are the same subquotient of the same abelian group.

The identification is carried out here.  The invariants of the whole group are the fixed points of
a generator, because every element of the group is a power of the generator; and the norm of the
group action is the norm operator of the generator, because the powers of the generator below the
order of the group enumerate the group.  So the isomorphism between the second cohomology and the
invariants modulo the norms becomes an isomorphism between the second cohomology and the Tate group
of the generator.

A representation over the integers is an action by multiplicative automorphisms of the
multiplicative copy of the underlying group, and the two carry the same cohomology; the integral
module structure of a representation is unique, so the comparison is an isomorphism of
representations even when it is not an equality.

The point of the identification is that the arithmetic of a cyclic extension of number fields is
developed for a single automorphism, whereas the machinery of complete cohomology is developed for
representations of the whole group; this is the dictionary between them.

## Main definitions

* `InverseGalois.CFT.repMulDistribMulAction`: a representation on an abelian group, read as an
  action by multiplicative automorphisms of the multiplicative copy of that group.
* `InverseGalois.CFT.repIso`: the resulting representation is the representation one started with.
* `InverseGalois.CFT.tateH0ToH2`: the map from the fixed points of a generator to the second
  cohomology.

## Main results

* `InverseGalois.CFT.mem_invariantsSubgroup_ofAdd_iff`: **the invariants of a finite cyclic group
  are the fixed points of a generator.**
* `InverseGalois.CFT.prod_smul_eq_ofAdd_normHom`: **the norm of a finite cyclic group is the norm
  operator of a generator.**
* `InverseGalois.CFT.tateH0AddEquivH2`: **the Tate group of a generator is the second cohomology of
  a finite cyclic group.**
* `InverseGalois.CFT.card_H2_eq_card_tateH0`: the two have the same number of elements.

## Tags

group cohomology, cyclic group, Tate cohomology, Herbrand quotient
-/

namespace InverseGalois.CFT

open groupCohomology CyclicH2

noncomputable section

variable {G : Type} [Group G]

/-! ### A representation as an action by multiplicative automorphisms -/

/-- A representation of a group on an abelian group, read as an action by multiplicative
automorphisms of the multiplicative copy of that group. -/
def repMulDistribMulAction (A : Rep ℤ G) : MulDistribMulAction G (Multiplicative ↥A.V) where
  smul g x := Multiplicative.ofAdd (A.ρ g (Multiplicative.toAdd x))
  one_smul x := by
    show Multiplicative.ofAdd (A.ρ 1 (Multiplicative.toAdd x)) = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    show Multiplicative.ofAdd (A.ρ (g * h) (Multiplicative.toAdd x)) = _
    rw [map_mul]
    rfl
  smul_one g := by
    show Multiplicative.ofAdd (A.ρ g (0 : ↥A.V)) = 1
    rw [map_zero]
    rfl
  smul_mul g x y := by
    show Multiplicative.ofAdd
      (A.ρ g (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [map_add]
    rfl

attribute [local instance] repMulDistribMulAction

/-- The action attached to a representation is the representation. -/
theorem smul_ofAdd (A : Rep ℤ G) (g : G) (x : ↥A.V) :
    g • Multiplicative.ofAdd x = Multiplicative.ofAdd (A.ρ g x) := rfl

/-- The multiplicative copy of the group underlying a representation, made additive again, is that
group: an integral module structure on an abelian group is unique. -/
def repLinearEquiv (A : Rep ℤ G) : Additive (Multiplicative ↥A.V) ≃ₗ[ℤ] ↥A.V where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  map_add' _ _ := rfl
  map_smul' r x := (Int.cast_smul_eq_zsmul (R := ℤ) r
    (Multiplicative.toAdd (Additive.toMul x))).symm
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The representation attached to the action attached to a representation is the representation
one started with.** -/
def repIso (A : Rep ℤ G) : Rep.ofMulDistribMulAction G (Multiplicative ↥A.V) ≅ A :=
  Action.mkIso (repLinearEquiv A).toModuleIso fun g => by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl

/-- **The second cohomology of the action attached to a representation is the second cohomology of
the representation.** -/
def h2AddEquiv (A : Rep ℤ G) :
    ↥(H2 (Rep.ofMulDistribMulAction G (Multiplicative ↥A.V))) ≃+ ↥(H2 A) :=
  ((groupCohomology.functor ℤ G 2).mapIso (repIso A)).toLinearEquiv.toAddEquiv

/-! ### The action of a generator -/

section Generator

variable {A : Rep ℤ G} {g : G} {σ : ↥A.V ≃+ ↥A.V}

/-- A power of the automorphism by which a group element acts is the automorphism by which the
corresponding power of the group element acts. -/
theorem pow_apply_eq_rho_pow (hσ : ∀ x, σ x = A.ρ g x) (i : ℕ) (x : ↥A.V) :
    (σ ^ i) x = A.ρ (g ^ i) x := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ_apply, ih, hσ, pow_succ', map_mul, Module.End.mul_apply]

/-- A point fixed by an additive automorphism is fixed by all its powers. -/
theorem pow_apply_of_fixed {M : Type*} [AddCommGroup M] {τ : M ≃+ M} {x : M} (h : τ x = x) :
    ∀ i : ℕ, (τ ^ i) x = x
  | 0 => rfl
  | i + 1 => by rw [pow_succ_apply, pow_apply_of_fixed h i, h]

variable [Fintype G]

/-- **The invariants of a finite cyclic group are the fixed points of a generator.** -/
theorem mem_invariantsSubgroup_ofAdd_iff (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) (x : ↥A.V) :
    Multiplicative.ofAdd x ∈ invariantsSubgroup G (Multiplicative ↥A.V) ↔ σ x = x := by
  rw [mem_invariantsSubgroup]
  refine ⟨fun h => (hσ x).trans (h g), fun h s => ?_⟩
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff s g).1 (mem_powers_iff_mem_zpowers.2 (hg s))
  show Multiplicative.ofAdd (A.ρ (g ^ k) x) = Multiplicative.ofAdd x
  rw [← pow_apply_eq_rho_pow hσ, pow_apply_of_fixed h]

/-- **The norm of a finite cyclic group is the norm operator of a generator.** -/
theorem prod_smul_eq_ofAdd_normHom (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) (m : ↥A.V) :
    ∏ s : G, s • Multiplicative.ofAdd m
      = Multiplicative.ofAdd (normHom σ (Nat.card G) m) := by
  have h1 : ∏ s : G, s • Multiplicative.ofAdd m
      = Multiplicative.ofAdd (∑ s : G, A.ρ s m) := by
    rw [ofAdd_sum]
    rfl
  rw [h1, normHom_apply, ← sum_range_card_pow hg fun s : G => A.ρ s m]
  exact congrArg Multiplicative.ofAdd
    (Finset.sum_congr rfl fun i _ => (pow_apply_eq_rho_pow hσ i m).symm)

/-! ### The comparison map -/

/-- The fixed points of a generator, as the invariants of the whole group. -/
def kerEquivInvariants (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hσ : ∀ x, σ x = A.ρ g x) :
    ↥(sigmaSubOne σ).ker ≃+ Additive ↥(invariantsSubgroup G (Multiplicative ↥A.V)) where
  toFun x := Additive.ofMul ⟨Multiplicative.ofAdd (x : ↥A.V),
    (mem_invariantsSubgroup_ofAdd_iff hg hσ _).2 ((mem_ker_sigmaSubOne_iff σ _).1 x.2)⟩
  invFun y := ⟨Multiplicative.toAdd ((Additive.toMul y : ↥(invariantsSubgroup G
      (Multiplicative ↥A.V))) : Multiplicative ↥A.V),
    (mem_ker_sigmaSubOne_iff σ _).2
      ((mem_invariantsSubgroup_ofAdd_iff hg hσ _).1 (Additive.toMul y).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The map from the fixed points of a generator to the second cohomology of the group. -/
def tateH0ToH2 (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hσ : ∀ x, σ x = A.ρ g x) :
    ↥(sigmaSubOne σ).ker →+ ↥(H2 A) :=
  ((h2AddEquiv A).toAddMonoidHom.comp
      (MonoidHom.toAdditiveLeft (h2OfInvariant (M := Multiplicative ↥A.V) hg))).comp
    (kerEquivInvariants hg hσ).toAddMonoidHom

/-- **Every class in the second cohomology of a finite cyclic group is the class of a fixed point
of a generator.** -/
theorem tateH0ToH2_surjective (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) : Function.Surjective (tateH0ToH2 hg hσ) := by
  intro y
  obtain ⟨a, ha⟩ := h2OfInvariant_surjective (M := Multiplicative ↥A.V) hg
    (Multiplicative.ofAdd ((h2AddEquiv A).symm y))
  refine ⟨(kerEquivInvariants hg hσ).symm (Additive.ofMul a), ?_⟩
  simp only [tateH0ToH2, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, MonoidHom.coe_toAdditiveLeft]
  rw [show Multiplicative.toAdd (h2OfInvariant hg (Additive.toMul (Additive.ofMul a)))
      = (h2AddEquiv A).symm y from congrArg Multiplicative.toAdd ha]
  exact (h2AddEquiv A).apply_symm_apply y

/-- **The class of a fixed point of a generator vanishes exactly when the point is a norm.** -/
theorem tateH0ToH2_eq_zero_iff (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) (x : ↥(sigmaSubOne σ).ker) :
    tateH0ToH2 hg hσ x = 0 ↔ ∃ y, normHom σ (Nat.card G) y = (x : ↥A.V) := by
  have h2 : (tateH0ToH2 hg hσ x = 0) ↔
      Additive.toMul (kerEquivInvariants hg hσ x)
        ∈ (h2OfInvariant (M := Multiplicative ↥A.V) hg).ker := by
    rw [MonoidHom.mem_ker]
    exact (h2AddEquiv A).map_eq_zero_iff
  rw [h2, ker_h2OfInvariant hg, Subgroup.mem_subgroupOf, mem_normSubgroup]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨Multiplicative.toAdd m,
      (prod_smul_eq_ofAdd_normHom hg hσ (Multiplicative.toAdd m)).symm.trans hm⟩
  · rintro ⟨y, hy⟩
    exact ⟨Multiplicative.ofAdd y,
      (prod_smul_eq_ofAdd_normHom hg hσ y).trans (congrArg Multiplicative.ofAdd hy)⟩

/-- The kernel of the comparison map is the image of the norm operator. -/
theorem ker_tateH0ToH2 (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hσ : ∀ x, σ x = A.ρ g x) :
    (tateH0ToH2 hg hσ).ker
      = (normHom σ (Nat.card G)).range.addSubgroupOf (sigmaSubOne σ).ker := by
  ext x
  rw [AddMonoidHom.mem_ker, tateH0ToH2_eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact Iff.rfl

/-- **The Tate group of a generator is the second cohomology of a finite cyclic group.** -/
def tateH0AddEquivH2 (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (hσ : ∀ x, σ x = A.ρ g x) :
    tateH0 σ (Nat.card G) ≃+ ↥(H2 A) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_tateH0ToH2 hg hσ).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (tateH0ToH2_surjective hg hσ))

/-- **The second cohomology of a finite cyclic group has as many elements as the Tate group of a
generator.** -/
theorem card_H2_eq_card_tateH0 (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hσ : ∀ x, σ x = A.ρ g x) :
    Nat.card ↥(H2 A) = Nat.card (tateH0 σ (Nat.card G)) :=
  Nat.card_congr (tateH0AddEquivH2 hg hσ).toEquiv.symm

end Generator

end

end InverseGalois.CFT
