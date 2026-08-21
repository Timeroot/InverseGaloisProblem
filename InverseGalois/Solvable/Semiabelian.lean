/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Solvable.Wreath
import InverseGalois.Rigidity.RET.RegularCriterion

/-!
# Semiabelian groups

Dentzer's class of **semiabelian** groups is the smallest class of finite groups that contains the
trivial group, is closed under forming a semidirect product `A ⋊[φ] H` with a finite abelian group
`A` and an arbitrary action `φ`, and is closed under homomorphic images.  It is exactly the class of
finite groups that the Ikeda / wreath-product approach to the inverse Galois problem reaches: one
climbs a chain of abelian extensions, and at each step the split extension `A ⋊[φ] H` is a quotient
of the single regular wreath product `A ≀ᵣ H`, whose realizability does not depend on `φ`.

The class sits between the finite abelian groups and the finite solvable groups.  It contains every
finite abelian group (take the trivial group for `H`), every dihedral group `DihedralGroup n` with
`n ≠ 0` (the rotation subgroup is cyclic and a reflection inverts it), and it is closed under
quotients and under multiplying by a finite abelian direct factor.  Every semiabelian group is
solvable, because `A ⋊[φ] H` is an extension of `H` by the abelian group `A`.

The payoff for the inverse Galois problem is recorded here in conditional form: from the single
input "the regular wreath product `A ≀ᵣ H` is realizable whenever `H` is and `A` is finite abelian"
one obtains a realization of *every* semiabelian group, over `ℚ` and — with the same argument, since
regular realizability over `ℚ(T)` obeys the same closure rules — regularly over `ℚ(T)`.

## Main results

* `IsSemiabelian` — the inductive predicate defining the class.
* `IsSemiabelian.of_subsingleton`, `IsSemiabelian.of_mulEquiv`, `IsSemiabelian.of_surjective`,
  `IsSemiabelian.quotient` — the basic closure properties.
* `IsSemiabelian.of_commGroup` — every finite abelian group is semiabelian.
* `IsSemiabelian.prod` — a finite abelian group times a semiabelian group is semiabelian.
* `IsSemiabelian.isSolvable` — every semiabelian group is solvable.
* `IsSemiabelian.dihedral` — every finite dihedral group is semiabelian.
* `IsSemiabelian.isInverseGalois`, `IsSemiabelian.isRegularInverseGalois` — from realizability of
  regular wreath products by finite abelian groups, every semiabelian group is realizable over `ℚ`,
  respectively regularly over `ℚ(T)`.
-/

/-- A semidirect product of two finite groups is finite: forgetting the twisted multiplication, it
is the product set. -/
instance SemidirectProduct.instFinite {N G : Type*} [Group N] [Group G] [Finite N] [Finite G]
    (φ : G →* MulAut N) : Finite (N ⋊[φ] G) :=
  Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm

/-- **Semiabelian groups**, Dentzer's class: the smallest class of finite groups containing the
trivial group, closed under semidirect products `A ⋊[φ] H` by a finite abelian group `A` acting
through an arbitrary `φ`, and closed under surjective homomorphic images. -/
inductive IsSemiabelian : ∀ (G : Type) [Group G] [Finite G], Prop
  /-- The trivial group is semiabelian. -/
  | of_subsingleton (G : Type) [Group G] [Finite G] [Subsingleton G] : IsSemiabelian G
  /-- A semidirect product of a semiabelian group by a finite abelian group, with an arbitrary
  action, is semiabelian. -/
  | semidirect {A H : Type} [CommGroup A] [Finite A] [Group H] [Finite H] (φ : H →* MulAut A)
      (h : IsSemiabelian H) : IsSemiabelian (A ⋊[φ] H)
  /-- A surjective homomorphic image of a semiabelian group is semiabelian. -/
  | of_surjective {G H : Type} [Group G] [Finite G] [Group H] [Finite H] (f : G →* H)
      (hf : Function.Surjective f) (h : IsSemiabelian G) : IsSemiabelian H

namespace IsSemiabelian

/-- Semiabelianness is invariant under group isomorphism. -/
theorem of_mulEquiv {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (hG : IsSemiabelian G) (e : G ≃* H) : IsSemiabelian H :=
  .of_surjective e.toMonoidHom e.surjective hG

/-- **Every finite abelian group is semiabelian**: it is the semidirect product of itself by the
trivial group, acting trivially. -/
theorem of_commGroup (A : Type) [CommGroup A] [Finite A] : IsSemiabelian A :=
  (IsSemiabelian.semidirect (1 : PUnit →* MulAut A) (.of_subsingleton PUnit)).of_mulEquiv
    (SemidirectProduct.mulEquivProd.trans MulEquiv.prodUnique)

/-- **A finite abelian group times a semiabelian group is semiabelian**: the direct product is the
semidirect product with the trivial action. -/
theorem prod {A H : Type} [CommGroup A] [Finite A] [Group H] [Finite H] (hH : IsSemiabelian H) :
    IsSemiabelian (A × H) :=
  (IsSemiabelian.semidirect (1 : H →* MulAut A) hH).of_mulEquiv SemidirectProduct.mulEquivProd

/-- **Semiabelian groups are closed under quotients by normal subgroups.** -/
theorem quotient {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) (N : Subgroup G)
    [N.Normal] : IsSemiabelian (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- **Every semiabelian group is solvable.**  The semidirect product `A ⋊[φ] H` is an extension of
`H` by the abelian group `A`: the kernel of the projection onto `H` is the image of `A`. -/
theorem isSolvable {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) : IsSolvable G := by
  induction hG with
  | of_subsingleton G =>
    letI : CommGroup G := { (inferInstance : Group G) with
      mul_comm := fun a b => Subsingleton.elim _ _ }
    exact CommGroup.isSolvable
  | semidirect φ _ ih =>
    letI := ih
    exact solvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  | of_surjective f hf _ ih =>
    letI := ih
    exact solvable_of_surjective hf

end IsSemiabelian

namespace Semiabelian

/-- The homomorphism out of the two-element group `Multiplicative (ZMod 2)` that sends the
generator to an element `k` whose square is the identity. -/
def ofSqEqOne {K : Type*} [Group K] (k : K) (hk : k * k = 1) : Multiplicative (ZMod 2) →* K where
  toFun ε := if Multiplicative.toAdd ε = 0 then 1 else k
  map_one' := by simp
  map_mul' a b := by
    have hab : Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b := rfl
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have hne : ¬ ((1 : ZMod 2) = 0) := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    show (if Multiplicative.toAdd (a * b) = 0 then (1 : K) else k) =
      (if Multiplicative.toAdd a = 0 then (1 : K) else k) *
        (if Multiplicative.toAdd b = 0 then (1 : K) else k)
    rcases h2 (Multiplicative.toAdd a) with ha | ha <;>
      rcases h2 (Multiplicative.toAdd b) with hb | hb <;>
        simp only [hab, ha, hb, zero_add, add_zero, h11, if_neg hne, if_true, one_mul, mul_one, hk]

@[simp]
theorem ofSqEqOne_zero {K : Type*} [Group K] (k : K) (hk : k * k = 1) :
    ofSqEqOne k hk (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := by
  show (if (0 : ZMod 2) = 0 then (1 : K) else k) = 1
  rw [if_pos rfl]

@[simp]
theorem ofSqEqOne_one {K : Type*} [Group K] (k : K) (hk : k * k = 1) :
    ofSqEqOne k hk (Multiplicative.ofAdd (1 : ZMod 2)) = k := by
  show (if (1 : ZMod 2) = 0 then (1 : K) else k) = k
  rw [if_neg (by decide : ¬ ((1 : ZMod 2) = 0))]

/-- The two-element group is exhausted by `0` and `1`. -/
theorem eq_zero_or_one (g : Multiplicative (ZMod 2)) :
    g = Multiplicative.ofAdd (0 : ZMod 2) ∨ g = Multiplicative.ofAdd (1 : ZMod 2) := by
  revert g
  decide

variable (n : ℕ)

/-- Inversion is an automorphism of the multiplicatively written cyclic group of order `n`, and it
is its own inverse. -/
theorem invAut_sq :
    (MulEquiv.inv (Multiplicative (ZMod n)) * MulEquiv.inv (Multiplicative (ZMod n)) :
      MulAut (Multiplicative (ZMod n))) = 1 := by
  ext x
  simp

/-- The action of the two-element group on the cyclic group of order `n` by inversion. -/
def dihedralAction : Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod n)) :=
  ofSqEqOne (MulEquiv.inv (Multiplicative (ZMod n))) (invAut_sq n)

@[simp]
theorem dihedralAction_zero :
    dihedralAction n (Multiplicative.ofAdd (0 : ZMod 2)) = 1 :=
  ofSqEqOne_zero _ _

@[simp]
theorem dihedralAction_one :
    dihedralAction n (Multiplicative.ofAdd (1 : ZMod 2)) = MulEquiv.inv (Multiplicative (ZMod n)) :=
  ofSqEqOne_one _ _

/-- The rotations, as a homomorphism from the cyclic group of order `n` into the dihedral group. -/
def rotationHom : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun a := DihedralGroup.r (Multiplicative.toAdd a)
  map_one' := rfl
  map_mul' _ _ := (DihedralGroup.r_mul_r _ _).symm

@[simp]
theorem rotationHom_apply (a : Multiplicative (ZMod n)) :
    rotationHom n a = DihedralGroup.r (Multiplicative.toAdd a) := rfl

/-- The reflections, as a homomorphism from the two-element group into the dihedral group. -/
def reflectionHom : Multiplicative (ZMod 2) →* DihedralGroup n :=
  ofSqEqOne (DihedralGroup.sr 0) (DihedralGroup.sr_mul_self 0)

@[simp]
theorem reflectionHom_zero : reflectionHom n (Multiplicative.ofAdd (0 : ZMod 2)) = 1 :=
  ofSqEqOne_zero _ _

@[simp]
theorem reflectionHom_one :
    reflectionHom n (Multiplicative.ofAdd (1 : ZMod 2)) = DihedralGroup.sr 0 :=
  ofSqEqOne_one _ _

/-- The dihedral group is generated by its rotation subgroup together with one reflection, which
conjugates every rotation to its inverse; this is the resulting homomorphism from the semidirect
product of the cyclic group of order `n` by the two-element group acting by inversion. -/
def dihedralHom :
    Multiplicative (ZMod n) ⋊[dihedralAction n] Multiplicative (ZMod 2) →* DihedralGroup n :=
  SemidirectProduct.lift (rotationHom n) (reflectionHom n) <| by
    intro g
    refine MonoidHom.ext fun a => ?_
    rcases eq_zero_or_one g with hg | hg <;> subst hg
    · show rotationHom n (dihedralAction n (Multiplicative.ofAdd (0 : ZMod 2)) a) =
        reflectionHom n (Multiplicative.ofAdd (0 : ZMod 2)) * rotationHom n a *
          (reflectionHom n (Multiplicative.ofAdd (0 : ZMod 2)))⁻¹
      simp
    · show rotationHom n (dihedralAction n (Multiplicative.ofAdd (1 : ZMod 2)) a) =
        reflectionHom n (Multiplicative.ofAdd (1 : ZMod 2)) * rotationHom n a *
          (reflectionHom n (Multiplicative.ofAdd (1 : ZMod 2)))⁻¹
      rw [dihedralAction_one, reflectionHom_one, DihedralGroup.inv_sr, rotationHom_apply,
        rotationHom_apply, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
      show DihedralGroup.r (-Multiplicative.toAdd a) = _
      rw [zero_add, zero_sub]

@[simp]
theorem dihedralHom_apply
    (x : Multiplicative (ZMod n) ⋊[dihedralAction n] Multiplicative (ZMod 2)) :
    dihedralHom n x = rotationHom n x.left * reflectionHom n x.right := rfl

/-- Every element of the dihedral group is a rotation, or a rotation times a fixed reflection. -/
theorem dihedralHom_surjective : Function.Surjective (dihedralHom n) := by
  intro x
  cases x with
  | r a =>
    refine ⟨⟨Multiplicative.ofAdd a, Multiplicative.ofAdd (0 : ZMod 2)⟩, ?_⟩
    simp
  | sr a =>
    refine ⟨⟨Multiplicative.ofAdd (-a), Multiplicative.ofAdd (1 : ZMod 2)⟩, ?_⟩
    rw [dihedralHom_apply, rotationHom_apply, reflectionHom_one]
    show DihedralGroup.r (-a) * DihedralGroup.sr 0 = DihedralGroup.sr a
    rw [DihedralGroup.r_mul_sr, zero_sub, neg_neg]

end Semiabelian

namespace IsSemiabelian

/-- **Every finite dihedral group is semiabelian**: it is a homomorphic image of the semidirect
product of the cyclic group of order `n` by the two-element group acting by inversion. -/
theorem dihedral (n : ℕ) [NeZero n] : IsSemiabelian (DihedralGroup n) :=
  (IsSemiabelian.semidirect (Semiabelian.dihedralAction n)
      (of_commGroup (Multiplicative (ZMod 2)))).of_surjective (Semiabelian.dihedralHom n)
    (Semiabelian.dihedralHom_surjective n)

/-- **Every semiabelian group is an inverse Galois group over `ℚ`**, given the hypothesis
`hwreath` that the regular wreath product `A ≀ᵣ H` is realizable over `ℚ` whenever `A` is a finite
abelian group and `H` is a realizable finite group.  Each semidirect step `A ⋊[φ] H` is a quotient
of `A ≀ᵣ H`, uniformly in the action `φ`, and realizability is closed under quotients. -/
theorem isInverseGalois
    (hwreath : ∀ (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H],
      IsInverseGalois H → IsInverseGalois (A ≀ᵣ H))
    {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) : IsInverseGalois G := by
  induction hG with
  | of_subsingleton G =>
    haveI : Unique G := uniqueOfSubsingleton 1
    exact IsInverseGalois.unit.of_mulEquiv MulEquiv.ofUnique
  | @semidirect A H _ _ _ _ φ _ ih =>
    exact IsInverseGalois.semidirectProduct_of_wreath φ (hwreath A H ih)
  | of_surjective f hf _ ih => exact ih.of_surjective f hf

/-- **Every semiabelian group is a regular inverse Galois group over `ℚ(T)`**, given the hypothesis
`hwreath` that the regular wreath product `A ≀ᵣ H` is regularly realizable whenever `A` is a finite
abelian group and `H` is a regularly realizable finite group.  Each semidirect step `A ⋊[φ] H` is a
quotient of `A ≀ᵣ H`, uniformly in the action `φ`, and regular realizability is closed under
quotients. -/
theorem isRegularInverseGalois
    (hwreath : ∀ (A H : Type) [CommGroup A] [Finite A] [Group H] [Finite H],
      IsRegularInverseGalois H → IsRegularInverseGalois (A ≀ᵣ H))
    {G : Type} [Group G] [Finite G] (hG : IsSemiabelian G) : IsRegularInverseGalois G := by
  induction hG with
  | of_subsingleton G => exact IsRegularInverseGalois.of_subsingleton
  | @semidirect A H _ _ _ _ φ _ ih =>
    exact IsRegularInverseGalois.semidirectProduct_of_wreath φ (hwreath A H ih)
  | of_surjective f hf _ ih => exact ih.of_surjective f hf

end IsSemiabelian
