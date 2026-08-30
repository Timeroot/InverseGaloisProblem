/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.InfResTwo

/-!
# Inflation in degree two is injective

A second cohomology class of the quotient of a group by a normal subgroup, with values in the
invariants of a representation, is determined by the class it inflates to, as soon as the first
cohomology of the subgroup vanishes.

The cocycle inflated from the quotient depends only on the pair of cosets, so a cochain
trivialising it can be corrected, without changing its differential, to be constant on cosets and
to take values fixed by the subgroup; that correction is exactly where the vanishing of the first
cohomology is spent.  Such a cochain is the pullback of a cochain on the quotient with values in
the invariants, and the differential of the latter is the cocycle one started with.

Together with the exactness of the inflation-restriction sequence this pins down the second
cohomology of the quotient inside that of the whole group: an inflated class has the same order as
the class it comes from.

## Main definitions

* `InverseGalois.CFT.descendCochain₁`: the one-cochain on the quotient attached to a one-cochain
  which is constant on the cosets of a normal subgroup and takes values fixed by it.

## Main results

* `InverseGalois.CFT.eq_zero_of_inflTwo_eq_zero`: **inflation in degree two is injective** once the
  first cohomology of the subgroup vanishes.
* `InverseGalois.CFT.inflTwo_injective`: the same, phrased as injectivity.
* `InverseGalois.CFT.dvd_of_zsmul_inflTwo_eq_zero`: an inflated class has the same annihilator as
  the class it is inflated from.

## Tags

group cohomology, inflation, restriction, two cocycle, injective
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology

noncomputable section

variable {G : Type} [Group G]

attribute [local instance] repMulDistribMulAction

section InfRes

variable {A : Rep ℤ G} {S : Subgroup G} [S.Normal]

/-! ### Descending a one-cochain -/

/-- The one-cochain on the quotient attached to a one-cochain which is constant on the cosets of a
normal subgroup and takes values fixed by that subgroup. -/
def descendCochain₁ (u : G → ↥A.V) (hfix : ∀ n ∈ S, ∀ x : G, A.ρ n (u x) = u x)
    (hcos : ∀ x n : G, n ∈ S → u (x * n) = u x) :
    G ⧸ S → ↥(Representation.invariants (A.ρ.comp S.subtype)) := fun p =>
  Quotient.liftOn' p (fun x => ⟨u x, fun n => hfix n n.2 x⟩) fun x x' hx => Subtype.ext <| by
    have hx' : x' = x * (x⁻¹ * x') := by group
    show u x = u x'
    conv_rhs => rw [hx']
    exact (hcos x _ (QuotientGroup.leftRel_apply.1 hx)).symm

omit [S.Normal] in
@[simp]
theorem descendCochain₁_coe (u : G → ↥A.V) (hfix hcos) (x : G) :
    ((descendCochain₁ (S := S) u hfix hcos (x : G ⧸ S) :
      ↥(Representation.invariants (A.ρ.comp S.subtype))) : ↥A.V) = u x :=
  rfl

/-! ### The vanishing of the first cohomology, multiplicatively -/

omit [S.Normal] in
/-- The vanishing of the first cohomology of a subgroup, read through the dictionary between a
representation over the integers and an action by multiplicative automorphisms: a map which is a
one-cocycle on the subgroup is there the coboundary of a single element. -/
theorem exists_smul_div_eq_of_forall_eq_zero_H1
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0)
    (f : G → Multiplicative ↥A.V) (hf : ∀ g ∈ S, ∀ h ∈ S, f (g * h) = g • f h * f g) :
    ∃ t : Multiplicative ↥A.V, ∀ g ∈ S, g • t / t = f g := by
  have hmem : (fun s : S => Multiplicative.toAdd (f ↑s)) ∈
      cocycles₁ ((Action.res _ S.subtype).obj A) := by
    rw [mem_cocycles₁_iff]
    intro s t
    exact congrArg Multiplicative.toAdd (hf ↑s s.2 ↑t t.2)
  have hzero := hH1 (H1π _ ⟨_, hmem⟩)
  rw [H1π_eq_zero_iff] at hzero
  obtain ⟨t, ht⟩ := hzero
  refine ⟨Multiplicative.ofAdd t, fun g hg => ?_⟩
  have h1 := congrFun ht ⟨g, hg⟩
  rw [d₀₁_hom_apply] at h1
  exact congrArg Multiplicative.ofAdd h1

/-! ### Injectivity of inflation -/

/-- **Inflation in degree two is injective** once the first cohomology of the normal subgroup
vanishes: a cochain trivialising an inflated cocycle can be taken inflated itself, and it then
descends to the quotient. -/
theorem eq_zero_of_inflTwo_eq_zero
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0)
    (z : ↥(H2 (A.quotientToInvariants S))) (hz : inflTwo A S z = 0) : z = 0 := by
  classical
  induction z using H2_induction_on with
  | @h ζ =>
  simp only [inflTwo] at hz
  rw [H2π_comp_map_apply (QuotientGroup.mk' S), H2π_eq_zero_iff] at hz
  obtain ⟨v, hv⟩ := hz
  -- The inflated cocycle, in multiplicative language, together with its two properties.
  set a : G × G → Multiplicative ↥A.V :=
    fun p => Multiplicative.ofAdd ((d₁₂ A).hom v p) with hadef
  have hcob : IsMulCoboundary₂ a := by
    rw [isMulCoboundary₂_iff]
    refine ⟨fun g => Multiplicative.ofAdd (v g), funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    rw [coboundary₂_apply, smul_ofAdd, ← ofAdd_sub, ← ofAdd_add]
    simp only [hadef, d₁₂_hom_apply]
  have hinfl : ∀ (x y n : G), n ∈ S → ∀ m : G, m ∈ S → a (x * n, y * m) = a (x, y) := by
    intro x y n hn m hm
    have h1 := (congrFun hv (x * n, y * m)).trans (coe_mapCocycles₂_inflation ζ (x * n, y * m))
    have h2 := (congrFun hv (x, y)).trans (coe_mapCocycles₂_inflation ζ (x, y))
    rw [hadef]
    refine congrArg Multiplicative.ofAdd ?_
    rw [h1, h2, QuotientGroup.mk_mul_of_mem _ hn, QuotientGroup.mk_mul_of_mem _ hm]
  obtain ⟨u, hcoset, hfix, hcb⟩ :=
    exists_coboundary₂_inflated (exists_smul_div_eq_of_forall_eq_zero_H1 hH1) hinfl hcob
  -- The trivialising cochain, back in additive language, descends to the quotient.
  set w : G → ↥A.V := fun g => Multiplicative.toAdd (u g) with hw
  have hwfix : ∀ n ∈ S, ∀ x : G, A.ρ n (w x) = w x := fun n hn x =>
    congrArg Multiplicative.toAdd (hfix x n hn)
  have hwcos : ∀ x n : G, n ∈ S → w (x * n) = w x := fun x n hn =>
    congrArg Multiplicative.toAdd (hcoset x n hn)
  rw [H2π_eq_zero_iff]
  refine ⟨descendCochain₁ w hwfix hwcos, funext fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  induction x using QuotientGroup.induction_on with | @H g =>
  induction y using QuotientGroup.induction_on with | @H h =>
  apply Subtype.ext
  have hkey := congrFun hcb (g, h)
  rw [coboundary₂_apply, hadef] at hkey
  have hkey' : A.ρ g (w h) - w (g * h) + w g = (d₁₂ A).hom v (g, h) :=
    congrArg Multiplicative.toAdd hkey
  have hcoe : (((d₁₂ (A.quotientToInvariants S)).hom (descendCochain₁ w hwfix hwcos)
      ((g : G ⧸ S), (h : G ⧸ S)) : ↥(Representation.invariants (A.ρ.comp S.subtype))) : ↥A.V)
      = A.ρ g (w h) - w (g * h) + w g := rfl
  rw [hcoe, hkey', congrFun hv (g, h), coe_mapCocycles₂_inflation ζ (g, h)]

/-- **Inflation in degree two is injective** once the first cohomology of the normal subgroup
vanishes. -/
theorem inflTwo_injective
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0) :
    Function.Injective fun z : ↥(H2 (A.quotientToInvariants S)) => inflTwo A S z := by
  intro z₁ z₂ h
  have hsub : inflTwo A S (z₁ - z₂) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 h
  exact sub_eq_zero.1 (eq_zero_of_inflTwo_eq_zero hH1 _ hsub)

/-- **An inflated second cohomology class has the same annihilator as the class it is inflated
from**, once the first cohomology of the normal subgroup vanishes. -/
theorem zsmul_eq_zero_of_zsmul_inflTwo_eq_zero
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0)
    (z : ↥(H2 (A.quotientToInvariants S))) {m : ℤ} (hm : m • inflTwo A S z = 0) : m • z = 0 := by
  refine eq_zero_of_inflTwo_eq_zero hH1 _ ?_
  rw [map_zsmul]
  exact hm

end InfRes

end

end InverseGalois.CFT
