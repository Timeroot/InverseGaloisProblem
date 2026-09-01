/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.GroupCohomology.CyclicTate
import InverseGalois.CFT.GroupCohomology.InflationRestriction

/-!
# Inflation and restriction in degree two

A representation of a group over the integers is the same thing as an action of the group by
multiplicative automorphisms of the multiplicative copy of the underlying abelian group, and the
cocycle and coboundary conditions in degree two match up under that dictionary.  So the analysis of
a two-cocycle whose restriction to a normal subgroup is a coboundary, carried out for an action by
multiplicative automorphisms, applies to a representation: the cocycle can be corrected inside its
class so that it depends only on the pair of cosets of the subgroup and takes values fixed by the
subgroup.  Such a cocycle descends to the quotient with values in the invariants, and inflating it
returns the class one started with.

That is the exactness of the inflation-restriction sequence at the middle term in degree two, and
the vanishing of the first cohomology of the subgroup is what makes it work.  Its use is a count: a
group whose kernel under one map lies in the image of another has at most as many elements as the
product of the source of the first and the target of the second, so a bound for the quotient and a
bound for the subgroup together bound the whole group.

## Main definitions

* `InverseGalois.CFT.descendCochain`: the cochain on the quotient attached to a two-cochain that
  depends only on the pair of cosets and takes values fixed by the subgroup.
* `InverseGalois.CFT.inflTwo`, `InverseGalois.CFT.resTwo`: inflation and restriction in degree two.

## Main results

* `InverseGalois.CFT.finite_and_card_le_of_ker_subset_range`: **a commutative group whose kernel
  under one map lies in the image of another is finite with at most as many elements as the
  product**, given that the source of the one and the target of the other are finite.
* `InverseGalois.CFT.mem_range_inflTwo_of_resTwo_eq_zero`: **the exactness of the
  inflation-restriction sequence in degree two.**
* `InverseGalois.CFT.finite_and_card_H2_le`: **the second cohomology of a group is finite with at
  most as many elements as the product of the second cohomology of the quotient by a normal
  subgroup and the second cohomology of the subgroup**, once the first cohomology of the subgroup
  vanishes.

## Tags

group cohomology, inflation, restriction, dévissage
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open CategoryTheory groupCohomology

noncomputable section

/-! ### A count from a kernel inside an image -/

/-- **A commutative group whose kernel under one map lies in the image of another is finite with at
most as many elements as the product**, provided the source of the one map and the target of the
other are finite: an element is determined by its image and by a preimage of its difference with a
chosen element of the same image. -/
theorem finite_and_card_le_of_ker_subset_range {X Y Z : Type*} [AddCommGroup X] [Finite Y]
    [AddCommGroup Z] [Finite Z] (i : Y → X) (f : X →+ Z)
    (h : ∀ x : X, f x = 0 → ∃ y : Y, i y = x) :
    Finite X ∧ Nat.card X ≤ Nat.card Y * Nat.card Z := by
  classical
  haveI : Nonempty X := ⟨0⟩
  have hsec : ∀ x : X, f (x - Function.invFun f (f x)) = 0 := by
    intro x
    rw [map_sub, sub_eq_zero]
    exact (Function.invFun_eq ⟨x, rfl⟩).symm
  set F : X → Y × Z := fun x => ((h _ (hsec x)).choose, f x) with hFdef
  have hinj : Function.Injective F := by
    intro x₁ x₂ hx
    have h2 : f x₁ = f x₂ := congrArg Prod.snd hx
    have h1 : (h _ (hsec x₁)).choose = (h _ (hsec x₂)).choose := congrArg Prod.fst hx
    have key : x₁ - Function.invFun f (f x₁) = x₂ - Function.invFun f (f x₂) := by
      rw [← (h _ (hsec x₁)).choose_spec, ← (h _ (hsec x₂)).choose_spec, h1]
    rw [h2] at key
    have := congrArg (fun t => t + Function.invFun f (f x₂)) key
    simpa using this
  haveI : Finite X := Finite.of_injective F hinj
  refine ⟨inferInstance, ?_⟩
  calc Nat.card X ≤ Nat.card (Y × Z) := Nat.card_le_card_of_injective F hinj
    _ = Nat.card Y * Nat.card Z := Nat.card_prod Y Z

variable {G : Type} [Group G]

attribute [local instance] repMulDistribMulAction

/-! ### The multiplicative dictionary in degree two -/

section Dictionary

variable {A : Rep ℤ G}

/-- A two-cocycle of a representation over the integers is a multiplicative two-cocycle of the
associated action by multiplicative automorphisms. -/
theorem isMulCocycle₂_ofAdd {f : G × G → ↥A.V} (hf : f ∈ cocycles₂ A) :
    IsMulCocycle₂ (M := Multiplicative ↥A.V) fun p => Multiplicative.ofAdd (f p) := by
  intro g h j
  show Multiplicative.ofAdd (f (g * h, j) + f (g, h))
    = Multiplicative.ofAdd (A.ρ g (f (h, j)) + f (g, h * j))
  exact congrArg Multiplicative.ofAdd ((mem_cocycles₂_iff f).1 hf g h j)

/-- A multiplicative two-cocycle of the action associated with a representation over the integers
is a two-cocycle of that representation. -/
theorem mem_cocycles₂_of_isMulCocycle₂ {f : G × G → ↥A.V}
    (hf : IsMulCocycle₂ (M := Multiplicative ↥A.V) fun p => Multiplicative.ofAdd (f p)) :
    f ∈ cocycles₂ A :=
  (mem_cocycles₂_iff f).2 fun g h j => congrArg Multiplicative.toAdd (hf g h j)

/-- A multiplicative two-coboundary of the action associated with a representation over the
integers is a two-coboundary of that representation. -/
theorem mem_coboundaries₂_of_isMulCoboundary₂ {f : G × G → ↥A.V}
    (hf : IsMulCoboundary₂ (M := Multiplicative ↥A.V) fun p => Multiplicative.ofAdd (f p)) :
    f ∈ coboundaries₂ A := by
  obtain ⟨u, hu⟩ := hf
  refine ⟨fun g => Multiplicative.toAdd (u g), funext fun p => ?_⟩
  rw [d₁₂_hom_apply]
  exact congrArg Multiplicative.toAdd (hu p.1 p.2)

end Dictionary

/-! ### Inflation and restriction -/

section InfRes

variable {A : Rep ℤ G} {S : Subgroup G} [S.Normal]

variable (A S) in
/-- Restriction of a second cohomology class to a subgroup. -/
abbrev resTwo : H2 A ⟶ H2 ((Action.res _ S.subtype).obj A) :=
  groupCohomology.map S.subtype (𝟙 _) 2

variable (A S) in
/-- Inflation of a second cohomology class of the quotient by a normal subgroup, with values in the
invariants, to the whole group. -/
abbrev inflTwo : H2 (A.quotientToInvariants S) ⟶ H2 A :=
  groupCohomology.map (QuotientGroup.mk' S)
    (Rep.subtype _ _ (Representation.le_comap_invariants A.ρ S)) 2

/-- The cochain on the quotient attached to a two-cochain which depends only on the pair of cosets
of a normal subgroup and takes values fixed by that subgroup. -/
def descendCochain (c : G × G → ↥A.V)
    (hfix : ∀ n ∈ S, ∀ x y : G, A.ρ n (c (x, y)) = c (x, y))
    (hcos : ∀ x y n : G, n ∈ S → ∀ m : G, m ∈ S → c (x * n, y * m) = c (x, y)) :
    (G ⧸ S) × (G ⧸ S) → ↥(Representation.invariants (A.ρ.comp S.subtype)) := fun p =>
  Quotient.liftOn₂' p.1 p.2 (fun x y => ⟨c (x, y), fun n => hfix n n.2 x y⟩)
    fun x y x' y' hx hy => Subtype.ext <| by
      have hx' : x' = x * (x⁻¹ * x') := by group
      have hy' : y' = y * (y⁻¹ * y') := by group
      show c (x, y) = c (x', y')
      conv_rhs => rw [hx', hy']
      exact (hcos x y _ (QuotientGroup.leftRel_apply.1 hx) _
        (QuotientGroup.leftRel_apply.1 hy)).symm

omit [S.Normal] in
@[simp]
theorem descendCochain_coe (c : G × G → ↥A.V) (hfix hcos) (x y : G) :
    ((descendCochain (S := S) c hfix hcos ((x : G ⧸ S), (y : G ⧸ S)) :
      ↥(Representation.invariants (A.ρ.comp S.subtype))) : ↥A.V) = c (x, y) :=
  rfl

@[simp]
theorem coe_quotientToInvariants_rho (x : G)
    (w : ↥(Representation.invariants (A.ρ.comp S.subtype))) :
    (((A.quotientToInvariants S).ρ (x : G ⧸ S) w :
      ↥(Representation.invariants (A.ρ.comp S.subtype))) : ↥A.V) = A.ρ x (w : ↥A.V) :=
  rfl

/-- Inflating a two-cocycle of the quotient with values in the invariants evaluates it at the pair
of cosets. -/
theorem coe_mapCocycles₂_inflation (z : cocycles₂ (A.quotientToInvariants S)) (p : G × G) :
    (⇑(mapCocycles₂ (QuotientGroup.mk' S)
        (Rep.subtype _ _ (Representation.le_comap_invariants A.ρ S)) z) : G × G → ↥A.V) p
      = ((z ((p.1 : G ⧸ S), (p.2 : G ⧸ S)) :
        ↥(Representation.invariants (A.ρ.comp S.subtype))) : ↥A.V) :=
  rfl

/-- **The exactness of the inflation-restriction sequence in degree two**: a second cohomology
class which dies on a normal subgroup is inflated from the quotient, as soon as the first
cohomology of the subgroup vanishes. -/
theorem mem_range_inflTwo_of_resTwo_eq_zero
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0)
    (y : ↥(H2 A)) (hy : resTwo A S y = 0) :
    ∃ z : ↥(H2 (A.quotientToInvariants S)), inflTwo A S z = y := by
  classical
  induction y using H2_induction_on with
  | @h x =>
  -- Restriction of the cocycle to the subgroup is a coboundary there.
  replace hy : H2π ((Action.res _ S.subtype).obj A) (mapCocycles₂ S.subtype (𝟙 _) x) = 0 := by
    rw [← H2π_comp_map_apply S.subtype]
    exact hy
  rw [H2π_eq_zero_iff] at hy
  obtain ⟨v, hv⟩ := hy
  -- Pass to the multiplicative language.
  have ha : IsMulCocycle₂ (M := Multiplicative ↥A.V) fun p => Multiplicative.ofAdd (x p) :=
    isMulCocycle₂_ofAdd x.2
  have hres : ∃ b : G → Multiplicative ↥A.V, ∀ g ∈ S, ∀ h ∈ S,
      (fun p : G × G => Multiplicative.ofAdd (x p)) (g, h) = g • b h / b (g * h) * b g := by
    refine ⟨fun g => if hg : g ∈ S then Multiplicative.ofAdd (v ⟨g, hg⟩) else 1, ?_⟩
    intro g hg h hh
    have hvp := congrFun hv (⟨g, hg⟩, ⟨h, hh⟩)
    rw [d₁₂_hom_apply] at hvp
    simp only [dif_pos hg, dif_pos hh, dif_pos (S.mul_mem hg hh)]
    exact (congrArg Multiplicative.ofAdd hvp).symm
  have hH1' : ∀ f : G → Multiplicative ↥A.V, (∀ g ∈ S, ∀ h ∈ S, f (g * h) = g • f h * f g) →
      ∃ t : Multiplicative ↥A.V, ∀ g ∈ S, g • t / t = f g := by
    intro f hf
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
  obtain ⟨u, hcos, hfix⟩ := exists_twist_inflated hH1' ha hres
  -- The corrected cocycle, back in additive language.
  set w : G → ↥A.V := fun g => Multiplicative.toAdd (u g) with hw
  set c : G × G → ↥A.V := fun p =>
    Multiplicative.toAdd (twist (fun p => Multiplicative.ofAdd (x p)) u p) with hc
  have hcc : c ∈ cocycles₂ A := mem_cocycles₂_of_isMulCocycle₂ (isMulCocycle₂_twist ha u)
  have hcfix : ∀ n ∈ S, ∀ g h : G, A.ρ n (c (g, h)) = c (g, h) := fun n hn g h =>
    congrArg Multiplicative.toAdd (hfix n hn g h)
  have hccos : ∀ g h n : G, n ∈ S → ∀ m : G, m ∈ S → c (g * n, h * m) = c (g, h) :=
    fun g h n hn m hm => congrArg Multiplicative.toAdd (hcos g h n hn m hm)
  -- It descends to a two-cocycle of the quotient with values in the invariants.
  have hdesc : descendCochain c hcfix hccos ∈ cocycles₂ (A.quotientToInvariants S) := by
    rw [mem_cocycles₂_iff]
    intro ga hb jc
    induction ga using QuotientGroup.induction_on with | @H g =>
    induction hb using QuotientGroup.induction_on with | @H h =>
    induction jc using QuotientGroup.induction_on with | @H j =>
    apply Subtype.ext
    simp only [Submodule.coe_add, ← QuotientGroup.mk_mul, descendCochain_coe]
    exact (mem_cocycles₂_iff c).1 hcc g h j
  -- Inflating it returns the class one started with.
  refine ⟨H2π _ ⟨descendCochain c hcfix hccos, hdesc⟩, ?_⟩
  simp only [inflTwo]
  rw [H2π_comp_map_apply (QuotientGroup.mk' S), H2π_eq_iff]
  have hkey : ∀ p : G × G,
      (x : G × G → ↥A.V) p = c p + (A.ρ p.1 (w p.2) - w (p.1 * p.2) + w p.1) := fun p =>
    congrArg Multiplicative.toAdd
      (eq_twist_mul_coboundary₂ (fun p => Multiplicative.ofAdd (x p)) u p)
  refine ⟨fun g => -w g, funext fun p => ?_⟩
  rw [d₁₂_hom_apply, Pi.sub_apply, coe_mapCocycles₂_inflation,
    cocycles₂.coe_mk (A := A.quotientToInvariants S), descendCochain_coe, hkey p, map_neg]
  abel

/-- **The second cohomology of a group is finite with at most as many elements as the product of
the second cohomology of the quotient by a normal subgroup and the second cohomology of the
subgroup**, once the first cohomology of the subgroup vanishes. -/
theorem finite_and_card_H2_le
    (hH1 : ∀ z : ↥(groupCohomology ((Action.res _ S.subtype).obj A) 1), z = 0)
    [Finite ↥(H2 (A.quotientToInvariants S))]
    [Finite ↥(H2 ((Action.res _ S.subtype).obj A))] :
    Finite ↥(H2 A) ∧ Nat.card ↥(H2 A)
      ≤ Nat.card ↥(H2 (A.quotientToInvariants S))
        * Nat.card ↥(H2 ((Action.res _ S.subtype).obj A)) :=
  finite_and_card_le_of_ker_subset_range (fun z => inflTwo A S z)
    (resTwo A S).hom.toAddMonoidHom fun y hy => mem_range_inflTwo_of_resTwo_eq_zero hH1 y hy

end InfRes

end

end InverseGalois.CFT
