/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Coeff
import InverseGalois.CFT.Profinite.Res
import InverseGalois.Solvable.Shafarevich.GenericHomology

/-!
# The shrinking count, run on smooth cochains

The counting argument that annihilates cohomology classes with coefficients in a layer of a generic
operator group only ever looks at the values a cocycle takes: a class is the class of a cocycle, a
cocycle on a finite group takes finitely many values, and a map of the coefficients killing those
values kills the class.  Nothing in that reasoning refers to the way the cohomology is built, so it
applies verbatim to the cohomology written with cochains on a topological group, which is the
language in which the embedding problems of the solvable programme are posed.

Two things have to be said before the count can be run there.  A layer is written additively, as the
additive copy of a subgroup of a quotient of the group, whereas a coefficient module of a smooth
cochain is written multiplicatively; the same object serves both, and the map induced by a
homomorphism of groups is the same map read twice.  And the operator group acts on that subgroup by
automorphisms, so it is a multiplicative module in the required sense, and the map induced by a
homomorphism commuting with the operators is equivariant.

With those in place a family of subgroups of the operator group — the decomposition subgroups of a
finite family of places, in the application — can have finitely many of its second cohomology
classes killed at once by a single surjective shrinking homomorphism, provided the number of blocks
exceeds the number of scalar equations, which is the number of classes times the square of the order
of the subgroup times the dimension of the layer downstairs.

## Main definitions

* `InverseGalois.Shafarevich.genericLayerSubAction` — **the layers of a generic operator group are
  multiplicative modules over the operator group.**

## Main results

* `InverseGalois.Shafarevich.layerSubMap_smul` — the map of layers induced by a homomorphism
  commuting with the operators is equivariant.
* `InverseGalois.Shafarevich.exists_genericShrink_forall_layerSubMap_eq_one` — the count, on the
  multiplicative layer.
* `InverseGalois.Shafarevich.exists_genericShrink_forall_coeffH2_eq_one` — **finitely many classes
  of the second cohomology of a finite group acting through the operator group, written with smooth
  cochains with coefficients in a layer, are annihilated all at once by a surjective shrinking
  homomorphism.**
* `InverseGalois.Shafarevich.exists_operatorHom_forall_layerSubMap_eq_one` — **finitely many
  prescribed elements of a layer are trivialised at once by a surjective homomorphism onto the
  intended rank commuting with the operators**, the rank to start from being fixed by the number of
  elements alone.
* `InverseGalois.Shafarevich.exists_operatorHom_forall_coeffH2_eq_one` — **Proposition 6 in the
  smooth language**, for a subgroup of the operator group and with the rank chosen in advance of the
  classes.
* `InverseGalois.Shafarevich.exists_genericShrink_forall_subgroupCoeffH2_eq_one` and
  `InverseGalois.Shafarevich.exists_operatorHom_forall_subgroupCoeffH2_eq_one` — the same, for a
  **family** of subgroups of the operator group at once, one class on each.

## Tags

Shafarevich's theorem, embedding problem, group cohomology, smooth cochain, p-central series,
decomposition group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### The layer as a multiplicative module -/

section Mul

variable (U : Type) [Group U] [Finite U] (m : ℕ) (S : Type) [Group S] [Finite S] (ℓ j : ℕ)

/-- **The operator group acts by automorphisms on every layer of a generic operator group.**  A
layer is the additive copy of a subgroup of a quotient of the group, and the linear action on the
one is an action by group automorphisms on the other. -/
instance genericLayerSubAction : MulDistribMulAction U ↥(layerSub ℓ (Generic U m S) j) where
  smul u v := Additive.toMul (genericLayerRep U m S ℓ j u (Additive.ofMul v))
  one_smul v := by
    show Additive.toMul (genericLayerRep U m S ℓ j 1 (Additive.ofMul v)) = v
    rw [_root_.map_one]
    rfl
  mul_smul u u' v := by
    show Additive.toMul (genericLayerRep U m S ℓ j (u * u') (Additive.ofMul v)) = _
    rw [_root_.map_mul]
    rfl
  smul_mul u v w := congrArg Additive.toMul (map_add (genericLayerRep U m S ℓ j u) _ _)
  smul_one u := congrArg Additive.toMul (map_zero (genericLayerRep U m S ℓ j u))

omit [Finite U] [Finite S] in
/-- The action of the operator group on a layer, computed on an element. -/
theorem genericLayerSubAction_smul (u : U) (v : ↥(layerSub ℓ (Generic U m S) j)) :
    u • v = layerSubMap ℓ (genericAut U m S u).toMonoidHom j v := rfl

end Mul

/-! ### Equivariance -/

section Equivariance

variable {U : Type} [Group U] [Finite U] {m n : ℕ} {S : Type} [Group S] [Finite S] {ℓ j : ℕ}
  {α : Generic U m S →* Generic U n S}

omit [Finite U] [Finite S] in
/-- **The map of layers induced by a homomorphism commuting with the operators is equivariant.** -/
theorem layerSubMap_smul (hα : IsOperatorHom α) (u : U)
    (v : ↥(layerSub ℓ (Generic U m S) j)) :
    layerSubMap ℓ α j (u • v) = u • layerSubMap ℓ α j v :=
  layerMap_isOperatorHom hα u (Additive.ofMul v)

omit [Finite U] [Finite S] in
/-- The same equivariance, for a group acting on the two layers through the operator group. -/
theorem layerSubMap_smul_comm {H : Type*} [Group H] (f : H →* U)
    [MulDistribMulAction H ↥(layerSub ℓ (Generic U m S) j)]
    [MulDistribMulAction H ↥(layerSub ℓ (Generic U n S) j)]
    (h₁ : ∀ (h : H) (v : ↥(layerSub ℓ (Generic U m S) j)), h • v = f h • v)
    (h₂ : ∀ (h : H) (v : ↥(layerSub ℓ (Generic U n S) j)), h • v = f h • v)
    (hα : IsOperatorHom α) (h : H) (v : ↥(layerSub ℓ (Generic U m S) j)) :
    layerSubMap ℓ α j (h • v) = h • layerSubMap ℓ α j v := by
  rw [h₁, h₂]
  exact layerSubMap_smul hα (f h) v

omit [Finite U] [Finite S] in
/-- The same equivariance, seen from a subgroup of the operator group. -/
theorem layerSubMap_smul_subgroup (P : Subgroup U) (hα : IsOperatorHom α) (h : ↥P)
    (v : ↥(layerSub ℓ (Generic U m S) j)) :
    layerSubMap ℓ α j (h • v) = h • layerSubMap ℓ α j v :=
  layerSubMap_smul hα (h : U) v

end Equivariance

/-! ### The count on multiplicative layers -/

section Count

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and trivialising finitely many prescribed
elements of a layer at once**, the layer being read multiplicatively. -/
theorem exists_genericShrink_forall_layerSubMap_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} {ι : Type*} [Finite ι]
    (hr : (j + 1) * (Nat.card ι * Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (v : ι → ↥(layerSub ℓ (Generic U (r * n) S) j)) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, layerSubMap ℓ (genericShrink U r n S a) j (v ν) = 1 := by
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerMap_eq_zero U r n S hS hr
    fun ν => Additive.ofMul (v ν)
  exact ⟨a, hsurj, fun ν => ha ν⟩

omit [Group U] in
/-- **A shrinking homomorphism can be chosen surjective and trivialising finitely many prescribed
two cochains on a finite group at once.**  A two cochain on a finite group has at most the square of
its order many values, so that is the number of scalar equations per cochain. -/
theorem exists_genericShrink_forall_coeffMap₂_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t : ℕ} {H : Type*} [Group H] [Finite H]
    (hr : (j + 1) * (t * Nat.card H ^ 2 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (d : Fin t → H × H → ↥(layerSub ℓ (Generic U (r * n) S) j)) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, coeffMap₂ (layerSubMap ℓ (genericShrink U r n S a) j) (d ν) = 1 := by
  have hcard : Nat.card (Fin t × (H × H)) = t * Nat.card H ^ 2 := by
    simp [Nat.card_prod, pow_two]
  have hr' : (j + 1) * (Nat.card (Fin t × (H × H)) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by rwa [hcard]
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerSubMap_eq_one U r n S hS hr'
    fun q : Fin t × (H × H) => d q.1 q.2
  exact ⟨a, hsurj, fun ν => funext fun q => ha (ν, q)⟩

end Count

/-! ### The count in the smooth language -/

section Smooth

variable (U : Type) [Group U] [Finite U] (r n : ℕ) (S : Type) [Group S] [Finite S]

/-- **Finitely many classes of the second cohomology of a finite group acting through the operator
group, written with smooth cochains with coefficients in a layer, are annihilated all at once by a
surjective shrinking homomorphism.**  Each class is the class of a cocycle, and a map of the
coefficients trivialising all of its values carries it to the trivial cocycle, hence to the trivial
class. -/
theorem exists_genericShrink_forall_coeffH2_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t : ℕ} {H : Type*} [Group H] [TopologicalSpace H] [Finite H] (f : H →* U)
    [MulDistribMulAction H ↥(layerSub ℓ (Generic U (r * n) S) j)]
    [MulDistribMulAction H ↥(layerSub ℓ (Generic U n S) j)]
    (h₁ : ∀ (h : H) (v : ↥(layerSub ℓ (Generic U (r * n) S) j)), h • v = f h • v)
    (h₂ : ∀ (h : H) (v : ↥(layerSub ℓ (Generic U n S) j)), h • v = f h • v)
    (hr : (j + 1) * (t * Nat.card H ^ 2 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (x : Fin t → SmoothH2 H ↥(layerSub ℓ (Generic U (r * n) S) j)) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, coeffH2 (layerSubMap ℓ (genericShrink U r n S a) j)
        (layerSubMap_smul_comm f h₁ h₂ (isOperatorHom_genericShrink U r n S a)) (x ν) = 1 := by
  choose d hd hs hdx using fun ν => smoothH2Mk_surjective (x ν)
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_coeffMap₂_eq_one U r n S hS hr d
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hdx ν, coeffH2_smoothH2Mk]
  refine (smoothH2Mk_eq_one_iff _ _).2 ⟨1, isSmooth₁_one, ?_⟩
  rw [ha ν]
  exact coboundary₂_one

/-- **One class for each of finitely many subgroups of the operator group is annihilated all at once
by a surjective shrinking homomorphism.**  The number of scalar equations is the number of values
the cocycles take, which is the number of pairs of elements of each of the subgroups. -/
theorem exists_genericShrink_forall_subgroupCoeffH2_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hS : IsPGroup ℓ S) {j t : ℕ} [TopologicalSpace U] (P : Fin t → Subgroup U)
    (hr : (j + 1) * (Nat.card ((ν : Fin t) × (↥(P ν) × ↥(P ν))) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r)
    (x : ∀ ν, SmoothH2 ↥(P ν) ↥(layerSub ℓ (Generic U (r * n) S) j)) :
    ∃ a : Fin r → ℕ, Function.Surjective (genericShrink U r n S a) ∧
      ∀ ν, coeffH2 (layerSubMap ℓ (genericShrink U r n S a) j)
        (layerSubMap_smul_subgroup (P ν) (isOperatorHom_genericShrink U r n S a)) (x ν) = 1 := by
  choose d hd hs hdx using fun ν => smoothH2Mk_surjective (x ν)
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerSubMap_eq_one U r n S hS hr
    fun q : (ν : Fin t) × (↥(P ν) × ↥(P ν)) => d q.1 q.2
  refine ⟨a, hsurj, fun ν => ?_⟩
  rw [← hdx ν, coeffH2_smoothH2Mk]
  refine (smoothH2Mk_eq_one_iff _ _).2 ⟨1, isSmooth₁_one, ?_⟩
  have hν : coeffMap₂ (layerSubMap ℓ (genericShrink U r n S a) j) (d ν) = 1 :=
    funext fun q => ha ⟨ν, q⟩
  rw [hν]
  exact coboundary₂_one

end Smooth

/-! ### Proposition 6 in the smooth language -/

section Prop6

variable (U : Type) [Group U] [Finite U] [TopologicalSpace U] (n : ℕ) (S : Type) [Group S]
  [Finite S]

omit [TopologicalSpace U] in
/-- **Finitely many prescribed elements of a layer are trivialised at once by a surjective
homomorphism onto the intended rank commuting with the operators.**  How many letters one has to
start from is settled by how many elements there are, so it can be fixed before the elements
themselves are known. -/
theorem exists_operatorHom_forall_layerSubMap_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j : ℕ} (ι : Type*) [Finite ι] :
    ∃ m : ℕ, ∀ v : ι → ↥(layerSub ℓ (Generic U m S) j),
      ∃ (α : Generic U m S →* Generic U n S) (_ : IsOperatorHom α), Function.Surjective α ∧
        ∀ c, layerSubMap ℓ α j (v c) = 1 := by
  set r : ℕ := (j + 1) * (Nat.card ι *
    Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) + 1 with hrdef
  have hr : (j + 1) * (Nat.card ι *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by
    rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun v => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_layerSubMap_eq_one U r n S hS hr v
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

/-- **Proposition 6 in the smooth language.**  For a large enough rank, finitely many classes of the
second cohomology of a subgroup of the operator group, written with smooth cochains with
coefficients in a layer, are annihilated all at once by a surjective homomorphism onto the intended
rank commuting with the operators. -/
theorem exists_operatorHom_forall_coeffH2_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t : ℕ} (P : Subgroup U) :
    ∃ m : ℕ, ∀ x : Fin t → SmoothH2 ↥P ↥(layerSub ℓ (Generic U m S) j),
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, coeffH2 (layerSubMap ℓ α j) (layerSubMap_smul_subgroup P hα) (x ν) = 1 := by
  set r : ℕ := (j + 1) * (t * Nat.card ↥P ^ 2 *
    Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) + 1 with hrdef
  have hr : (j + 1) * (t * Nat.card ↥P ^ 2 *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by
    rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun x => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_coeffH2_eq_one U r n S hS P.subtype
    (fun _ _ => rfl) (fun _ _ => rfl) hr x
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

/-- **Proposition 6 in the smooth language, for a family of subgroups at once.**  For a large enough
rank, one class of the second cohomology of each of finitely many subgroups of the operator group,
with coefficients in a layer, is annihilated by a single surjective homomorphism onto the intended
rank commuting with the operators. -/
theorem exists_operatorHom_forall_subgroupCoeffH2_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hS : IsPGroup ℓ S)
    {j t : ℕ} (P : Fin t → Subgroup U) :
    ∃ m : ℕ, ∀ x : ∀ ν, SmoothH2 ↥(P ν) ↥(layerSub ℓ (Generic U m S) j),
      ∃ (α : Generic U m S →* Generic U n S) (hα : IsOperatorHom α), Function.Surjective α ∧
        ∀ ν, coeffH2 (layerSubMap ℓ α j) (layerSubMap_smul_subgroup (P ν) hα) (x ν) = 1 := by
  set r : ℕ := (j + 1) * (Nat.card ((ν : Fin t) × (↥(P ν) × ↥(P ν))) *
    Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) + 1 with hrdef
  have hr : (j + 1) * (Nat.card ((ν : Fin t) × (↥(P ν) × ↥(P ν))) *
      Module.finrank (ZMod ℓ) (Layer ℓ (Generic U n S) j)) < r := by
    rw [hrdef]; exact Nat.lt_succ_self _
  refine ⟨r * n, fun x => ?_⟩
  obtain ⟨a, hsurj, ha⟩ := exists_genericShrink_forall_subgroupCoeffH2_eq_one U r n S hS P hr x
  exact ⟨genericShrink U r n S a, isOperatorHom_genericShrink U r n S a, hsurj, ha⟩

end Prop6

end InverseGalois.Shafarevich
