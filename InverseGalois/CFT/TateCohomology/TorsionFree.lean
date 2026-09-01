/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.TateCohomology.Additive
import InverseGalois.CFT.TateCohomology.Annihilate
import InverseGalois.CFT.TateCohomology.PTorsionTrivial

/-!
# A representation without torsion at a prime

Multiplication by a natural number is a map of a representation to itself, and its cokernel is the
representation modulo that multiple.  When the number is a prime `p` acting without torsion the
resulting sequence is short exact, so the complete cohomology of the representation and of its
reduction are tied together by a long exact sequence.

The reduction is killed by `p`, so for a `p`-group it has no complete cohomology at all as soon as
it has none in a single degree, and a single degree is supplied by two consecutive degrees of the
representation itself.  Feeding that back into the long exact sequence, multiplication by `p` is
injective on the complete cohomology of the representation in every degree; since the order of the
group already annihilates it and that order is a power of `p`, the complete cohomology vanishes
everywhere.

## Main definitions

* `InverseGalois.CFT.Tate.nsmulHom`: multiplication by a natural number, as a map of
  representations.
* `InverseGalois.CFT.Tate.modNsmul`: a representation modulo the multiples of a natural number.

## Main results

* `InverseGalois.CFT.Tate.nsmulSeq_shortExact`: **a representation without torsion at `p` sits in a
  short exact sequence with its reduction modulo `p`.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_injective_nsmul`: **a representation of a `p`-group
  over the integers on whose complete cohomology multiplication by `p` is injective has none in any
  degree.**
* `InverseGalois.CFT.Tate.isZero_tateModule_of_isZero_two_int`: **a representation of a `p`-group
  over the integers without torsion at `p` whose complete cohomology vanishes in two consecutive
  degrees has none in any degree.**

## Tags

Tate cohomology, cohomologically trivial, p-group, torsion free
-/

namespace InverseGalois.CFT.Tate

open CategoryTheory Representation

universe u

noncomputable section

/-! ### Two consequences of the long exact sequence -/

section Exactness

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

theorem eq_zero_of_isZero {M : ModuleCat.{u} k} (h : Limits.IsZero M) (x : M) : x = 0 := by
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact Subsingleton.elim x 0

theorem isZero_of_forall_eq_zero {M : ModuleCat.{u} k} (h : ∀ x : M, x = 0) : Limits.IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun a b => by rw [h a, h b]⟩

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℤ)

include hX

/-- **The quotient has nothing in a degree in which the middle term has nothing and the sub has
nothing one degree higher.** -/
theorem isZero_tateModule_X₃ (h2 : Limits.IsZero (tateModule X.X₂ n))
    (h1 : Limits.IsZero (tateModule X.X₁ (n + 1))) : Limits.IsZero (tateModule X.X₃ n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨y, hy⟩ := (tateExact_map_δ hX n x).1 (eq_zero_of_isZero h1 _)
  rw [← hy, eq_zero_of_isZero h2 y, map_zero]

/-- **The map from the sub is injective one degree above a degree in which the quotient has
nothing.** -/
theorem injective_tateMap_f (h : Limits.IsZero (tateModule X.X₃ n)) :
    Function.Injective (tateMap X.f (n + 1)) := by
  intro a b hab
  obtain ⟨x, hx⟩ := (tateExact_δ_map hX n (a - b)).1 (by rw [map_sub, hab, sub_self])
  have hzero : (tateδ hX n) x = 0 := by
    rw [h.eq_zero_of_src (tateδ hX n)]
    simp
  rw [hzero] at hx
  exact sub_eq_zero.1 hx.symm

end Exactness

/-! ### Multiplication by a natural number -/

section Nsmul

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

variable (k) in
/-- **Multiplication by a natural number**, as a linear map. -/
def nsmulLinear (m : ℕ) (V : Type*) [AddCommGroup V] [Module k V] : V →ₗ[k] V where
  toFun v := m • v
  map_add' a b := smul_add m a b
  map_smul' c v := smul_comm m c v

@[simp]
theorem nsmulLinear_apply (m : ℕ) {V : Type*} [AddCommGroup V] [Module k V] (v : V) :
    nsmulLinear k m V v = m • v := rfl

variable (A : Rep k G) (m : ℕ)

omit [Finite G] in
/-- The multiples of `m` form a stable submodule. -/
theorem range_nsmulLinear_le_comap (g : G) :
    LinearMap.range (nsmulLinear k m ↥A.V)
      ≤ (LinearMap.range (nsmulLinear k m ↥A.V)).comap (A.ρ g) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨A.ρ g v, by simp⟩

/-- **A representation modulo the multiples of a natural number.** -/
def modNsmul : Rep k G :=
  Rep.of (A.ρ.quotient (LinearMap.range (nsmulLinear k m ↥A.V)) (range_nsmulLinear_le_comap A m))

/-- **Multiplication by a natural number**, as a map of representations. -/
def nsmulHom : A ⟶ A :=
  mkHom (nsmulLinear k m ↥A.V) fun g => by ext v; simp

omit [Finite G] in
@[simp]
theorem nsmulHom_hom_apply (v : ↥A.V) : (nsmulHom A m).hom v = m • v := rfl

omit [Finite G] in
theorem nsmulHom_eq_nsmul_id : nsmulHom A m = m • 𝟙 A := by
  ext v
  simp

/-- **A multiple of a class of the complete cohomology is the class of that multiple.** -/
theorem tateMap_nsmulHom_apply (n : ℤ) (x : tateModule A n) :
    (tateMap (nsmulHom A m) n) x = m • x := by
  rw [nsmulHom_eq_nsmul_id]
  simpa using tateMap_nsmul_id_apply A m n x

omit [Finite G] in
/-- **Every vector of the reduction is killed by the number one reduces by.** -/
theorem nsmul_modNsmul_eq_zero (v : ↥(modNsmul A m).V) : m • v = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (nsmulLinear k m ↥A.V)) v
  have h : (LinearMap.range (nsmulLinear k m ↥A.V)).mkQ (m • f) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨f, rfl⟩
  rwa [map_nsmul] at h

/-- **The short exact sequence of a representation, its multiple and its reduction.** -/
def nsmulSeq : ShortComplex (Rep k G) where
  X₁ := A
  X₂ := A
  X₃ := modNsmul A m
  f := nsmulHom A m
  g := mkHom (LinearMap.range (nsmulLinear k m ↥A.V)).mkQ fun _ => by ext v; rfl
  zero := by
    ext v
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨v, rfl⟩

omit [Finite G] in
/-- **The sequence is short exact when the number acts without torsion.** -/
theorem nsmulSeq_shortExact (hm : ∀ v : ↥A.V, m • v = 0 → v = 0) : (nsmulSeq A m).ShortExact :=
  shortExact_of_linearMap
    (fun v w h => by
      refine sub_eq_zero.1 (hm _ ?_)
      rw [smul_sub]
      exact sub_eq_zero.2 h)
    (Submodule.mkQ_surjective _) fun _ hx => (Submodule.Quotient.mk_eq_zero _).1 hx

end Nsmul

/-! ### Vanishing in two consecutive degrees -/

section Int

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Fact p.Prime] in
/-- **A class killed by a power of a number on which that number acts injectively vanishes.** -/
theorem eq_zero_of_pow_nsmul_eq_zero {M : Type*} [AddCommGroup M]
    (hinj : ∀ y : M, p • y = 0 → y = 0) (a : ℕ) (x : M) (hx : p ^ a • x = 0) : x = 0 := by
  induction a generalizing x with
  | zero => simpa using hx
  | succ a ih =>
    refine hinj x (ih (p • x) ?_)
    rw [smul_smul, ← pow_succ]
    exact hx

/-- **A representation of a `p`-group over the integers on whose complete cohomology multiplication
by `p` is injective has no complete cohomology in any degree.** -/
theorem isZero_tateModule_of_injective_nsmul (hG : IsPGroup p G) (A : Rep ℤ G)
    (hinj : ∀ m : ℤ, Function.Injective (tateMap (nsmulHom A p) (m + 1))) (n : ℤ) :
    Limits.IsZero (tateModule A n) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p) (G := G)).1 hG
  have step : ∀ m : ℤ, Limits.IsZero (tateModule A (m + 1)) := by
    intro m
    refine isZero_of_forall_eq_zero fun x => ?_
    refine eq_zero_of_pow_nsmul_eq_zero (p := p) (fun y hy => hinj m ?_) a x ?_
    · rw [map_zero, tateMap_nsmulHom_apply A p (m + 1) y]
      exact hy
    · rw [← ha]
      exact card_nsmul_eq_zero_tateModule A (m + 1) x
  exact isZero_tateModule_congr (by omega) (step (n - 1))

/-- **A representation of a `p`-group over the integers without torsion at `p` whose complete
cohomology vanishes in two consecutive degrees has none in any degree.** -/
theorem isZero_tateModule_of_isZero_two_int (hG : IsPGroup p G) (A : Rep ℤ G)
    (htf : ∀ v : ↥A.V, p • v = 0 → v = 0) {i : ℤ} (hi : Limits.IsZero (tateModule A i))
    (hi1 : Limits.IsZero (tateModule A (i + 1))) (n : ℤ) : Limits.IsZero (tateModule A n) := by
  have hX : (nsmulSeq A p).ShortExact := nsmulSeq_shortExact A p htf
  have hq : ∀ j : ℤ, Limits.IsZero (tateModule (modNsmul A p) j) :=
    isZero_tateModule_of_isZero_single_int hG _ (nsmul_modNsmul_eq_zero A p)
      (isZero_tateModule_X₃ hX i hi hi1)
  exact isZero_tateModule_of_injective_nsmul hG A (fun m => injective_tateMap_f hX m (hq m)) n

end Int

end

end InverseGalois.CFT.Tate
