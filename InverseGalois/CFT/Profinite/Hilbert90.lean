/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Profinite.Krull

/-!
# Hilbert's theorem ninety for an infinite Galois group

A smooth one cocycle of the Galois group of an arbitrary Galois extension, with values in the units
of the extension, is a coboundary.

The reduction to the finite case is the standard one.  A smooth cochain is constant on the cosets
of an open normal subgroup, and the subgroups fixing a finite Galois intermediate field are cofinal
among those, so the cocycle is constant on the cosets of the subgroup fixing such a field.  The
values of a smooth cocycle are fixed by that subgroup, hence lie in the field it fixes, which is
the finite Galois level itself.  Restriction to the level is surjective with that subgroup as
kernel, so choosing a preimage of each automorphism of the level produces a one cocycle of the
level with values in its units, and Noether's form of Hilbert's theorem ninety for a finite
extension supplies a primitive.  The primitive works upstairs unchanged, because every automorphism
of the extension acts on the level through its restriction.

## Main results

* `InverseGalois.CFT.isMulCoboundary₁_of_isMulCocycle₁_smooth`: **Hilbert's theorem ninety for an
  infinite Galois group** — a smooth one cocycle with values in the units of the extension is the
  coboundary of a single unit.
* `InverseGalois.CFT.subsingleton_smoothH1_units`: **the first cohomology of an infinite Galois
  group with values in the units of the extension is trivial.**

## Tags

infinite Galois theory, Krull topology, Galois cohomology, Hilbert's theorem 90, smooth cochain
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace InverseGalois.CFT

open groupCohomology

section Hilbert90

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]

/-- The values of a smooth one cocycle with values in the units of the extension lie in every
intermediate field whose fixing subgroup the cocycle is smooth for. -/
theorem mem_of_isMulCocycle₁_of_smooth {N : Subgroup Gal(K/k)} (hN : IsOpenNormal N)
    {u : Gal(K/k) → Kˣ} (hu : IsMulCocycle₁ u) (hcon : ∀ x : Gal(K/k), ∀ n ∈ N, u (x * n) = u x)
    (E : IntermediateField k K) (hle : E.fixingSubgroup ≤ N) (g : Gal(K/k)) : (u g : K) ∈ E := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := smul_eq_self_of_isMulCocycle₁_of_smooth hu hN.normal hcon (hle hσ) g
  simpa using congrArg (Units.val (α := K)) h

/-- **Hilbert's theorem ninety for an infinite Galois group**: a smooth one cocycle of the Galois
group of an arbitrary Galois extension, with values in the units of the extension, is the
coboundary of a single unit. -/
theorem isMulCoboundary₁_of_isMulCocycle₁_smooth {u : Gal(K/k) → Kˣ} (hu : IsMulCocycle₁ u)
    (hs : IsSmooth₁ u) : IsMulCoboundary₁ u := by
  obtain ⟨N, hN, hcon⟩ := hs
  obtain ⟨E, hfin, hgal, hle⟩ := exists_fixingSubgroup_le hN
  haveI := hfin
  haveI := hgal
  have hmem : ∀ g : Gal(K/k), (u g : K) ∈ E :=
    mem_of_isMulCocycle₁_of_smooth hN hu hcon E hle
  -- a cocycle constant on the cosets of the fixing subgroup only depends on the restriction
  have hres : ∀ g h : Gal(K/k), AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g
      = AlgEquiv.restrictNormalHom E h → u g = u h := by
    intro g h hgh
    have hker : g⁻¹ * h ∈ E.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker E, MonoidHom.mem_ker, map_mul, map_inv, hgh,
        inv_mul_cancel]
    have := hcon g (g⁻¹ * h) (hle hker)
    rwa [mul_inv_cancel_left, eq_comm] at this
  -- a section of the restriction to the finite Galois level
  choose lift hlift using restrictNormalHom_surjective_level (k := k) (K := K) E
  have hne : ∀ τ : E ≃ₐ[k] E, (⟨(u (lift τ) : K), hmem (lift τ)⟩ : ↥E) ≠ 0 := by
    intro τ hτ
    exact (u (lift τ)).ne_zero (congrArg Subtype.val hτ)
  set w : (E ≃ₐ[k] E) → (↥E)ˣ := fun τ => Units.mk0 _ (hne τ) with hw
  have hwval : ∀ τ : E ≃ₐ[k] E, ((w τ : ↥E) : K) = (u (lift τ) : K) := fun _ => rfl
  -- an automorphism of the extension acts on the level through its restriction
  have hsmul : ∀ (g : Gal(K/k)) (x : ↥E),
      ((AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g • x : ↥E) : K) = g (x : K) :=
    fun g x => AlgEquiv.restrictNormal_commutes g ↥E x
  have hKsmul : ∀ (g : Gal(K/k)) (x : Kˣ), ((g • x : Kˣ) : K) = g (x : K) := fun _ _ => rfl
  have hliftsmul : ∀ (τ : Gal(↥E/k)) (x : ↥E), ((τ • x : ↥E) : K) = (lift τ) ((x : K)) := by
    intro τ x
    have h := hsmul (lift τ) x
    rwa [hlift] at h
  have hwc : IsMulCocycle₁ w := by
    intro τ ρ
    refine Units.ext (Subtype.ext ?_)
    have hmulres : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (lift (τ * ρ))
        = AlgEquiv.restrictNormalHom E (lift τ * lift ρ) := by
      rw [hlift, map_mul, hlift, hlift]
    have hleft : ((w (τ * ρ) : ↥E) : K)
        = (lift τ) ((u (lift ρ) : K)) * (u (lift τ) : K) := by
      rw [hwval, hres _ _ hmulres, hu (lift τ) (lift ρ), Units.val_mul, hKsmul]
    have hright : (((τ • w ρ * w τ : (↥E)ˣ) : ↥E) : K)
        = (lift τ) ((u (lift ρ) : K)) * (u (lift τ) : K) := by
      show ((τ • (w ρ : ↥E) : ↥E) : K) * ((w τ : ↥E) : K) = _
      rw [hliftsmul, hwval, hwval]
    rw [hleft, hright]
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units w hwc
  -- the primitive of the level is a primitive upstairs
  set f : (↥E)ˣ →* Kˣ := Units.map (algebraMap ↥E K).toMonoidHom with hf
  have hfval : ∀ x : (↥E)ˣ, ((f x : K)) = ((x : ↥E) : K) := fun _ => rfl
  have hfw : ∀ τ : Gal(↥E/k), f (w τ) = u (lift τ) := fun τ => Units.ext (by rw [hfval, hwval])
  have hfsmul : ∀ (g : Gal(K/k)) (x : (↥E)ˣ),
      f (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g • x) = g • f x := fun g x =>
    Units.ext (by rw [hfval, hKsmul, hfval]; exact hsmul g (x : ↥E))
  refine ⟨f β, fun g => ?_⟩
  have hτ : AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E (lift
      (AlgEquiv.restrictNormalHom E g)) = AlgEquiv.restrictNormalHom E g := hlift _
  calc g • f β / f β
      = f (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g • β) / f β := by rw [hfsmul]
    _ = f (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g • β / β) := (map_div f _ _).symm
    _ = f (w (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) E g)) := by rw [hβ]
    _ = u g := (hfw _).trans (hres _ _ hτ)

/-- **The first cohomology of an infinite Galois group with values in the units of the extension is
trivial.** -/
theorem subsingleton_smoothH1_units : Subsingleton (SmoothH1 Gal(K/k) Kˣ) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨u, hu, hus, rfl⟩ := smoothH1Mk_surjective x
  obtain ⟨v, hv, hvs, rfl⟩ := smoothH1Mk_surjective y
  obtain ⟨a, ha⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth hu hus
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_smooth hv hvs
  rw [smoothH1Mk_eq_one_iff hu hus |>.2 ⟨a, funext ha⟩,
    smoothH1Mk_eq_one_iff hv hvs |>.2 ⟨b, funext hb⟩]

end Hilbert90

end InverseGalois.CFT
