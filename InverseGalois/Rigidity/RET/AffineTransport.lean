/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.GeomRET
import InverseGalois.Rigidity.RET.Scale
import InverseGalois.Rigidity.RET.SemiIsoInertia
import InverseGalois.Rigidity.RET.TranslateInfinity

/-!
# The branch-cycle correspondence depends only on the affine class of the branch points

Reading a cover of the line in an affine coordinate `T ↦ cT + a` changes neither its deck group nor
its behaviour at the point at infinity; it only moves the branch points by the affine map, and it
carries inertia generators to inertia generators.  Both directions of the branch-cycle
correspondence over a tuple of points therefore hold over the affine image of that tuple as soon as
they hold over the tuple itself.

For three points this says that the correspondence depends on the three points through a single
number, the cross-ratio-like invariant of the normalized triple `(0, 1, λ)`: an ordered triple of
distinct points of the line is carried to `(0, 1, λ)` by a unique affine map, and the two triples
carry the same covers.

## Main results

* `Rigidity.RET.GeomRET.twist_scale`, `Rigidity.RET.GeomRET.twist_translate` — the correspondence
  travels along a scaling and along a translation of the parameter.
* `Rigidity.RET.GeomRET.affine` — the correspondence travels along an affine coordinate change.
* `Rigidity.RET.geomRET_of_normalized` — the correspondence over an ordered triple of distinct
  points follows from the correspondence over the normalized triple `(0, 1, λ)`.

Each of these comes in several forms: for a single monodromy tuple (`IsMonodromyOver`), for the
existence direction (`GeomRETExistence`), for the completeness direction (`GeomRETCompleteness`),
and for the two together (`GeomRET`).  The tuple-level form is the finest, and is what lets a cover
built for one group over one branch locus be moved to any other branch locus of the same size.
-/

open Polynomial

noncomputable section


namespace Rigidity.RET

open GeomAKLB

/-! ## The branch locus of an affinely transformed tuple -/

theorem preimage_inv_smul_range {r : ℕ} (t : Fin r → k) {c : k} (hc : c ≠ 0) :
    ((fun s => c⁻¹ * s) ⁻¹' Set.range t) = Set.range fun i => c * t i := by
  ext s
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi, mul_inv_cancel_left₀ hc]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by rw [inv_mul_cancel_left₀ hc]⟩

theorem preimage_smul_range {r : ℕ} (t : Fin r → k) {c : k} (hc : c ≠ 0) :
    ((fun s => c * s) ⁻¹' Set.range fun i => c * t i) = Set.range t := by
  ext s
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, mul_left_cancel₀ hc hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

theorem preimage_sub_range {r : ℕ} (t : Fin r → k) (a : k) :
    ((fun s => s - a) ⁻¹' Set.range t) = Set.range fun i => t i + a := by
  ext s
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [hi]; ring⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by ring⟩

theorem preimage_add_range {r : ℕ} (t : Fin r → k) (a : k) :
    ((fun s => s - -a) ⁻¹' Set.range fun i => t i + a) = Set.range t := by
  ext s
  simp only [Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h : t i + a = s + a := by rw [hi]; ring
    exact add_right_cancel h
  · rintro ⟨i, rfl⟩
    exact ⟨i, by ring⟩

/-! ## Scaling the branch points -/

/-- **A monodromy tuple travels along a scaling of the parameter.** -/
theorem IsMonodromyOver.twist_scale {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} {c : k} (hc : c ≠ 0) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => c * t i := by
    obtain ⟨L, e, hout, hinf, hin⟩ := H
    refine ⟨L.twist (scaleSubst hc),
      ((L.twistSemiIso (scaleSubst hc)).symm.deckEquiv.symm).trans e, ?_, ?_, ?_⟩
    · rw [← preimage_inv_smul_range t hc]
      exact LineCover.IsUnramifiedOutside.twist_scale hc hout
    · exact LineCover.IsUnramifiedAtInfinity.twist_scale hc hinf
    · intro i
      exact LineCover.IsInertiaGenAt.semiIso (L.twistSemiIso (scaleSubst hc)).symm
        (scaleSubst_polyPreserving hc).symm (map_placeP_scale_symm hc (t i)) (hin i)

/-- **The existence direction travels along a scaling of the parameter.** -/
theorem GeomRETExistence.twist_scale {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0)
    (H : GeomRETExistence t) : GeomRETExistence fun i => c * t i :=
  fun _ _ _ h hprod htop => (H h hprod htop).twist_scale hc

/-- **The completeness direction travels along a scaling of the parameter.** -/
theorem GeomRETCompleteness.twist_scale {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0)
    (H : GeomRETCompleteness t) : GeomRETCompleteness fun i => c * t i := by
    intro L' hout hinf
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have hout' : (L'.twist (scaleSubst hc')).IsUnramifiedOutside (Set.range t) := by
      have h1 := LineCover.IsUnramifiedOutside.twist_scale hc' hout
      have hset : ((fun s => (c⁻¹)⁻¹ * s) ⁻¹' Set.range fun i => c * t i) = Set.range t := by
        rw [inv_inv]
        exact preimage_smul_range t hc
      rwa [hset] at h1
    have hinf' : (L'.twist (scaleSubst hc')).IsUnramifiedAtInfinity :=
      LineCover.IsUnramifiedAtInfinity.twist_scale hc' hinf
    obtain ⟨g, hg⟩ := H _ hout' hinf'
    have hmove : ∀ i, Ideal.map (scalePoly hc') (placeP (t i)) = placeP (c * t i) := by
      intro i
      rw [map_placeP_scale, inv_inv]
    exact ⟨fun i => (L'.twistSemiIso (scaleSubst hc')).conj (g i),
      LineCover.IsBranchCycleGenSystem.semiIso _ (scaleSubst_polyPreserving hc') hmove hg⟩

/-- **The branch-cycle correspondence travels along a scaling of the parameter.** -/
theorem GeomRET.twist_scale {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0) (H : GeomRET t) :
    GeomRET fun i => c * t i :=
  ⟨H.exists_cover.twist_scale hc, H.exists_cycles.twist_scale hc⟩

/-! ## Translating the branch points -/

/-- **A monodromy tuple travels along a translation of the parameter.** -/
theorem IsMonodromyOver.twist_translate {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} (a : k) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => t i + a := by
    obtain ⟨L, e, hout, hinf, hin⟩ := H
    refine ⟨L.twist (translateSubst a),
      ((L.twistSemiIso (translateSubst a)).symm.deckEquiv.symm).trans e, ?_, ?_, ?_⟩
    · rw [← preimage_sub_range t a]
      exact LineCover.IsUnramifiedOutside.twist_translate a hout
    · exact LineCover.IsUnramifiedAtInfinity.twist_translate a hinf
    · intro i
      exact LineCover.IsInertiaGenAt.semiIso (L.twistSemiIso (translateSubst a)).symm
        (translateSubst_polyPreserving a).symm (map_placeP_translate_symm a (t i)) (hin i)

/-- **The existence direction travels along a translation of the parameter.** -/
theorem GeomRETExistence.twist_translate {r : ℕ} {t : Fin r → k} (a : k)
    (H : GeomRETExistence t) : GeomRETExistence fun i => t i + a :=
  fun _ _ _ h hprod htop => (H h hprod htop).twist_translate a

/-- **The completeness direction travels along a translation of the parameter.** -/
theorem GeomRETCompleteness.twist_translate {r : ℕ} {t : Fin r → k} (a : k)
    (H : GeomRETCompleteness t) : GeomRETCompleteness fun i => t i + a := by
    intro L' hout hinf
    have hout' : (L'.twist (translateSubst (-a))).IsUnramifiedOutside (Set.range t) := by
      have h1 := LineCover.IsUnramifiedOutside.twist_translate (-a) hout
      rwa [preimage_add_range t a] at h1
    have hinf' : (L'.twist (translateSubst (-a))).IsUnramifiedAtInfinity :=
      LineCover.IsUnramifiedAtInfinity.twist_translate (-a) hinf
    obtain ⟨g, hg⟩ := H _ hout' hinf'
    have hmove : ∀ i, Ideal.map (translatePoly (-a)) (placeP (t i)) = placeP (t i + a) := by
      intro i
      rw [map_placeP_translate, sub_neg_eq_add]
    exact ⟨fun i => (L'.twistSemiIso (translateSubst (-a))).conj (g i),
      LineCover.IsBranchCycleGenSystem.semiIso _ (translateSubst_polyPreserving (-a)) hmove hg⟩

/-- **The branch-cycle correspondence travels along a translation of the parameter.** -/
theorem GeomRET.twist_translate {r : ℕ} {t : Fin r → k} (a : k) (H : GeomRET t) :
    GeomRET fun i => t i + a :=
  ⟨H.exists_cover.twist_translate a, H.exists_cycles.twist_translate a⟩

/-! ## Affine coordinate changes -/

/-- **A monodromy tuple travels along an affine coordinate change.** -/
theorem IsMonodromyOver.affine {G : Type} [Group G] [Finite G] {r : ℕ} {h : Fin r → G}
    {t : Fin r → k} {c : k} (hc : c ≠ 0) (a : k) (H : IsMonodromyOver h t) :
    IsMonodromyOver h fun i => c * t i + a :=
  (H.twist_scale hc).twist_translate a

/-- **The existence direction travels along an affine coordinate change.** -/
theorem GeomRETExistence.affine {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0) (a : k)
    (H : GeomRETExistence t) : GeomRETExistence fun i => c * t i + a :=
  fun _ _ _ h hprod htop => (H h hprod htop).affine hc a

/-- **The completeness direction travels along an affine coordinate change.** -/
theorem GeomRETCompleteness.affine {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0) (a : k)
    (H : GeomRETCompleteness t) : GeomRETCompleteness fun i => c * t i + a :=
  (H.twist_scale hc).twist_translate a

/-- **The branch-cycle correspondence travels along an affine coordinate change.** -/
theorem GeomRET.affine {r : ℕ} {t : Fin r → k} {c : k} (hc : c ≠ 0) (a : k) (H : GeomRET t) :
    GeomRET fun i => c * t i + a :=
  (H.twist_scale hc).twist_translate a

/-! ## Normalizing a triple of points -/

/-- The affine coordinate change carrying the normalized triple `(0, 1, λ)` to `(t₀, t₁, t₂)`,
where `λ` is the affine invariant `(t₂ - t₀) / (t₁ - t₀)` of the triple. -/
theorem affine_normalized_triple {t₀ t₁ t₂ : k} (hc : t₁ - t₀ ≠ 0) :
    (fun i => (t₁ - t₀) * (![0, 1, (t₂ - t₀) / (t₁ - t₀)] : Fin 3 → k) i + t₀)
      = ![t₀, t₁, t₂] := by
  funext i
  fin_cases i
  · show (t₁ - t₀) * 0 + t₀ = t₀
    ring
  · show (t₁ - t₀) * 1 + t₀ = t₁
    ring
  · show (t₁ - t₀) * ((t₂ - t₀) / (t₁ - t₀)) + t₀ = t₂
    field_simp
    ring

/-- **A monodromy tuple over an ordered triple of distinct points of the line is a monodromy tuple
over the normalized triple `(0, 1, λ)`.** -/
theorem isMonodromyOver_of_normalized {G : Type} [Group G] [Finite G] {h : Fin 3 → G}
    {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁)
    (H : IsMonodromyOver h ![0, 1, (t₂ - t₀) / (t₁ - t₀)]) : IsMonodromyOver h ![t₀, t₁, t₂] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  exact affine_normalized_triple hc ▸ H.affine hc t₀

/-- **The existence direction over an ordered triple of distinct points of the line is the
existence direction over the normalized triple `(0, 1, λ)`.** -/
theorem geomRETExistence_of_normalized {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁)
    (H : GeomRETExistence ![0, 1, (t₂ - t₀) / (t₁ - t₀)]) : GeomRETExistence ![t₀, t₁, t₂] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  exact affine_normalized_triple hc ▸ H.affine hc t₀

/-- **The completeness direction over an ordered triple of distinct points of the line is the
completeness direction over the normalized triple `(0, 1, λ)`.** -/
theorem geomRETCompleteness_of_normalized {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁)
    (H : GeomRETCompleteness ![0, 1, (t₂ - t₀) / (t₁ - t₀)]) :
    GeomRETCompleteness ![t₀, t₁, t₂] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  exact affine_normalized_triple hc ▸ H.affine hc t₀

/-- **The branch-cycle correspondence over an ordered triple of distinct points of the line is the
correspondence over the normalized triple `(0, 1, λ)`**, where `λ` is the affine invariant of the
triple: the unique affine coordinate change carrying `(0, 1, λ)` to the triple carries covers to
covers. -/
theorem geomRET_of_normalized {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁)
    (H : GeomRET ![0, 1, (t₂ - t₀) / (t₁ - t₀)]) : GeomRET ![t₀, t₁, t₂] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  exact affine_normalized_triple hc ▸ H.affine hc t₀

end Rigidity.RET
