/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.AffineTransport
import InverseGalois.Rigidity.RET.Inversion

/-!
# The branch-cycle correspondence over three points does not depend on the points

Translations, scalings and the inversion `T ↦ T⁻¹` generate the coordinate changes of the
projective line, and each of them carries covers of the line to covers of the line, branch points
to branch points and distinguished inertia generators to distinguished inertia generators.  A
statement about a branch locus that survives all three therefore depends on the locus only through
its orbit under coordinate changes.

For a *triple* of points that orbit is everything: three distinct points of the line can be moved
to any other three by a coordinate change.  Consequently the branch-cycle correspondence over three
branch points is a single statement, the same for every triple of distinct points — a triple of
points carries no invariant at all, once the point at infinity is allowed to move.

The argument is run once, for an abstract property `P` of triples closed under the three basic
coordinate changes, and then applied to the existence direction, to the completeness direction and
to the two together.  A triple `(t₀, t₁, t₂)` is first normalized affinely to `(0, 1, λ)`, and then
two normalized triples are joined by a single inversion: reading `(0, 1, λ)` in the coordinate
`(T - c)⁻¹` and renormalizing gives `(0, 1, λ(1-c)/(λ-c))`, and the value `λ(1-c)/(λ-c)` runs over
everything but `0` and `1` as `c` does.

## Main definitions

* `Rigidity.RET.IsTripleInvariant` — a property of triples closed under the coordinate changes of
  the projective line.

## Main results

* `Rigidity.RET.IsTripleInvariant.transport` — a triple-invariant property holds for one triple of
  distinct points if and only if it holds for every triple of distinct points.
* `Rigidity.RET.isMonodromyOver_transport` — a cover of the line branched over three points can be
  rebuilt, with the same monodromy, over any other three points.
* `Rigidity.RET.geomRETExistence_transport`, `Rigidity.RET.geomRETCompleteness_transport`,
  `Rigidity.RET.geomRET_transport` — the two directions of the branch-cycle correspondence over
  three points, and the two together, do not depend on the three points.
-/

noncomputable section

namespace Rigidity.RET

open GeomAKLB

/-- Every triple is the triple of its own values. -/
theorem eta_triple (t : Fin 3 → k) : t = ![t 0, t 1, t 2] := by
  funext i
  fin_cases i <;> rfl

/-- The affine invariant of an ordered triple of points of the line whose first two entries are
distinct: the value at which the affine coordinate change taking the first two entries to `0` and
`1` sends the third. -/
theorem affineInvariant_ne {u : Fin 3 → k} (hu : Function.Injective u) :
    u 0 ≠ u 1 ∧ (u 2 - u 0) / (u 1 - u 0) ≠ 0 ∧ (u 2 - u 0) / (u 1 - u 0) ≠ 1 := by
  have h01 : u 0 ≠ u 1 := fun hcontra => by simpa using hu hcontra
  have hden : u 1 - u 0 ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  have h02 : u 2 - u 0 ≠ 0 := sub_ne_zero_of_ne fun hcontra => by simpa using hu hcontra
  have h21 : u 2 - u 0 ≠ u 1 - u 0 := by
    intro hcontra
    have h2 : u 2 = u 1 := sub_left_inj.mp hcontra
    simpa using hu h2
  exact ⟨h01, div_ne_zero h02 hden, fun hcontra => h21 ((div_eq_one_iff_eq hden).mp hcontra)⟩

/-- A property of ordered triples of points of the line unchanged by the three basic coordinate
changes of the projective line: translating the parameter, scaling it, and inverting it.  Those
three generate all coordinate changes. -/
structure IsTripleInvariant (P : (Fin 3 → k) → Prop) : Prop where
  /-- the property survives a translation of the parameter. -/
  translate : ∀ {t : Fin 3 → k} (a : k), P t → P fun i => t i + a
  /-- the property survives a scaling of the parameter. -/
  scale : ∀ {t : Fin 3 → k} {c : k}, c ≠ 0 → P t → P fun i => c * t i
  /-- the property survives inverting the parameter, away from the origin. -/
  inv : ∀ {t : Fin 3 → k}, (∀ i, t i ≠ 0) → P t → P fun i => (t i)⁻¹

namespace IsTripleInvariant

variable {P : (Fin 3 → k) → Prop} (hP : IsTripleInvariant P)
include hP

/-- A triple-invariant property survives an affine coordinate change. -/
theorem affine {t : Fin 3 → k} {c : k} (hc : c ≠ 0) (a : k) (h : P t) :
    P fun i => c * t i + a :=
  hP.translate a (hP.scale hc h)

/-! ## Normalizing a triple -/

/-- **A triple of distinct points is affinely normalized to `(0, 1, λ)`**, where `λ` is its affine
invariant. -/
theorem normalize {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁) (h : P ![t₀, t₁, t₂]) :
    P ![0, 1, (t₂ - t₀) / (t₁ - t₀)] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  have hfun : (fun i => (t₁ - t₀)⁻¹ * (![t₀, t₁, t₂] : Fin 3 → k) i + -(t₀ / (t₁ - t₀)))
      = ![0, 1, (t₂ - t₀) / (t₁ - t₀)] := by
    funext i
    fin_cases i
    · show (t₁ - t₀)⁻¹ * t₀ + -(t₀ / (t₁ - t₀)) = 0
      ring
    · show (t₁ - t₀)⁻¹ * t₁ + -(t₀ / (t₁ - t₀)) = 1
      rw [inv_mul_eq_div, neg_div', ← add_div, ← sub_eq_add_neg, div_self hc]
    · show (t₁ - t₀)⁻¹ * t₂ + -(t₀ / (t₁ - t₀)) = (t₂ - t₀) / (t₁ - t₀)
      ring
  exact hfun ▸ hP.affine (inv_ne_zero hc) (-(t₀ / (t₁ - t₀))) h

/-- **The normalized triple `(0, 1, λ)` is carried back to the triple it came from.** -/
theorem denormalize {t₀ t₁ t₂ : k} (h01 : t₀ ≠ t₁)
    (h : P ![0, 1, (t₂ - t₀) / (t₁ - t₀)]) : P ![t₀, t₁, t₂] := by
  have hc : t₁ - t₀ ≠ 0 := sub_ne_zero_of_ne (Ne.symm h01)
  exact affine_normalized_triple hc ▸ hP.affine hc t₀ h

/-! ## Joining two normalized triples by an inversion -/

/-- **One inversion step between normalized triples.**  Reading the triple `(0, 1, λ)` in the
coordinate `(T - c)⁻¹` and renormalizing affinely gives the triple `(0, 1, λ(1-c)/(λ-c))`. -/
theorem inv_step {lam c : k} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcl : lam ≠ c)
    (h : P ![0, 1, lam]) : P ![0, 1, lam * (1 - c) / (lam - c)] := by
  have h1c : (1 : k) - c ≠ 0 := sub_ne_zero_of_ne (Ne.symm hc1)
  have hlc : lam - c ≠ 0 := sub_ne_zero_of_ne hcl
  -- move the triple by `-c`, so that it misses the origin
  have hshift : (fun i => (![0, 1, lam] : Fin 3 → k) i + -c) = ![-c, 1 - c, lam - c] := by
    funext i
    fin_cases i
    · show (0 : k) + -c = -c
      ring
    · show (1 : k) + -c = 1 - c
      ring
    · show lam + -c = lam - c
      ring
  have h1 : P ![-c, 1 - c, lam - c] := hshift ▸ hP.translate (-c) h
  have hne : ∀ i, (![-c, 1 - c, lam - c] : Fin 3 → k) i ≠ 0 := by
    intro i
    fin_cases i
    · exact neg_ne_zero.2 hc0
    · exact h1c
    · exact hlc
  -- invert the parameter
  have hinv : (fun i => ((![-c, 1 - c, lam - c] : Fin 3 → k) i)⁻¹)
      = ![(-c)⁻¹, (1 - c)⁻¹, (lam - c)⁻¹] := by
    funext i
    fin_cases i <;> rfl
  have h2 : P ![(-c)⁻¹, (1 - c)⁻¹, (lam - c)⁻¹] := hinv ▸ hP.inv hne h1
  -- renormalize
  have hcc : c * (1 - c) ≠ 0 := mul_ne_zero hc0 h1c
  have hfun : (fun i => c * (1 - c) * (![(-c)⁻¹, (1 - c)⁻¹, (lam - c)⁻¹] : Fin 3 → k) i + (1 - c))
      = ![0, 1, lam * (1 - c) / (lam - c)] := by
    funext i
    fin_cases i
    · show c * (1 - c) * (-c)⁻¹ + (1 - c) = 0
      have hfold : c * (1 - c) * (-c)⁻¹ = -(1 - c) := by
        rw [inv_neg, mul_neg, mul_comm c (1 - c), mul_assoc, mul_inv_cancel₀ hc0, mul_one]
      rw [hfold]
      ring
    · show c * (1 - c) * (1 - c)⁻¹ + (1 - c) = 1
      rw [mul_assoc, mul_inv_cancel₀ h1c, mul_one]
      ring
    · show c * (1 - c) * (lam - c)⁻¹ + (1 - c) = lam * (1 - c) / (lam - c)
      have hfold : c * (1 - c) * (lam - c)⁻¹ + (1 - c)
          = (c * (1 - c) + (1 - c) * (lam - c)) * (lam - c)⁻¹ := by
        rw [add_mul, mul_assoc ((1 : k) - c) (lam - c) ((lam - c)⁻¹), mul_inv_cancel₀ hlc, mul_one]
      rw [hfold, div_eq_mul_inv]
      congr 1
      ring
  exact hfun ▸ hP.affine hcc (1 - c) h2

/-- **Any two normalized triples are joined by a single inversion.** -/
theorem normalized {lam mu : k} (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1) (hmu0 : mu ≠ 0)
    (hmu1 : mu ≠ 1) (h : P ![0, 1, lam]) : P ![0, 1, mu] := by
  rcases eq_or_ne lam mu with rfl | hne
  · exact h
  have hd : lam - mu ≠ 0 := sub_ne_zero_of_ne hne
  have h1m : (1 : k) - mu ≠ 0 := sub_ne_zero_of_ne (Ne.symm hmu1)
  have hl1 : lam - 1 ≠ 0 := sub_ne_zero_of_ne hlam1
  obtain ⟨c, hcdef⟩ : ∃ c : k, c = lam * (1 - mu) / (lam - mu) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (mul_ne_zero hlam0 h1m) hd
  -- `1 - c = μ(λ-1)/(λ-μ)` and `λ - c = λ(λ-1)/(λ-μ)`, both non-zero
  have h1c : (1 : k) - c = mu * (lam - 1) / (lam - mu) := by
    rw [hcdef, eq_div_iff hd]
    field_simp
    ring
  have hlc : lam - c = lam * (lam - 1) / (lam - mu) := by
    rw [hcdef, eq_div_iff hd]
    field_simp
    ring
  have hc1 : c ≠ 1 := by
    intro hcontra
    refine div_ne_zero (mul_ne_zero hmu0 hl1) hd ?_
    rw [← h1c, hcontra]
    ring
  have hcl : lam ≠ c := by
    intro hcontra
    refine div_ne_zero (mul_ne_zero hlam0 hl1) hd ?_
    rw [← hlc, ← hcontra]
    ring
  have hstep := hP.inv_step hc0 hc1 hcl h
  have hden : lam * (lam - 1) / (lam - mu) ≠ 0 := div_ne_zero (mul_ne_zero hlam0 hl1) hd
  have hval : lam * (1 - c) / (lam - c) = mu := by
    rw [h1c, hlc, div_eq_iff hden]
    ring
  exact hval ▸ hstep

/-! ## The transport theorem -/

/-- **A triple-invariant property does not depend on the triple**: if it holds for one ordered
triple of distinct points of the line, it holds for every ordered triple of distinct points. -/
theorem transport {t s : Fin 3 → k} (ht : Function.Injective t) (hs : Function.Injective s)
    (h : P t) : P s := by
  obtain ⟨ht01, ht0, ht1⟩ := affineInvariant_ne ht
  obtain ⟨hs01, hs0, hs1⟩ := affineInvariant_ne hs
  have hstart : P ![t 0, t 1, t 2] := (eta_triple t) ▸ h
  have hnorm := hP.normalize ht01 hstart
  have hmove := hP.normalized ht0 ht1 hs0 hs1 hnorm
  exact (eta_triple s) ▸ hP.denormalize hs01 hmove

end IsTripleInvariant

/-! ## The instances -/

/-- **Being the monodromy of a cover branched over three points is a triple-invariant
property.** -/
theorem isTripleInvariant_isMonodromyOver {G : Type} [Group G] [Finite G] (h : Fin 3 → G) :
    IsTripleInvariant fun t : Fin 3 → k => IsMonodromyOver h t where
  translate a H := IsMonodromyOver.twist_translate a H
  scale hc H := IsMonodromyOver.twist_scale hc H
  inv ht H := IsMonodromyOver.twist_inv ht H

/-- **The existence direction of the branch-cycle correspondence is a triple-invariant
property.** -/
theorem isTripleInvariant_geomRETExistence :
    IsTripleInvariant fun t : Fin 3 → k => GeomRETExistence t where
  translate a h := GeomRETExistence.twist_translate a h
  scale hc h := GeomRETExistence.twist_scale hc h
  inv ht h := GeomRETExistence.twist_inv ht h

/-- **The completeness direction of the branch-cycle correspondence is a triple-invariant
property.** -/
theorem isTripleInvariant_geomRETCompleteness :
    IsTripleInvariant fun t : Fin 3 → k => GeomRETCompleteness t where
  translate a h := GeomRETCompleteness.twist_translate a h
  scale hc h := GeomRETCompleteness.twist_scale hc h
  inv ht h := GeomRETCompleteness.twist_inv ht h

/-- **The branch-cycle correspondence is a triple-invariant property.** -/
theorem isTripleInvariant_geomRET : IsTripleInvariant fun t : Fin 3 → k => GeomRET t where
  translate a h := GeomRET.twist_translate a h
  scale hc h := GeomRET.twist_scale hc h
  inv ht h := GeomRET.twist_inv ht h

/-- **A cover of the line branched over three points can be rebuilt, with the same monodromy, over
any other three points.** -/
theorem isMonodromyOver_transport {G : Type} [Group G] [Finite G] {h : Fin 3 → G}
    {t s : Fin 3 → k} (ht : Function.Injective t) (hs : Function.Injective s)
    (H : IsMonodromyOver h t) : IsMonodromyOver h s :=
  (isTripleInvariant_isMonodromyOver h).transport ht hs H

/-- **The existence direction of the branch-cycle correspondence over three branch points does not
depend on the branch points.** -/
theorem geomRETExistence_transport {t s : Fin 3 → k} (ht : Function.Injective t)
    (hs : Function.Injective s) (h : GeomRETExistence t) : GeomRETExistence s :=
  isTripleInvariant_geomRETExistence.transport ht hs h

/-- **The completeness direction of the branch-cycle correspondence over three branch points does
not depend on the branch points.** -/
theorem geomRETCompleteness_transport {t s : Fin 3 → k} (ht : Function.Injective t)
    (hs : Function.Injective s) (h : GeomRETCompleteness t) : GeomRETCompleteness s :=
  isTripleInvariant_geomRETCompleteness.transport ht hs h

/-- **The branch-cycle correspondence over three branch points does not depend on the branch
points**: three distinct points of the projective line carry no invariant, so the Riemann existence
theorem over three points is a single statement. -/
theorem geomRET_transport {t s : Fin 3 → k} (ht : Function.Injective t)
    (hs : Function.Injective s) (h : GeomRET t) : GeomRET s :=
  isTripleInvariant_geomRET.transport ht hs h

end Rigidity.RET
