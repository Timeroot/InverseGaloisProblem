/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.Shrink

/-!
# Pulling a family back along a power substitution of the parameter

Substituting `T = s + wᵉ` in a monic family of equations produces another monic family, of the same
degree, whose fibre over `w` is the fibre of the original family over `s + wᵉ`.  The substitution is
therefore a map of root varieties over the `e`-th power map of parameter planes, and the monodromy
of the pulled-back family is the monodromy of the original one along the pushed-forward loops.

This is the algebraic side of the local analysis of a family at a parameter where it degenerates:
the `e`-th power map wraps a small loop around `0` onto the `e`-th power of a small loop around `s`,
so pulling back is what kills the local monodromy.

## Main definitions

* `Rigidity.RET.Analytic.substHom` — the substitution `T ↦ s + Tᵉ` of the parameter.
* `Rigidity.RET.Analytic.pullFam` — the family pulled back along it.
* `Rigidity.RET.Analytic.pullBase`, `Rigidity.RET.Analytic.pullTotal` — the substitution as a map of
  punctured planes and as a map of root covers over it.
* `Rigidity.RET.Analytic.pullFibre` — the induced bijection of fibres.

## Main results

* `Rigidity.RET.Analytic.spec_pullFam` — the fibre equation of the pulled-back family.
* `Rigidity.RET.Analytic.monodromyHom_comp_map_pullBase` — the monodromy of the pulled-back family
  is the monodromy of the original family along the pushed-forward loops.
* `Rigidity.RET.Analytic.range_monodromyHom_pullFam_le` — the monodromy group of the pulled-back
  family sits inside the monodromy group of the original one.
-/

open Polynomial Rigidity.RET

noncomputable section

namespace Rigidity.RET.Analytic

/-! ### The substitution -/

/-- The substitution `T ↦ s + Tᵉ` of the parameter of a family. -/
def substHom (s : ℂ) (e : ℕ) : Polynomial ℂ →+* Polynomial ℂ :=
  eval₂RingHom C (C s + X ^ e)

@[simp] theorem substHom_C (s : ℂ) (e : ℕ) (a : ℂ) : substHom s e (C a) = C a := by
  simp [substHom]

@[simp] theorem substHom_X (s : ℂ) (e : ℕ) : substHom s e X = C s + X ^ e := by
  simp [substHom]

theorem evalRingHom_comp_substHom (s : ℂ) (e : ℕ) (w : ℂ) :
    (evalRingHom w).comp (substHom s e) = evalRingHom (s + w ^ e) := by
  refine ringHom_ext (fun a => ?_) ?_ <;> simp

/-- **The family pulled back along the substitution `T = s + wᵉ`.** -/
def pullFam (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) : Polynomial (Polynomial ℂ) :=
  P.map (substHom s e)

variable {P : Polynomial (Polynomial ℂ)} {S S' : Finset ℂ} {s : ℂ} {e : ℕ}

theorem monic_pullFam (hP : P.Monic) (s : ℂ) (e : ℕ) : (pullFam P s e).Monic := hP.map _

theorem natDegree_pullFam (hP : P.Monic) (s : ℂ) (e : ℕ) :
    (pullFam P s e).natDegree = P.natDegree := hP.natDegree_map _

/-- **The equation of the fibre of the pulled-back family** over `w` is the equation of the fibre of
the original family over `s + wᵉ`. -/
theorem spec_pullFam (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) (w : ℂ) :
    spec (pullFam P s e) w = spec P (s + w ^ e) := by
  show (P.map (substHom s e)).map (evalRingHom w) = P.map (evalRingHom (s + w ^ e))
  rw [Polynomial.map_map, evalRingHom_comp_substHom]

/-- **The pulled-back family degenerates exactly over the degeneration locus of the original
one.** -/
theorem degenLocus_pullFam (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) :
    degenLocus (pullFam P s e) = (fun w => s + w ^ e) ⁻¹' degenLocus P := by
  ext w
  simp only [degenLocus, Set.mem_setOf_eq, Set.mem_preimage, spec_pullFam]

/-- The parameters left separable by the pulled-back family. -/
theorem separable_spec_pullFam (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) :
    ∀ w ∉ (S' : Set ℂ), (spec (pullFam P s e) w).Separable := by
  intro w hw
  rw [spec_pullFam]
  exact hS _ (hbase w hw)

/-! ### The substitution as a map of root covers -/

theorem mem_rootVariety_pull {q : ℂ × ℂ} (hq : q ∈ rootVariety (pullFam P s e)) :
    (s + q.1 ^ e, q.2) ∈ rootVariety P := by
  have h : (spec (pullFam P s e) q.1).eval q.2 = 0 := hq
  rwa [spec_pullFam] at h

/-- The parameter substitution as a map of punctured planes. -/
def pullBase (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) :
    C(↥((S' : Set ℂ)ᶜ), ↥((S : Set ℂ)ᶜ)) :=
  ⟨fun w => ⟨s + (w : ℂ) ^ e, hbase w w.2⟩,
    (continuous_const.add (continuous_subtype_val.pow e)).subtype_mk _⟩

/-- The parameter substitution lifted to the root covers. -/
def pullTotal (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) :
    C(↥(rootProj (pullFam P s e) ⁻¹' ((S' : Set ℂ)ᶜ)), ↥(rootProj P ⁻¹' ((S : Set ℂ)ᶜ))) where
  toFun q :=
    ⟨⟨(s + ((q.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 ^ e,
        ((q.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).2), mem_rootVariety_pull q.1.2⟩,
      hbase _ q.2⟩
  continuous_toFun := by
    have hv : Continuous fun q : ↥(rootProj (pullFam P s e) ⁻¹' ((S' : Set ℂ)ᶜ)) =>
        ((q.1 : rootVariety (pullFam P s e)) : ℂ × ℂ) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (((continuous_const.add (hv.fst.pow e)).prodMk hv.snd).subtype_mk _).subtype_mk _

theorem puncturedProj_pullTotal (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ))
    (q : ↥(rootProj (pullFam P s e) ⁻¹' ((S' : Set ℂ)ᶜ))) :
    puncturedProj P S (pullTotal P s e hbase q)
      = pullBase s e hbase (puncturedProj (pullFam P s e) S' q) :=
  Subtype.ext rfl

/-! ### The induced bijection of fibres -/

/-- The map of fibres induced by the parameter substitution. -/
def pullFibreFun (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ (S' : Set ℂ)) :
    (puncturedProj (pullFam P s e) S' ⁻¹' {(⟨w₀, hw₀⟩ : ↥((S' : Set ℂ)ᶜ))}) →
      (puncturedProj P S ⁻¹' {(⟨s + w₀ ^ e, hbase w₀ hw₀⟩ : ↥((S : Set ℂ)ᶜ))}) := fun q =>
  ⟨pullTotal P s e hbase q.1, by
    have hq : ((q.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 = w₀ :=
      congrArg Subtype.val q.2
    refine Subtype.ext ?_
    show s + ((q.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 ^ e = s + w₀ ^ e
    rw [hq]⟩

theorem bijective_pullFibreFun (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ (S' : Set ℂ)) : Function.Bijective (pullFibreFun P s e hbase hw₀) := by
  constructor
  · intro q₁ q₂ h
    have h₁ : ((q₁.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 = w₀ :=
      congrArg Subtype.val q₁.2
    have h₂ : ((q₂.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 = w₀ :=
      congrArg Subtype.val q₂.2
    have hval : (s + ((q₁.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 ^ e,
          ((q₁.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).2)
        = (s + ((q₂.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).1 ^ e,
          ((q₂.1.1 : rootVariety (pullFam P s e)) : ℂ × ℂ).2) :=
      congrArg Subtype.val (congrArg Subtype.val (congrArg Subtype.val h))
    refine Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext ?_ ?_)))
    · rw [h₁, h₂]
    · have hsnd := congrArg Prod.snd hval
      exact hsnd
  · intro r
    have hr : ((r.1.1 : rootVariety P) : ℂ × ℂ).1 = s + w₀ ^ e := congrArg Subtype.val r.2
    have hroot : (spec (pullFam P s e) w₀).eval ((r.1.1 : rootVariety P) : ℂ × ℂ).2 = 0 := by
      rw [spec_pullFam]
      have h := r.1.1.2
      rw [mem_rootVariety, hr] at h
      exact h
    refine ⟨⟨⟨⟨(w₀, ((r.1.1 : rootVariety P) : ℂ × ℂ).2), hroot⟩, hw₀⟩, Subtype.ext rfl⟩, ?_⟩
    refine Subtype.ext (Subtype.ext (Subtype.ext (Prod.ext ?_ rfl)))
    exact hr.symm

/-- **The fibres of the pulled-back family are the fibres of the original one.** -/
def pullFibre (P : Polynomial (Polynomial ℂ)) (s : ℂ) (e : ℕ) {S S' : Finset ℂ}
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ (S' : Set ℂ)) :
    (puncturedProj (pullFam P s e) S' ⁻¹' {(⟨w₀, hw₀⟩ : ↥((S' : Set ℂ)ᶜ))}) ≃
      (puncturedProj P S ⁻¹' {(⟨s + w₀ ^ e, hbase w₀ hw₀⟩ : ↥((S : Set ℂ)ᶜ))}) :=
  Equiv.ofBijective _ (bijective_pullFibreFun P s e hbase hw₀)

/-! ### Monodromy of the pulled-back family -/

/-- **The monodromy of the pulled-back family is the monodromy of the original family along the
pushed-forward loops.**  Acting by a loop of the punctured plane of the parameter `w` on the fibre
of the pulled-back family is acting by its image under the substitution on the fibre of the
original family. -/
theorem monodromyHom_comp_map_pullBase (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ (S' : Set ℂ)) :
    (monodromyHom hP hS (hbase w₀ hw₀)).comp
        (FundamentalGroup.map (pullBase s e hbase) (⟨w₀, hw₀⟩ : ↥((S' : Set ℂ)ᶜ)))
      = (Equiv.permCongrHom (pullFibre P s e hbase hw₀)).toMonoidHom.comp
        (monodromyHom (monic_pullFam hP s e) (separable_spec_pullFam hS hbase) hw₀) := by
  refine MonoidHom.ext fun γ => Equiv.ext fun r => ?_
  obtain ⟨d, rfl⟩ := (pullFibre P s e hbase hw₀).surjective r
  show monodromyHom hP hS (hbase w₀ hw₀)
      (FundamentalGroup.map (pullBase s e hbase) _ γ) (pullFibre P s e hbase hw₀ d)
    = Equiv.permCongrHom (pullFibre P s e hbase hw₀)
      (monodromyHom (monic_pullFam hP s e) (separable_spec_pullFam hS hbase) hw₀ γ)
      (pullFibre P s e hbase hw₀ d)
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  refine Subtype.ext ?_
  exact monodromyHom_naturality
    (isCoveringMap_puncturedProj (monic_pullFam hP s e) (separable_spec_pullFam hS hbase))
    (isCoveringMap_puncturedProj hP hS) (pullBase s e hbase) (pullTotal P s e hbase)
    (puncturedProj_pullTotal P s e hbase) γ d _

/-- **The monodromy group of the pulled-back family sits inside the monodromy group of the original
family**, once the fibres are identified. -/
theorem range_monodromyHom_pullFam_le (hP : P.Monic)
    (hS : ∀ z ∉ (S : Set ℂ), (spec P z).Separable)
    (hbase : ∀ w : ℂ, w ∉ (S' : Set ℂ) → s + w ^ e ∉ (S : Set ℂ)) {w₀ : ℂ}
    (hw₀ : w₀ ∉ (S' : Set ℂ)) :
    (monodromyHom (monic_pullFam hP s e) (separable_spec_pullFam hS hbase) hw₀).range.map
        (Equiv.permCongrHom (pullFibre P s e hbase hw₀)).toMonoidHom
      ≤ (monodromyHom hP hS (hbase w₀ hw₀)).range := by
  rintro x ⟨y, ⟨γ, rfl⟩, rfl⟩
  exact ⟨FundamentalGroup.map (pullBase s e hbase) (⟨w₀, hw₀⟩ : ↥((S' : Set ℂ)ᶜ)) γ,
    congrFun (congrArg DFunLike.coe (monodromyHom_comp_map_pullBase hP hS hbase hw₀)) γ⟩

end Rigidity.RET.Analytic

end
