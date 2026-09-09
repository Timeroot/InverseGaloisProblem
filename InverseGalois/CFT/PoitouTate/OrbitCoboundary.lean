/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# A cocycle on a permutation module is a coboundary as soon as it is one at every point

A finite group acting on a set acts on the finitely supported functions from that set to a module,
moving the point and the value at once.  A one-cocycle with values in those functions is a family
of one-cocycles, one for each point, each defined only on the subgroup fixing that point.  **If
every one of those is a coboundary, so is the whole cocycle.**

The proof is the usual transport along a section of the orbit map.  Choose for every point a
representative of its orbit and an element of the group carrying the representative to the point.
At the representative the cocycle is, by hypothesis, the coboundary of a single value of the
module; carrying that value along the chosen element and correcting by the value of the cocycle at
the chosen element gives a function on the whole set which does not depend on the choice, because
two choices differ by an element fixing the representative and the correction absorbs exactly that
difference.  That function is finitely supported: the cocycle takes only finitely many values, each
finitely supported, so away from a finite set of points the hypothesis is met by the zero value of
the module, and the orbit of a finite set under a finite group is finite.  A short computation with
the cocycle identity then shows the cocycle is its coboundary.

This is the local-to-global step for a module of the shape "one copy of a module for every place",
where the group of the extension permutes the places: a class which is trivial over every
decomposition group is trivial.  It is Shapiro's lemma in the one degree where it can be written
out by hand, and it is written out by hand here so that the identification of the places with the
orbit does not have to be made functorial.

## Main definitions

* `InverseGalois.CFT.permFinsuppMap`: the action of a group element on the finitely supported
  functions on a set it acts on, moving the point and the value at once.
* `InverseGalois.CFT.permFinsuppRep`: **the resulting representation.**
* `InverseGalois.CFT.orbitRep` and `InverseGalois.CFT.orbitLift`: the chosen representative of the
  orbit of a point, and an element of the group carrying it to that point.

## Main results

* `InverseGalois.CFT.exists_finsupp_eq_sub_of_forall_stabilizer`: **a cocycle with values in the
  finitely supported functions which is a coboundary at every point, on the subgroup fixing that
  point, is a coboundary.**
* `InverseGalois.CFT.H1π_permFinsuppRep_eq_zero`: the same, read as the vanishing of the class in
  the first cohomology of the representation.

## Tags

group cohomology, permutation module, Shapiro, orbit, coboundary
-/

namespace InverseGalois.CFT

open MulAction groupCohomology

/-! ### The permutation module -/

section Rep

variable (Q : Type) [Group Q] (X : Type) [MulAction Q X] (W : Type) [AddCommGroup W]
  [DistribMulAction Q W]

/-- **The action of a group element on the finitely supported functions on a set it acts on**,
moving the point and the value at once. -/
noncomputable def permFinsuppMap (σ : Q) : (X →₀ W) →+ (X →₀ W) :=
  (Finsupp.domCongr (toPerm σ) : (X →₀ W) ≃+ (X →₀ W)).toAddMonoidHom.comp
    (Finsupp.mapRange.addMonoidHom (DistribSMul.toAddMonoidHom W σ))

@[simp]
theorem permFinsuppMap_apply (σ : Q) (b : X →₀ W) (x : X) :
    permFinsuppMap Q X W σ b x = σ • b (σ⁻¹ • x) := rfl

/-- The diagonal action, as a representation over the integers. -/
noncomputable def permFinsuppRepρ : Representation ℤ Q (X →₀ W) where
  toFun σ := (permFinsuppMap Q X W σ).toIntLinearMap
  map_one' := by
    refine LinearMap.ext fun b => Finsupp.ext fun x => ?_
    show ((1 : Q) • b ((1 : Q)⁻¹ • x) : W) = b x
    rw [inv_one, one_smul, one_smul]
  map_mul' σ τ := by
    refine LinearMap.ext fun b => Finsupp.ext fun x => ?_
    show ((σ * τ) • b ((σ * τ)⁻¹ • x) : W) = σ • (τ • b (τ⁻¹ • σ⁻¹ • x))
    rw [mul_inv_rev, mul_smul, mul_smul]

/-- **The permutation module**: the finitely supported functions on a set the group acts on, with
the point and the value moving at once. -/
noncomputable def permFinsuppRep : Rep ℤ Q := Rep.of (permFinsuppRepρ Q X W)

theorem permFinsuppRep_ρ_eq (σ : Q) (b : X →₀ W) :
    (permFinsuppRep Q X W).ρ σ b = permFinsuppMap Q X W σ b := rfl

end Rep

/-! ### A section of the orbit map -/

section Orbit

variable (Q : Type) [Group Q] {X : Type} [MulAction Q X]

/-- **The chosen representative of the orbit of a point.** -/
noncomputable def orbitRep (x : X) : X := (Quotient.mk (orbitRel Q X) x).out

theorem orbitRep_mem_orbit (x : X) : orbitRep Q x ∈ orbit Q x :=
  orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel Q X) x)))

theorem orbitRep_smul (σ : Q) (x : X) : orbitRep Q (σ • x) = orbitRep Q x :=
  congrArg Quotient.out (Quotient.sound (orbitRel_apply.2 (mem_orbit x σ)))

/-- **An element of the group carrying the chosen representative of an orbit to a point** of that
orbit. -/
noncomputable def orbitLift (x : X) : Q := (mem_orbit_iff.1 (orbitRep_mem_orbit Q x)).choose⁻¹

theorem orbitLift_smul (x : X) : orbitLift Q x • orbitRep Q x = x :=
  inv_smul_eq_iff.2 (mem_orbit_iff.1 (orbitRep_mem_orbit Q x)).choose_spec.symm

end Orbit

/-! ### The coboundary -/

section Coboundary

variable {Q : Type} [Group Q] [Finite Q] {X : Type} [MulAction Q X] {W : Type} [AddCommGroup W]
  [DistribMulAction Q W]

/-- **A cocycle with values in the finitely supported functions on a set the group acts on which is
a coboundary at every point, on the subgroup fixing that point, is a coboundary.**  Transporting
the value which trivialises the cocycle at the representative of an orbit along a chosen element of
the group, and correcting by the value of the cocycle at that element, gives a function which does
not depend on the choice and whose coboundary is the cocycle. -/
theorem exists_finsupp_eq_sub_of_forall_stabilizer {d : Q → (X →₀ W)}
    (hd : ∀ (σ τ : Q) (x : X), d (σ * τ) x = σ • d τ (σ⁻¹ • x) + d σ x)
    (hloc : ∀ x : X, ∃ u : W, ∀ ρ : Q, ρ • x = x → d ρ x = ρ • u - u) :
    ∃ b : X →₀ W, ∀ (σ : Q) (x : X), d σ x = σ • b (σ⁻¹ • x) - b x := by
  classical
  have hd1 : ∀ x : X, d 1 x = 0 := by
    intro x
    have h := hd 1 1 x
    rw [mul_one, inv_one, one_smul, one_smul] at h
    have h2 : d 1 x + d 1 x = d 1 x + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hinv : ∀ (σ : Q) (x : X), σ • d σ⁻¹ (σ⁻¹ • x) = -d σ x := by
    intro σ x
    have h := hd σ σ⁻¹ x
    rw [mul_inv_cancel, hd1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  set S : Set X := ⋃ σ : Q, ((d σ).support : Set X) with hSdef
  have hSfin : S.Finite := Set.finite_iUnion fun σ => (d σ).support.finite_toSet
  have hdS : ∀ (σ : Q) (x : X), x ∉ S → d σ x = 0 := by
    intro σ x hx
    by_contra h
    exact hx (Set.mem_iUnion.2 ⟨σ, Finsupp.mem_support_iff.2 h⟩)
  choose u hu using hloc
  set v : X → W := fun x => if x ∈ S then u x else 0 with hvdef
  have hv : ∀ (x : X) (ρ : Q), ρ • x = x → d ρ x = ρ • v x - v x := by
    intro x ρ hρ
    by_cases hx : x ∈ S
    · simpa only [hvdef, if_pos hx] using hu x ρ hρ
    · simpa only [hvdef, if_neg hx, smul_zero, sub_zero] using hdS ρ x hx
  have hvS : ∀ x : X, x ∉ S → v x = 0 := fun x hx => by simp only [hvdef, if_neg hx]
  set β : X → W := fun x => orbitLift Q x • v (orbitRep Q x) - d (orbitLift Q x) x with hβdef
  have hβ : ∀ (τ : Q) (x : X), τ • orbitRep Q x = x → β x = τ • v (orbitRep Q x) - d τ x := by
    intro τ x hτ
    have hs : orbitLift Q x • orbitRep Q x = x := orbitLift_smul Q x
    have hxs : (orbitLift Q x)⁻¹ • x = orbitRep Q x := inv_smul_eq_iff.2 hs.symm
    have hρ' : ((orbitLift Q x)⁻¹ * τ) • orbitRep Q x = orbitRep Q x := by
      rw [mul_smul, hτ, hxs]
    have hτeq : orbitLift Q x * ((orbitLift Q x)⁻¹ * τ) = τ := by group
    have h1 := hd (orbitLift Q x) ((orbitLift Q x)⁻¹ * τ) x
    rw [hτeq, hxs, hv _ _ hρ', smul_sub, smul_smul, hτeq] at h1
    simp only [hβdef]
    rw [h1]
    abel
  have hβfin : (Function.support β).Finite := by
    refine Set.Finite.subset
      ((Set.finite_iUnion fun σ : Q => hSfin.image (fun y => σ • y)).union hSfin) ?_
    intro x hx
    by_cases hdx : d (orbitLift Q x) x = 0
    · refine Or.inl (Set.mem_iUnion.2 ⟨orbitLift Q x, ⟨orbitRep Q x, ?_, orbitLift_smul Q x⟩⟩)
      by_contra hmem
      exact hx (by simp only [hβdef, hvS _ hmem, smul_zero, hdx, sub_zero])
    · refine Or.inr ?_
      by_contra hmem
      exact hdx (hdS _ _ hmem)
  refine ⟨Finsupp.ofSupportFinite β hβfin, fun σ x => ?_⟩
  simp only [Finsupp.ofSupportFinite_coe]
  have hrep : orbitRep Q (σ⁻¹ • x) = orbitRep Q x := orbitRep_smul Q σ⁻¹ x
  have hτx : (σ⁻¹ * orbitLift Q x) • orbitRep Q (σ⁻¹ • x) = σ⁻¹ • x := by
    rw [hrep, mul_smul, orbitLift_smul]
  have hb := hβ (σ⁻¹ * orbitLift Q x) (σ⁻¹ • x) hτx
  rw [hrep] at hb
  have h2 := hd σ⁻¹ (orbitLift Q x) (σ⁻¹ • x)
  rw [inv_inv, smul_inv_smul] at h2
  rw [h2, ← smul_smul] at hb
  have h3 : β (σ⁻¹ • x) = σ⁻¹ • β x - d σ⁻¹ (σ⁻¹ • x) := by
    rw [hb]
    simp only [hβdef, smul_sub]
    abel
  rw [h3, smul_sub, smul_inv_smul, hinv]
  abel

omit [Finite Q] in
/-- A family of finitely supported functions satisfying the cocycle identity pointwise is a
one-cocycle of the permutation module. -/
theorem mem_cocycles₁_permFinsuppRep (d : Q → (X →₀ W))
    (hd : ∀ (σ τ : Q) (x : X), d (σ * τ) x = σ • d τ (σ⁻¹ • x) + d σ x) :
    d ∈ cocycles₁ (permFinsuppRep Q X W) :=
  (mem_cocycles₁_iff (A := permFinsuppRep Q X W) d).2 fun σ τ =>
    Finsupp.ext fun x => hd σ τ x

/-- **A class of the first cohomology of the permutation module which is trivial at every point,
on the subgroup fixing that point, vanishes.** -/
theorem H1π_permFinsuppRep_eq_zero (d : Q → (X →₀ W))
    (hd : ∀ (σ τ : Q) (x : X), d (σ * τ) x = σ • d τ (σ⁻¹ • x) + d σ x)
    (hloc : ∀ x : X, ∃ u : W, ∀ ρ : Q, ρ • x = x → d ρ x = ρ • u - u) :
    H1π (permFinsuppRep Q X W) ⟨d, mem_cocycles₁_permFinsuppRep d hd⟩ = 0 := by
  rw [H1π_eq_zero_iff]
  obtain ⟨b, hb⟩ := exists_finsupp_eq_sub_of_forall_stabilizer hd hloc
  exact ⟨b, funext fun σ => Finsupp.ext fun x => (hb σ x).symm⟩

end Coboundary

/-! ### Correcting a cocycle into the kernel of a valuation -/

section Valuation

variable {Q : Type} [Group Q] [Finite Q] {X : Type} [MulAction Q X] {W : Type} [AddCommGroup W]
  [DistribMulAction Q W] {A : Type} [AddCommGroup A] [DistribMulAction Q A]

/-- **A cocycle whose valuation is a coboundary at every point, on the subgroup fixing that point,
becomes a cocycle with values in the kernel of the valuation after subtracting a coboundary.**
This is the shape in which the everywhere locally trivial classes are pushed into the classes with
coefficients in the units which are integral away from a finite set of places: the valuation is the
family of orders at the remaining places, its kernel is the group of those units, and the subgroup
fixing a place is the decomposition group. -/
theorem exists_forall_apply_sub_eq_zero_of_forall_stabilizer (f : A →+ (X →₀ W))
    (hfeq : ∀ (σ : Q) (a : A) (x : X), f (σ • a) x = σ • f a (σ⁻¹ • x))
    (hf : Function.Surjective f) {c : Q → A} (hc : ∀ σ τ : Q, c (σ * τ) = σ • c τ + c σ)
    (hloc : ∀ x : X, ∃ u : W, ∀ ρ : Q, ρ • x = x → f (c ρ) x = ρ • u - u) :
    ∃ a : A, ∀ (σ : Q) (x : X), f (c σ - (σ • a - a)) x = 0 := by
  obtain ⟨b, hb⟩ := exists_finsupp_eq_sub_of_forall_stabilizer (d := fun σ => f (c σ))
    (fun σ τ x => by
      show f (c (σ * τ)) x = σ • f (c τ) (σ⁻¹ • x) + f (c σ) x
      rw [hc, map_add, Finsupp.add_apply, hfeq]) hloc
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨a, fun σ x => ?_⟩
  have hbx : f (c σ) x = σ • f a (σ⁻¹ • x) - f a x := hb σ x
  rw [map_sub, map_sub, Finsupp.sub_apply, Finsupp.sub_apply, hfeq, hbx]
  abel

end Valuation

end InverseGalois.CFT
