/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Characters of a central subgroup of exponent `p`

A subgroup `N` of the centre of a group, all of whose elements satisfy `z ^ p = 1` for a prime
`p`, is an elementary abelian `p`-group, that is, a vector space over the field with `p`
elements.  Its characters — the additive maps from `Additive ↥N` to `ZMod p` — therefore separate
its elements, and there are only finitely many of them when `N` is finite.  This is the form in
which the linear algebra of such a subgroup enters an induction along the lower `p`-central
series: an element of `N` is trivial as soon as every character kills it, and the characters can
be enumerated.

A character is evaluated through `charValue`, which extends it by `0` to the whole ambient group,
so that no membership hypothesis has to be carried through the algebra.

## Main definitions

* `InverseGalois.charValue`: the value of a character of `N` at an element of the ambient group,
  taken to be `0` outside `N`.

## Main results

* `InverseGalois.exists_charValue_ne_zero`: **the characters separate the elements of a central
  subgroup of exponent `p`.**
* `InverseGalois.eq_one_iff_forall_charValue_eq_zero`: the same statement as a criterion for
  triviality.
* `InverseGalois.finite_char`: a finite subgroup has only finitely many characters.

## Tags

elementary abelian group, character, centre, `p`-group
-/

namespace InverseGalois

variable {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}

/-- A subgroup of the centre of a group is commutative. -/
def commGroupOfLeCenter (h : N ≤ Subgroup.center G) : CommGroup ↥N :=
  { (inferInstance : Group ↥N) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.2) a) }

/-- The elements of a subgroup of the centre of exponent `p` form a vector space over the field
with `p` elements. -/
noncomputable def zmodModuleOfLeCenter (h : N ≤ Subgroup.center G)
    (hexp : ∀ z ∈ N, z ^ p = 1) :
    letI := commGroupOfLeCenter h
    Module (ZMod p) (Additive ↥N) :=
  letI := commGroupOfLeCenter h
  AddCommGroup.zmodModule fun x => by
    have h1 : (Additive.toMul x) ^ p = 1 := by
      apply Subtype.ext
      push_cast
      exact hexp _ (Additive.toMul x).2
    have h2 : Additive.ofMul ((Additive.toMul x) ^ p) = p • x := ofMul_pow p (Additive.toMul x)
    rw [h1] at h2
    simpa using h2.symm

/-- **The characters of a central subgroup of exponent `p` separate its elements.** -/
theorem exists_char_apply_ne_zero (hp : p.Prime) (h : N ≤ Subgroup.center G)
    (hexp : ∀ z ∈ N, z ^ p = 1) {z : ↥N} (hz : z ≠ 1) :
    ∃ φ : Additive ↥N →+ ZMod p, φ (Additive.ofMul z) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI := commGroupOfLeCenter h
  letI := zmodModuleOfLeCenter h hexp
  have hz' : Additive.ofMul z ≠ 0 := fun hc => hz (Additive.ofMul.injective hc)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hz'
  exact ⟨f.toAddMonoidHom, hf⟩

theorem finite_char (hp : p ≠ 0) [Finite ↥N] : Finite (Additive ↥N →+ ZMod p) := by
  haveI : NeZero p := ⟨hp⟩
  exact Finite.of_injective (fun φ => (φ : Additive ↥N → ZMod p)) DFunLike.coe_injective

/-! ## Evaluation -/

/-- The value of a character of a subgroup `N` at an element of the ambient group, taken to be
`0` outside `N`. -/
noncomputable def charValue (N : Subgroup G) (φ : Additive ↥N →+ ZMod p) (z : G) : ZMod p :=
  haveI := Classical.dec (z ∈ N)
  if hz : z ∈ N then φ (Additive.ofMul ⟨z, hz⟩) else 0

variable (φ : Additive ↥N →+ ZMod p)

theorem charValue_of_mem {z : G} (hz : z ∈ N) :
    charValue N φ z = φ (Additive.ofMul ⟨z, hz⟩) :=
  dif_pos hz

@[simp] theorem charValue_one : charValue N φ 1 = 0 := by
  rw [charValue_of_mem φ N.one_mem]
  exact φ.map_zero

theorem charValue_mul {u v : G} (hu : u ∈ N) (hv : v ∈ N) :
    charValue N φ (u * v) = charValue N φ u + charValue N φ v := by
  rw [charValue_of_mem φ (N.mul_mem hu hv), charValue_of_mem φ hu, charValue_of_mem φ hv,
    ← map_add]
  rfl

theorem charValue_inv {u : G} (hu : u ∈ N) : charValue N φ u⁻¹ = -charValue N φ u := by
  have h := charValue_mul φ (N.inv_mem hu) hu
  rw [inv_mul_cancel, charValue_one] at h
  linear_combination (norm := abel) -h

theorem charValue_list_prod {l : List G} (hl : ∀ z ∈ l, z ∈ N) :
    charValue N φ l.prod = (l.map (charValue N φ)).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hz : z ∈ N := hl z (by simp)
    have hrest : ∀ w ∈ l, w ∈ N := fun w hw => hl w (by simp [hw])
    rw [List.prod_cons, charValue_mul φ hz (N.list_prod_mem hrest), ih hrest,
      List.map_cons, List.sum_cons]

/-- **An element of a central subgroup of exponent `p` is trivial as soon as every character
kills it.** -/
theorem eq_one_of_forall_charValue_eq_zero (hp : p.Prime) (h : N ≤ Subgroup.center G)
    (hexp : ∀ z ∈ N, z ^ p = 1) {z : G} (hz : z ∈ N)
    (hchar : ∀ φ : Additive ↥N →+ ZMod p, charValue N φ z = 0) : z = 1 := by
  by_contra hne
  have hz1 : (⟨z, hz⟩ : ↥N) ≠ 1 := fun hc => hne (congrArg Subtype.val hc)
  obtain ⟨φ, hφ⟩ := exists_char_apply_ne_zero hp h hexp hz1
  exact hφ ((charValue_of_mem φ hz).symm.trans (hchar φ))

end InverseGalois
