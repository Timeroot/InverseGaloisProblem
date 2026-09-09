/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Solvable.Shafarevich.InducedCocycle
import InverseGalois.Solvable.Shafarevich.LevelRamification

/-!
# The first rung of the ladder, out of a character of the base realization

The bottom of the ladder is the base realization itself, and the first step above it is the one the
group theory cannot take: the layer there is the Frattini layer of the generic operator group, and a
lift across it carries no guarantee of being onto.  The arithmetic has to supply that rung outright,
and what it supplies is a character.

The group at the first level is the quotient of the generic operator group by the first term of its
descending `ℓ`-central series, extended by the operators.  That quotient is the zeroth layer, an
elementary abelian group the operators act on, and a homomorphism from the Galois group onto its
extension by the operators, lying over the base realization, is exactly what a solution at the first
level is.  Such a homomorphism is built from a character of the kernel of the base realization by
Shapiro's construction: the character is induced up to the whole Galois group, and the induced
module then maps equivariantly onto the layer by summing the translates of the coordinates.  The one
thing the arithmetic must arrange is that the conjugates of the character be jointly onto, and that
is the count Shafarevich's number existence lemma delivers.

## Main definitions

* `InverseGalois.Shafarevich.layerZeroAut` — the operators acting on the zeroth layer.
* `InverseGalois.Shafarevich.layerZeroSemidirect` — the covering of the group at the first level by
  the zeroth layer with the operators alongside.
* `InverseGalois.Shafarevich.HasLevelOneCharacter` — **the character the first rung of the ladder
  asks the arithmetic for.**

## Main results

* `InverseGalois.Shafarevich.layerSub_zero_eq_top` — the zeroth layer is the whole of the quotient
  by the first term of the series.
* `InverseGalois.Shafarevich.levelSolution_one_of_character` — **a character of the kernel of the
  base realization whose conjugates are jointly onto gives a solution at the first level.**
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_inducedHom` — **the homomorphism a character
  induces carries the ramification restriction as soon as, at every prime where it ramifies, one
  coordinate carries the whole of the character on the decomposition subgroup and is bounded there
  by an element the prime kills.**
* `InverseGalois.Shafarevich.levelSolution_one_of_hasLevelOneCharacter` — the character the
  arithmetic supplies gives the first rung of the ladder.
* `InverseGalois.Shafarevich.forall_conj_mem_inducedCharKer` — along a family closed under
  conjugation, local triviality of the character is all that the first rung asks of it.

## Tags

Shafarevich's theorem, embedding problem, Frattini layer, Shapiro's lemma, character
-/

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### The zeroth layer is the whole of the first quotient -/

section Zero

variable (p : ℕ) (P : Type*) [Group P]

/-- **The zeroth layer of the descending `p`-central series is the whole of the quotient by the
first term of the series**, the zeroth term being the group itself. -/
theorem layerSub_zero_eq_top : layerSub p P 0 = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  induction y using QuotientGroup.induction_on with
  | _ x => exact mk_mem_layerSub (n := 0) (by rw [pCentral_zero]; trivial)

/-- Reading the zeroth layer inside the quotient by the first term of the series is onto. -/
theorem subtype_layerSub_zero_surjective :
    Function.Surjective (layerSub p P 0).subtype := fun y =>
  ⟨⟨y, by rw [layerSub_zero_eq_top]; trivial⟩, rfl⟩

end Zero

/-! ### The operators on the zeroth layer -/

section Model

variable (ℓ : ℕ) (U : Type) [Group U] [Finite U] (n : ℕ) (S : Type) [Group S] [Finite S]

/-- The operators, acting by automorphisms on the zeroth layer of a generic operator group. -/
def layerZeroAut : U →* MulAut ↥(layerSub ℓ (Generic U n S) 0) :=
  MulDistribMulAction.toMulAut U ↥(layerSub ℓ (Generic U n S) 0)

omit [Finite U] [Finite S] in
@[simp]
theorem layerZeroAut_apply (u : U) (v : ↥(layerSub ℓ (Generic U n S) 0)) :
    layerZeroAut ℓ U n S u v = u • v := rfl

/-- **The zeroth layer with the operators alongside covers the group at the first level of the
filtration**, the layer being the whole of the quotient by the first term of the series. -/
def layerZeroSemidirect :
    ↥(layerSub ℓ (Generic U n S) 0) ⋊[layerZeroAut ℓ U n S] U →* GenericQuot ℓ U n S 1 :=
  SemidirectProduct.map (layerSub ℓ (Generic U n S) 0).subtype (MonoidHom.id U) fun u =>
    MonoidHom.ext fun v =>
      (pCentralAut_subtype ℓ (genericAut U n S) 0 (genericLayerSubAction_smul U n S ℓ 0) u v).symm

omit [Finite U] [Finite S] in
theorem layerZeroSemidirect_surjective : Function.Surjective (layerZeroSemidirect ℓ U n S) := by
  rintro ⟨y, u⟩
  obtain ⟨v, hv⟩ := subtype_layerSub_zero_surjective ℓ (Generic U n S) y
  exact ⟨⟨v, u⟩, SemidirectProduct.ext hv rfl⟩

omit [Finite U] [Finite S] in
/-- The covering lies over the operators. -/
theorem rightHom_layerZeroSemidirect
    (x : ↥(layerSub ℓ (Generic U n S) 0) ⋊[layerZeroAut ℓ U n S] U) :
    SemidirectProduct.rightHom (layerZeroSemidirect ℓ U n S x)
      = SemidirectProduct.rightHom x := rfl

end Model

/-! ### The solution built from a character -/

section Solution

variable {ℓ : ℕ} {U : Type} [Group U] [Finite U] {n : ℕ} {S : Type} [Group S] [Finite S]
  {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

omit [Finite S] in
/-- **A character of the kernel of the base realization whose conjugates are jointly onto gives a
solution at the first level of the filtration.**

The character is induced up to the whole Galois group by Shapiro's construction, which produces a
homomorphism onto the extension of the operators by the functions on them, and the functions map
equivariantly onto the layer by summing their translates.  Being trivial along the family and
carrying the ramification restriction are read off the character alone: the first asks the character
to kill every conjugate of every element the family names which the base realization kills, and the
second is inherited from the induced homomorphism because it is a statement about values. -/
theorem levelSolution_one_of_character (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k)))
    (r : U → Gal(Ω/k)) (hr : ∀ u, φ (r u) = u)
    (χ : ↥φ.ker →* ↥(layerSub ℓ (Generic U n S) 0))
    (hnorm : Function.Surjective (inducedNorm φ r χ hr))
    (W : Subgroup Gal(Ω/k)) (hW : IsOpenNormal W) (hWφ : W ≤ φ.ker)
    (hWχ : W ≤ inducedCharKer φ χ)
    (hT : ∀ D ∈ T, ∀ x ∈ D, φ x = 1 → ∀ u : U, (r u)⁻¹ * x * r u ∈ inducedCharKer φ χ)
    (hram : IsSplitTotallyRamifiedHom ℓ φ (inducedHom φ r χ hr)) :
    LevelSolution ℓ U S φ T (IsSplitTotallyRamified ℓ U S φ) n 1 := by
  letI : Fintype U := Fintype.ofFinite U
  haveI : W.Normal := hW.normal
  refine ⟨(layerZeroSemidirect ℓ U n S).comp
    ((shiftCounitMap (layerZeroAut ℓ U n S)).comp (inducedHom φ r χ hr)), ?_, ?_, fun _ => rfl,
    ?_, ?_⟩
  · exact (layerZeroSemidirect_surjective ℓ U n S).comp
      ((shiftCounitMap_surjective _).comp (inducedHom_surjective φ r χ hr hnorm))
  · refine fun N _ => ⟨W, hW, fun x hx => Subgroup.mem_comap.2 ?_⟩
    rw [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.mem_ker.1 (le_ker_inducedHom φ r χ hr hWφ hWχ hx), _root_.map_one, _root_.map_one]
    exact N.one_mem
  · intro D hD x hx hφ
    rw [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      inducedHom_eq_one φ r χ hr hφ (hT D hD x hx hφ), _root_.map_one, _root_.map_one]
  · exact (hram.comp (shiftCounitMap (layerZeroAut ℓ U n S))).comp (layerZeroSemidirect ℓ U n S)

end Solution

/-! ### The ramification restriction, read off the character -/

section Ramified

open MulAction NumberField

open scoped Pointwise

variable {ℓ : ℕ} {U V : Type*} [Group U] [CommGroup V] {k Ω : Type*} [Field k] [Field Ω]
  [Algebra k Ω]

/-- **The homomorphism induced by a character carries the ramification restriction as soon as, at
every prime where it ramifies, one coordinate carries the whole of the character on the
decomposition subgroup and is bounded there by an element the prime kills.**

At such a prime the values of the character on the decomposition subgroup are concentrated in a
single coordinate, so the induced values all lie in the powers of the value at the element of
inertia witnessing the ramification: that value is nontrivial, hence generates the cyclic group of
prime order bounding the coordinate.  The remaining clauses — that the base realization kill the
decomposition subgroup, and that the local field carry the roots of unity of the prime squared — are
carried across untouched. -/
theorem isSplitTotallyRamifiedHom_inducedHom (hℓ : ℓ.Prime) (φ : Gal(Ω/k) →* U)
    (r : U → Gal(Ω/k)) (hr : ∀ u, φ (r u) = u) (χ : ↥φ.ker →* V) (hV : ∀ v : V, v ^ ℓ = 1)
    (h : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 → inducedHom φ r χ hr x ≠ 1 →
        ∃ (u₀ : U) (c : V), (∀ y ∈ stabilizer Gal(Ω/k) P, φ y = 1) ∧
          (∀ y ∈ stabilizer Gal(Ω/k) P, ∀ u, u ≠ u₀ → inducedCocycle φ r χ hr y u = 1) ∧
            (∀ y ∈ stabilizer Gal(Ω/k) P, inducedCocycle φ r χ hr y u₀ ∈ Subgroup.zpowers c) ∧
              c ^ ℓ = 1 ∧
                ∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ) = 1 → ∀ y ∈ stabilizer Gal(Ω/k) P, y • ζ = ζ) :
    IsSplitTotallyRamifiedHom ℓ φ (inducedHom φ r χ hr) := by
  refine isSplitTotallyRamifiedHom_of_le_zpowers hℓ fun P hPp hPbot x hxI hxφ hxΦ => ?_
  obtain ⟨u₀, c, hsplit, hvan, hzp, hcℓ, hμ⟩ := h P hPp hPbot x hxI hxφ hxΦ
  have hxst : x ∈ stabilizer Gal(Ω/k) P := Ideal.inertia_le_stabilizer P hxI
  have hxu₀ : inducedCocycle φ r χ hr x u₀ ≠ 1 := by
    intro h0
    refine hxΦ ?_
    have hzero : inducedCocycle φ r χ hr x = 1 := by
      funext u
      by_cases hu : u = u₀
      · subst hu
        exact h0
      · exact hvan x hxst u hu
    rw [inducedHom_of_mem_ker φ r χ hr hxφ, hzero, _root_.map_one]
  have hcmem : c ∈ Subgroup.zpowers (inducedCocycle φ r χ hr x u₀) :=
    mem_zpowers_of_pow_prime hℓ hcℓ (hzp x hxst) hxu₀
  refine ⟨inducedHom φ r χ hr x, hsplit, fun y hy => ?_,
    inducedHom_pow_eq_one φ r χ hr hxφ hV, hμ⟩
  exact inducedHom_mem_zpowers_of_forall_ne φ r χ hr hxφ (hsplit y hy) u₀
    (fun u hu => hvan x hxst u hu) (fun u hu => hvan y hy u hu)
    (Subgroup.zpowers_le.2 hcmem (hzp y hy))

end Ramified

/-! ### The character the arithmetic is asked for -/

section Datum

variable (ℓ : ℕ) (U : Type) [Group U] [Finite U] (S : Type) [Group S] [Finite S]
  {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **The character the first rung of the ladder asks the arithmetic for.**

A section of the base realization, a character of its kernel with values in the zeroth layer of the
generic operator group on the given number of letters, and an open normal subgroup on which both are
trivial, subject to three demands: that the conjugates of the character by the section be jointly
onto, which is the independence count; that the character kill every element of every member of the
family which the base realization kills, which is local triviality; and that the homomorphism the
character induces carry the ramification restriction. -/
def HasLevelOneCharacter (φ : Gal(Ω/k) →* U) (T : Set (Subgroup Gal(Ω/k))) (n : ℕ) : Prop :=
  ∃ (r : U → Gal(Ω/k)) (hr : ∀ u, φ (r u) = u)
      (χ : ↥φ.ker →* ↥(layerSub ℓ (Generic U n S) 0)) (W : Subgroup Gal(Ω/k)),
    Function.Surjective (inducedNorm φ r χ hr) ∧ IsOpenNormal W ∧ W ≤ φ.ker ∧
      W ≤ inducedCharKer φ χ ∧
        (∀ D ∈ T, ∀ x ∈ D, φ x = 1 → ∀ u : U, (r u)⁻¹ * x * r u ∈ inducedCharKer φ χ) ∧
          IsSplitTotallyRamifiedHom ℓ φ (inducedHom φ r χ hr)

variable {ℓ U S}

omit [Finite S] in
/-- **The character the arithmetic supplies gives the first rung of the ladder.** -/
theorem levelSolution_one_of_hasLevelOneCharacter {φ : Gal(Ω/k) →* U}
    {T : Set (Subgroup Gal(Ω/k))} {n : ℕ} (h : HasLevelOneCharacter ℓ U S φ T n) :
    LevelSolution ℓ U S φ T (IsSplitTotallyRamified ℓ U S φ) n 1 := by
  obtain ⟨r, hr, χ, W, hnorm, hW, hWφ, hWχ, hT, hram⟩ := h
  exact levelSolution_one_of_character φ T r hr χ hnorm W hW hWφ hWχ hT hram

omit [Finite U] [Finite S] in
/-- **Along a family closed under conjugation, local triviality of the character is all that the
first rung asks of it.**  A conjugate of an element of a member of the family lies in another
member, and the base realization still kills it, so a character killing every such element kills
every conjugate of every such element. -/
theorem forall_conj_mem_inducedCharKer {φ : Gal(Ω/k) →* U} {T : Set (Subgroup Gal(Ω/k))} {n : ℕ}
    {χ : ↥φ.ker →* ↥(layerSub ℓ (Generic U n S) 0)} (r : U → Gal(Ω/k))
    (hconj : ∀ D ∈ T, ∀ g : Gal(Ω/k), ∃ D' ∈ T, ∀ x ∈ D, g⁻¹ * x * g ∈ D')
    (hker : ∀ D ∈ T, ∀ x ∈ D, φ x = 1 → x ∈ inducedCharKer φ χ) :
    ∀ D ∈ T, ∀ x ∈ D, φ x = 1 → ∀ u : U, (r u)⁻¹ * x * r u ∈ inducedCharKer φ χ := by
  intro D hD x hx hφ u
  obtain ⟨D', hD', hsub⟩ := hconj D hD (r u)
  refine hker D' hD' _ (hsub x hx) ?_
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv, hφ, mul_one, inv_mul_cancel]

end Datum

end InverseGalois.Shafarevich
