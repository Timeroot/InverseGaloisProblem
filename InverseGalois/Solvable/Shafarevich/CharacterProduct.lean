/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.Kummer.RadicalCharacter
import InverseGalois.Solvable.Shafarevich.InducedCocycle
import InverseGalois.Solvable.Shafarevich.LevelOneCharacter

/-!
# A character assembled coordinate by coordinate out of a family of additive ones

The character the first rung of the ladder asks for takes values in an elementary abelian group, and
what the arithmetic supplies is a family of additive characters with values in the cyclic group of
order the exponent, one for each element of the target.  The product of the powers of those elements
by the values of the additive characters is the character wanted, and this file records what the
product does under the two hypotheses the rung imposes on it.

Both hypotheses are read off the coordinates.  The product is onto together with its conjugates as
soon as each coordinate is realised with value one on a subgroup where all the other coordinates
vanish, and as soon as every conjugate the base map moves kills every coordinate: the first gives
each element of the family in the image, and the family generates.  The product carries the
ramification restriction as soon as, at every prime where the induced homomorphism ramifies, all the
coordinates but one vanish on the whole decomposition subgroup outside a single coset, and on that
coset all the coordinates but one vanish; the surviving element of the family is then the bound the
restriction asks for, since a power of it is what the surviving coordinate contributes.

The arrangement is what makes the arithmetic input small.  Indexing the family by the elements of
the target rather than by a basis removes any linear algebra from the generation clause, and reading
the ramification off one coordinate at a time removes any need to compare the induced homomorphism
with the character it comes from.

## Main definitions

* `InverseGalois.Shafarevich.charProd` — the product over a finite family of the powers of fixed
  elements by the values of additive characters.

## Main results

* `InverseGalois.Shafarevich.charProd_apply_of_forall_ne` — a product character with a single
  surviving coordinate is the corresponding power.
* `InverseGalois.Shafarevich.exists_inducedCocycle_ne_one` — a character inducing a homomorphism
  nontrivial at an element of the kernel is nontrivial in some coordinate of the cocycle there.
* `InverseGalois.Shafarevich.inducedNorm_surjective_of_charProd` — **a product character built from
  a generating family is jointly onto with its conjugates as soon as each factor is realised on a
  subgroup the others vanish on and every conjugate the base map moves is killed.**
* `InverseGalois.Shafarevich.isSplitTotallyRamifiedHom_inducedHom_charProd` — **a product character
  induces a homomorphism carrying the ramification restriction as soon as, at every prime where it
  ramifies, one coordinate carries the whole of it and one factor carries the whole of that
  coordinate.**

## Tags

Shafarevich's theorem, embedding problem, Frattini layer, character, Kummer theory, ramification
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT

/-! ### A coordinate of the cocycle a character induces -/

section Missing

variable {G U V : Type*} [Group G] [Group U] [CommGroup V] (φ : G →* U) (r : U → G)
  (χ : ↥φ.ker →* V)

/-- A character inducing a homomorphism nontrivial at an element of the kernel of the base map is
nontrivial in some coordinate of the cocycle it induces there, the homomorphism being the product of
the coordinates. -/
theorem exists_inducedCocycle_ne_one (hr : ∀ u, φ (r u) = u) {x : G} (hx : φ x = 1)
    (h : inducedHom φ r χ hr x ≠ 1) : ∃ u, inducedCocycle φ r χ hr x u ≠ 1 := by
  by_contra hcon
  push_neg at hcon
  exact h (by rw [inducedHom_of_mem_ker φ r χ hr hx,
    show inducedCocycle φ r χ hr x = 1 from funext hcon, _root_.map_one])

end Missing

/-! ### The product character -/

section Product

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] {ℓ : ℕ} [NeZero ℓ] {ι : Type*}
  [Fintype ι] {v : ι → V} {hv : ∀ i, v i ^ ℓ = 1} {f : ι → G → ZMod ℓ}
  {hf : ∀ i, ∀ x y : G, f i (x * y) = f i x + f i y}

variable (v hv f hf) in
/-- The product over a finite family of the powers of fixed elements by the values of characters. -/
noncomputable def charProd : G →* V := ∏ i, rootHom (v i) (hv i) (f i) (hf i)

/-- A product character is the product of the powers of the elements of the family by the values of
the coordinates. -/
theorem charProd_apply (x : G) : charProd v hv f hf x = ∏ i, v i ^ (f i x).val := by
  rw [charProd, MonoidHom.finset_prod_apply]
  exact Finset.prod_congr rfl fun i _ => rootHom_apply _ _ _ _ x

/-- A product character with a single surviving coordinate is the corresponding power. -/
theorem charProd_apply_of_forall_ne {i₀ : ι} {x : G} (h : ∀ i, i ≠ i₀ → f i x = 0) :
    charProd v hv f hf x = v i₀ ^ (f i₀ x).val := by
  rw [charProd_apply]
  refine Finset.prod_eq_single i₀ (fun i _ hi => ?_) (fun hi => absurd (Finset.mem_univ i₀) hi)
  rw [h i hi, ZMod.val_zero, pow_zero]

/-- A product character is trivial where all its coordinates vanish. -/
theorem charProd_eq_one {x : G} (h : ∀ i, f i x = 0) : charProd v hv f hf x = 1 := by
  rw [charProd_apply]
  exact Finset.prod_eq_one fun i _ => by rw [h i, ZMod.val_zero, pow_zero]

/-- A product character takes the value of a member of the family where the corresponding coordinate
takes the value one and all the others vanish. -/
theorem charProd_eq_of_val_eq_one {i₀ : ι} {x : G} (h : ∀ i, i ≠ i₀ → f i x = 0)
    (h1 : (f i₀ x).val = 1) : charProd v hv f hf x = v i₀ := by
  rw [charProd_apply_of_forall_ne h, h1, pow_one]

end Product

/-! ### Generation -/

section Surjective

variable {G U : Type*} [Group G] [Group U] {V : Type*} [CommGroup V] {ℓ : ℕ} [NeZero ℓ]
  {ι : Type*} [Fintype ι]

/-- **A product character built from a generating family is jointly onto with its conjugates as
soon as each factor is realised on a subgroup the others vanish on and every conjugate the base
map moves is killed.** -/
theorem inducedNorm_surjective_of_charProd [DecidableEq U] [Fintype U] (φ : G →* U) (r : U → G)
    (hr : ∀ u, φ (r u) = u) {v : ι → V} (hv : ∀ i, v i ^ ℓ = 1) {f : ι → ↥φ.ker → ZMod ℓ}
    (hf : ∀ i, ∀ x y : ↥φ.ker, f i (x * y) = f i x + f i y)
    (htop : Subgroup.closure (Set.range v) = ⊤) (J : ι → Subgroup ↥φ.ker)
    (hone : ∀ i, ∃ y ∈ J i, (f i y).val = 1 ∧ ∀ j, j ≠ i → f j y = 0)
    (htriv : ∀ g : G, φ g ≠ 1 → ∀ i, ∀ y ∈ J i, ∀ j, f j (MulAut.conjNormal g y) = 0) :
    Function.Surjective (inducedNorm φ r (charProd v hv f hf) hr) := by
  refine inducedNorm_surjective_of_iSup φ r _ hr J ?_ ?_
  · refine eq_top_iff.2 ?_
    rw [← htop, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hyJ, hy1, hy0⟩ := hone i
    exact Subgroup.mem_iSup_of_mem i ⟨y, hyJ, charProd_eq_of_val_eq_one hy0 hy1⟩
  · exact fun g hg i y hy => charProd_eq_one fun j => htriv g hg i y hy j

end Surjective

/-! ### Ramification -/

section Ramified

open MulAction NumberField

open scoped Pointwise

variable {U : Type*} [Group U] {V : Type*} [CommGroup V] {ℓ : ℕ} [NeZero ℓ] {ι : Type*}
  [Fintype ι] {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- **A product character induces a homomorphism carrying the ramification restriction as soon as,
at every prime where it ramifies, one coordinate carries the whole of it and one factor carries the
whole of that coordinate.** -/
theorem isSplitTotallyRamifiedHom_inducedHom_charProd (hℓ : ℓ.Prime) (φ : Gal(Ω/k) →* U)
    (r : U → Gal(Ω/k)) (hr : ∀ u, φ (r u) = u) {v : ι → V} (hv : ∀ i, v i ^ ℓ = 1)
    {f : ι → ↥φ.ker → ZMod ℓ} (hf : ∀ i, ∀ x y : ↥φ.ker, f i (x * y) = f i x + f i y)
    (hV : ∀ w : V, w ^ ℓ = 1)
    (h : ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      ∀ x ∈ Ideal.inertia Gal(Ω/k) P, φ x = 1 →
        inducedHom φ r (charProd v hv f hf) hr x ≠ 1 →
        ∃ (u₀ : U) (i₀ : ι), (∀ y ∈ stabilizer Gal(Ω/k) P, φ y = 1) ∧
          (∀ y ∈ stabilizer Gal(Ω/k) P, ∀ u, u ≠ u₀ → ∀ j : ι,
            f j ⟨cocycleArg φ r y u, cocycleArg_mem φ r hr y u⟩ = 0) ∧
            (∀ y ∈ stabilizer Gal(Ω/k) P, ∀ j : ι, j ≠ i₀ →
              f j ⟨cocycleArg φ r y u₀, cocycleArg_mem φ r hr y u₀⟩ = 0) ∧
              ∀ ζ : Ωˣ, ζ ^ (ℓ * ℓ) = 1 → ∀ y ∈ stabilizer Gal(Ω/k) P, y • ζ = ζ) :
    IsSplitTotallyRamifiedHom ℓ φ (inducedHom φ r (charProd v hv f hf) hr) := by
  refine isSplitTotallyRamifiedHom_inducedHom hℓ φ r hr _ hV fun P hPp hPbot x hxI hxφ hxΦ => ?_
  obtain ⟨u₀, i₀, hsplit, hvan, hconc, hμ⟩ := h P hPp hPbot x hxI hxφ hxΦ
  refine ⟨u₀, v i₀, hsplit, fun y hy u hu => ?_, fun y hy => ?_, hv i₀, hμ⟩
  · exact charProd_eq_one fun j => hvan y hy u hu j
  · rw [inducedCocycle_apply, charProd_apply_of_forall_ne (fun j hj => hconc y hy j hj)]
    exact Subgroup.mem_zpowers_iff.2 ⟨(f i₀ _).val, (zpow_natCast _ _)⟩

end Ramified

end InverseGalois.Shafarevich
