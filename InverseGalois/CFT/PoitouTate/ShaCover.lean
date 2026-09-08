/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ShaSurjection
import InverseGalois.CFT.PoitouTate.ShaTateNatural

/-!
# A single class of complete cohomology that governs every change of the coefficients

An everywhere locally trivial class of the second cohomology is read, by global duality, as a
character of the everywhere locally trivial classes of the first cohomology of the Cartier dual,
and every such character is the pairing against a single class of complete cohomology of a finite
level in degree minus two.  The class of complete cohomology is produced once and for all, before
any change of the coefficients is chosen.

What makes it useful is that it governs *every* change of the coefficients at once.  A map of the
coefficients moves the three ingredients in a compatible way: it carries the everywhere locally
trivial classes of the second cohomology forward, it carries those of the first cohomology of the
Cartier dual backward, and it carries the pairing along with them.  Feeding those three
compatibilities into one another, the character cut out by the class of complete cohomology carried
forward along the map is the character of the locally trivial class carried forward along the same
map.  So **if the class of complete cohomology dies under the map, the everywhere locally trivial
class dies with it.**

This is the shape an embedding problem consumes.  The obstruction to a solution is a class of the
second cohomology which the local conditions have already made everywhere locally trivial; the
statement here turns it into a single class of the complete cohomology of a finite group, and then
any group-theoretic construction that kills that class - a change of the coefficients under which
its complete cohomology dies - kills the obstruction.

Two of the three compatibilities are theorems, of the pairing and of the reading at the level.  The
third, the compatibility of the duality itself, is named as a hypothesis, alongside the injectivity
of the reading it is compatible with.

## Main definitions

* `InverseGalois.CFT.IsShaDualNatural`: the injective reading of the everywhere locally trivial
  classes as characters is compatible with a map of the coefficients.
* `InverseGalois.CFT.HasNaturalShaDualInjection`: such a compatible pair of injective readings
  exists.

## Main results

* `InverseGalois.CFT.exists_tateMap_imp_coeffH2_eq_one`: **a single class of complete cohomology of
  the level in degree minus two whose death under the map of the coefficients forces the everywhere
  locally trivial class to die.**
* `InverseGalois.CFT.exists_tateMap_imp_coeffH2_eq_one_of_hasNaturalShaDualInjection`: the same
  statement from the packaged hypothesis.

## Tags

Poitou-Tate, global duality, local-global principle, complete cohomology, embedding problem
-/

namespace InverseGalois.CFT

open CategoryTheory groupCohomology Tate

noncomputable section

attribute [local instance] repMulDistribMulAction

section Cover

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
  (F : IntermediateField k Ω) [FiniteDimensional k F] [IsGalois k F] [NumberField ↥F]
  (A : Rep ℤ (↥F ≃ₐ[k] ↥F)) [IsAddCyclic ↥A.V] [Finite ↥A.V]
  {B B' : Rep ℤ (↥F ≃ₐ[k] ↥F)} [Finite ↥B.V] [Finite ↥B'.V]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B.V)]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥B'.V)]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B A).V)]
  [MulDistribMulAction Gal(Ω/k) (Multiplicative ↥(linHomObj B' A).V)]
  (hπ : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)
  (hπ' : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥(linHomObj B' A).V),
    g • m = AlgEquiv.restrictNormalHom F g • m)
  (f : B ⟶ B')
  (hf : ∀ (g : Gal(Ω/k)) (m : Multiplicative ↥B.V),
    repMulHom f (g • m) = g • repMulHom f m)

/-- **The injective reading of the everywhere locally trivial classes as characters is compatible
with a map of the coefficients.**  Testing the class carried forward along the map against a
character downstairs is testing the class itself against that character carried backward. -/
def IsShaDualNatural
    (α : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ)))
    (α' : Additive ↥(sha2 (Multiplicative ↥B'.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))) : Prop :=
  ∀ (ε : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)))
    (t : Additive ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω))),
    α' (Additive.ofMul (shaCoeffH2 (repMulHom f) hf (decompositionSubgroups k Ω)
        (Additive.toMul ε))) t
      = α ε (Additive.ofMul (shaCoeffH1 (repMulHom (linHomPreHom A f))
          (repMulHom_smul_gal F A hπ hπ' f) (decompositionSubgroups k Ω) (Additive.toMul t)))

/-- **A compatible pair of injective readings exists.**  Only the injectivity of the reading
downstairs is asked for: it is what turns the death of a character into the death of the class. -/
def HasNaturalShaDualInjection : Prop :=
  ∃ (α : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ)))
    (α' : Additive ↥(sha2 (Multiplicative ↥B'.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))),
    Function.Injective α' ∧ IsShaDualNatural F A hπ hπ' f hf α α'

variable (hB : ∀ b : ↥B.V, Nat.card ↥A.V • b = 0) (hB' : ∀ b : ↥B'.V, Nat.card ↥A.V • b = 0)

include hB hB'

/-- **A single class of complete cohomology of the level in degree minus two governs the everywhere
locally trivial class.**  The class is produced from the character the locally trivial class cuts
out, before the map of the coefficients is used; and once the class of complete cohomology dies
under the map, the character of the locally trivial class carried along the map is identically
zero, so the injectivity of the reading downstairs makes that class trivial. -/
theorem exists_tateMap_imp_coeffH2_eq_one
    {α : Additive ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))}
    {α' : Additive ↥(sha2 (Multiplicative ↥B'.V) (decompositionSubgroups k Ω)) →+
      (Additive ↥(sha1 (Multiplicative ↥(linHomObj B' A).V) (decompositionSubgroups k Ω)) →ₗ[ℤ]
        AddCircle (1 : ℚ))}
    (hα' : Function.Injective α') (hnat : IsShaDualNatural F A hπ hπ' f hf α α')
    (ε : ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω))) :
    ∃ x : ↥(tateModule (linHomObj A B) (-2)),
      tateMap (linHomPostHom A f) (-2) x = 0 →
        coeffH2 (repMulHom f) hf (ε : SmoothH2 Gal(Ω/k) (Multiplicative ↥B.V)) = 1 := by
  obtain ⟨x, hx⟩ := exists_cartierPairing_sha_eq F A B hπ hB (α (Additive.ofMul ε))
  refine ⟨x, fun hkill => ?_⟩
  have hchar : α' (Additive.ofMul
      (shaCoeffH2 (repMulHom f) hf (decompositionSubgroups k Ω) ε)) = 0 := by
    refine LinearMap.ext fun t => ?_
    have hz : cartierPairing A B' hB' (-2) (tateMap (linHomPostHom A f) (-2) x)
        (shaTateLinear F A B' hπ' t) = 0 := by
      rw [hkill, _root_.map_zero, LinearMap.zero_apply]
    have hstep : cartierPairing A B hB (-2) x
        (tateMap (linHomPreHom A f) 1 (shaTateLinear F A B' hπ' t)) = 0 :=
      (cartierPairing_naturality A f hB hB' (-2) x (shaTateLinear F A B' hπ' t)).symm.trans hz
    have hgoal : α (Additive.ofMul ε) (Additive.ofMul (shaCoeffH1 (repMulHom (linHomPreHom A f))
        (repMulHom_smul_gal F A hπ hπ' f) (decompositionSubgroups k Ω) (Additive.toMul t)))
        = 0 := by
      rw [← hx, shaTateLinear_shaCoeffH1 F A hπ hπ' f (Additive.toMul t)]
      exact hstep
    exact (hnat (Additive.ofMul ε) t).trans hgoal
  have hone : shaCoeffH2 (repMulHom f) hf (decompositionSubgroups k Ω) ε = 1 :=
    congrArg Additive.toMul (hα' (hchar.trans (_root_.map_zero α').symm))
  exact congrArg (fun z : ↥(sha2 (Multiplicative ↥B'.V) (decompositionSubgroups k Ω)) =>
    (z : SmoothH2 Gal(Ω/k) (Multiplicative ↥B'.V))) hone

/-- **The governing class, from the packaged hypothesis.** -/
theorem exists_tateMap_imp_coeffH2_eq_one_of_hasNaturalShaDualInjection
    (h : HasNaturalShaDualInjection F A hπ hπ' f hf)
    (ε : ↥(sha2 (Multiplicative ↥B.V) (decompositionSubgroups k Ω))) :
    ∃ x : ↥(tateModule (linHomObj A B) (-2)),
      tateMap (linHomPostHom A f) (-2) x = 0 →
        coeffH2 (repMulHom f) hf (ε : SmoothH2 Gal(Ω/k) (Multiplicative ↥B.V)) = 1 := by
  obtain ⟨_, _, hα', hnat⟩ := h
  exact exists_tateMap_imp_coeffH2_eq_one F A hπ hπ' f hf hB hB' hα' hnat ε

end Cover

end

end InverseGalois.CFT
