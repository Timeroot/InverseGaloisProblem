/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Hilbert.Analytic.NewtonPuiseux
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# Quadratic discriminant descent (family-agnostic)

This file develops the **group-theoretic heart** of the Serre alternating-group families in a
*reusable*, family-agnostic form.

The mathematical statement is:

> If a separable polynomial `f ∈ K[X]` has geometric Galois group the full symmetric group `Sₙ`
> over `K`, then over the quadratic extension `K' = K(√(disc f))` its Galois group is exactly the
> alternating group `Aₙ`.

The proof splits into the two classical halves, but with a decisive simplification:

* **`≤` (`galActionHom_range_le_alternating_of_disc_sq`).**  Over `K'` the discriminant is a
  *square*, so every Galois automorphism acts as an even permutation of the roots and the image of
  `galActionHom` lands inside the alternating group.  This reuses the repository's generic
  `gal_le_alternating_of_disc_sq` (`InverseGalois/Resolvent/PolynomialGaloisTheory.lean`).

* **`≥` / equality (the descent).**  The extension `K'/K` has degree `2`, cut out by `√disc`,
  whose fixed subgroup under the Galois correspondence is exactly `ker(sign) = Aₙ`.  Concretely
  `Gal(SF/K') = Gal(SF/K) ∩ Aₙ = Sₙ ∩ Aₙ = Aₙ`, so the `K'`-Galois group has order `n!/2`.

The key packaging insight is that **`Aₙ` is the unique index-2 subgroup of `Sₙ`**
(`Equiv.Perm.eq_alternatingGroup_of_index_eq_two`).  Hence the entire equality
`range = alternatingGroup` follows from the single *cardinality* statement
`2 · |Gal_{K'}| = n!`.  This makes:

* `galActionHom_range_eq_alternating_of_card` — the pure group-theoretic core; and
* `galActionHom_range_eq_alternating_of_quadratic_disc` — the natural-input interface that the
  even *and* odd Serre-family descent agents build against — which reduces, via
  `card_gal_descent_of_quadratic`, to the single field-theory fact `2 · |Gal_{K'}| = |Gal_K|`
  (the degree halving), established by `le_antisymm`: the upper bound uses the
  discriminant-square certificate `hle` (`range ≤ Aₙ`), and the lower bound uses the tower law
  `[SF : K] = [K':K]·[SF:K']` together with the embedding `SF_f ↪ SF_g`.
-/

open Polynomial
open scoped Classical

noncomputable section

namespace QuadraticDescent

/-- `Fact` instance: any polynomial splits in its own splitting field.  Kept `local`. -/
local instance splitsInSplittingField (F : Type*) [Field F] (p : F[X]) :
    Fact ((p.map (algebraMap F p.SplittingField)).Splits) := ⟨SplittingField.splits p⟩

/-!
## The generic descent lemma
-/

/-- **The group-theoretic core.**

If the `K'`-Galois group of `g` has order exactly `n!/2` (phrased as `2 · |g.Gal| = n!`), where
`n` is the number of roots, then the image of the permutation representation `galActionHom` is
*exactly* the alternating group on the roots.

This is the reusable target: both the even and the odd Serre families reduce their descent to
supplying the cardinality hypothesis `hdesc` (see `card_gal_descent_of_quadratic`).  The proof is
the observation that `Aₙ` is the unique index-2 subgroup of `Sₙ`
(`Equiv.Perm.eq_alternatingGroup_of_index_eq_two`). -/
theorem galActionHom_range_eq_alternating_of_card
    {K' : Type*} [Field K'] (g : K'[X]) {n : ℕ}
    (hcardRoot : Fintype.card (g.rootSet g.SplittingField) = n)
    (hdesc : 2 * Nat.card g.Gal = n.factorial) :
    (Gal.galActionHom g g.SplittingField).range
      = alternatingGroup (g.rootSet g.SplittingField) := by
  -- The Galois group embeds into `Perm (rootSet)`; its range is isomorphic to `g.Gal`.
  have hinj := Gal.galActionHom_injective g g.SplittingField
  have hcardRange : Nat.card (Gal.galActionHom g g.SplittingField).range = Nat.card g.Gal :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  -- `|Perm (rootSet)| = n!`.
  have hperm : Nat.card (Equiv.Perm (g.rootSet g.SplittingField)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardRoot]
  -- Hence the range has index 2.
  have hmul := Subgroup.index_mul_card (Gal.galActionHom g g.SplittingField).range
  rw [hcardRange, hperm] at hmul
  -- `range.index * |g.Gal| = n! = 2 * |g.Gal|`, and `|g.Gal| > 0`.
  have hindex : (Gal.galActionHom g g.SplittingField).range.index = 2 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (hmul.trans hdesc.symm)
  -- The unique index-2 subgroup of `Perm (rootSet)` is the alternating group.
  exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex

/-!
### The `≤` half

The containment `range ≤ alternatingGroup` (over `K'`, where the discriminant is a square) is
provided at the enumeration level by the repository's generic
`gal_le_alternating_of_disc_sq` (`InverseGalois/Resolvent/PolynomialGaloisTheory.lean:144`): for
every `σ : g.Gal` there is an even permutation `π` with `σ (v i) = v (π i)` and `sign π = 1`, i.e.
`galActionHom g g.SplittingField σ` is an even permutation of the roots.  We do **not** need this
half separately for the equality below, because `galActionHom_range_eq_alternating_of_card`
derives the *exact* equality from the single cardinality fact via the uniqueness of the index-2
subgroup — the index-2 argument subsumes the `≤` containment.
-/

set_option linter.unusedVariables false in
/-- **The descent (field-theoretic core).**

From the natural inputs

* `hSn` : the geometric Galois group of `f` over `K` is the full symmetric group `Sₙ`
  (`galActionHom` surjective),
* `hK'_deg` : `K'` is a quadratic extension of `K` (`finrank K K' = 2`), and
* `hle` : over `K'` the image of `galActionHom` for `g = f.map (K → K')` is contained in the
  alternating group on the roots (the discriminant-square certificate: `K' = K(√disc)`),

the `K'`-Galois group of `g` has order `n!/2`, i.e. `2 · |g.Gal| = n!`.

The hypothesis `hle` is *essential*: for a general quadratic `K'` (one not containing `√disc`),
`g` remains an `Sₙ`-extension over `K'` and `|g.Gal| = n!`.  The certificate `hle` pins down that
`K'` is the discriminant extension; downstream callers supply it for free from a disc-square fact
(`an_geometric_le_alternating` in `AlternatingFamilyMonodromy`).

Proof outline (`le_antisymm` on `2 · |g.Gal|` and `n!`):

* **Upper bound.**  `g.Gal ≅ range (galActionHom g)`; by `hle` this range sits inside `Aₙ`, so
  `2 · |g.Gal| ≤ 2 · |Aₙ| = |Sₙ| = n!` via `Equiv.Perm.two_mul_nat_card_alternatingGroup`.
* **Lower bound.**  `f` splits in `L := g.SplittingField` (its roots are those of `g`), so
  `SF_f` embeds in `L`; hence `n! = |f.Gal| = [SF_f : K] ≤ [L : K] = [K':K]·[L:K'] = 2·|g.Gal|`
  by the tower law and `Gal.card_of_separable`. -/
theorem card_gal_descent_of_quadratic
    {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [CharZero K]
    (f : K[X]) (hf_sep : f.Separable) {n : ℕ} (hf_deg : f.natDegree = n) (hn : 3 ≤ n)
    (hSn : Function.Surjective (Gal.galActionHom f f.SplittingField))
    [FiniteDimensional K K'] (hK'_deg : Module.finrank K K' = 2)
    (hle : (Gal.galActionHom (f.map (algebraMap K K'))
             (f.map (algebraMap K K')).SplittingField).range
          ≤ alternatingGroup ((f.map (algebraMap K K')).rootSet
             (f.map (algebraMap K K')).SplittingField)) :
    2 * Nat.card (f.map (algebraMap K K')).Gal = n.factorial := by
  set φ := algebraMap K K' with hφ
  set g := f.map φ with hg
  -- `g` is separable of degree `n`, so its root set has `n` elements.
  have hg_sep : g.Separable := hf_sep.map
  have hg_deg : g.natDegree = n := by
    rw [hg, natDegree_map_eq_of_injective φ.injective, hf_deg]
  have hcardRoot : Fintype.card (g.rootSet g.SplittingField) = n := by
    rw [card_rootSet_eq_natDegree hg_sep (SplittingField.splits g), hg_deg]
  -- Step 1 (fully proved): `|f.Gal| = n!` from surjectivity + injectivity of `galActionHom`.
  have hbij : Function.Bijective (Gal.galActionHom f f.SplittingField) :=
    ⟨Gal.galActionHom_injective f f.SplittingField, hSn⟩
  have hcardRootf : Fintype.card (f.rootSet f.SplittingField) = n := by
    rw [card_rootSet_eq_natDegree hf_sep (SplittingField.splits f), hf_deg]
  have hfGal : Nat.card f.Gal = n.factorial :=
    calc Nat.card f.Gal
        = Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_congr (Equiv.ofBijective _ hbij)
      _ = n.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardRootf]
  -- The tower `K → K' → L` on the splitting field of `g` is already available as instances
  -- (`SplittingField` derives `Algebra K` and `IsScalarTower K K'`).
  have : FiniteDimensional K g.SplittingField := Module.Finite.trans K' g.SplittingField
  -- `f` splits in `L`, since its image `g` does and `g.map (K' → L) = f.map (K → L)`.
  have hmapeq : f.map (algebraMap K g.SplittingField)
      = g.map (algebraMap K' g.SplittingField) := by
    rw [hg, map_map, hφ, ← IsScalarTower.algebraMap_eq K K' g.SplittingField]
  have hfsplit : (f.map (algebraMap K g.SplittingField)).Splits := by
    rw [hmapeq]
    exact SplittingField.splits g
  -- The root set is nontrivial (it has `n ≥ 3` elements).
  have : Nontrivial (g.rootSet g.SplittingField) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardRoot]
    omega
  -- Prove `2 · |g.Gal| = n!` by antisymmetry.
  apply le_antisymm
  · -- Upper bound: `range ≤ Aₙ`, and `2·|Aₙ| = |Sₙ| = n!`.
    have hcardRange :
        Nat.card (Gal.galActionHom g g.SplittingField).range = Nat.card g.Gal :=
      (Nat.card_congr
        (MonoidHom.ofInjective (Gal.galActionHom_injective g g.SplittingField)).toEquiv).symm
    have hcardle : Nat.card (Gal.galActionHom g g.SplittingField).range
        ≤ Nat.card (alternatingGroup (g.rootSet g.SplittingField)) :=
      Subgroup.card_le_of_le hle
    calc 2 * Nat.card g.Gal
        = 2 * Nat.card (Gal.galActionHom g g.SplittingField).range := by rw [hcardRange]
      _ ≤ 2 * Nat.card (alternatingGroup (g.rootSet g.SplittingField)) := by gcongr
      _ = Nat.card (Equiv.Perm (g.rootSet g.SplittingField)) :=
          two_mul_nat_card_alternatingGroup
      _ = n.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcardRoot]
  · -- Lower bound: `SF_f ↪ L`, so `n! = [SF_f:K] ≤ [L:K] = 2·[L:K'] = 2·|g.Gal|`.
    have hlift_inj : Function.Injective (SplittingField.lift f hfsplit) :=
      (SplittingField.lift f hfsplit).toRingHom.injective
    have hfr_le :
        Module.finrank K f.SplittingField ≤ Module.finrank K g.SplittingField :=
      LinearMap.finrank_le_finrank_of_injective
        (f := (SplittingField.lift f hfsplit).toLinearMap) hlift_inj
    calc n.factorial
        = Nat.card f.Gal := hfGal.symm
      _ = Module.finrank K f.SplittingField := Gal.card_of_separable hf_sep
      _ ≤ Module.finrank K g.SplittingField := hfr_le
      _ = Module.finrank K K' * Module.finrank K' g.SplittingField :=
          (Module.finrank_mul_finrank K K' g.SplittingField).symm
      _ = 2 * Module.finrank K' g.SplittingField := by rw [hK'_deg]
      _ = 2 * Nat.card g.Gal := by rw [Gal.card_of_separable hg_sep]

/-- **Main interface: the family-agnostic quadratic discriminant descent.**

If `f ∈ K[X]` is separable of degree `n ≥ 3` with geometric Galois group the full symmetric group
`Sₙ` over `K`, `K'` is a quadratic extension of `K`, and over `K'` the image of the permutation
representation `galActionHom` of `g = f.map (K → K')` is contained in the alternating group
(the discriminant-square certificate that pins down `K' = K(√(disc f))`), then over `K'` that image
is *exactly* the alternating group on the roots.

The containment hypothesis `hle` is necessary: for a general quadratic `K'` not containing `√disc`,
`g` stays an `Sₙ`-extension over `K'`.  Downstream callers obtain `hle` for free from a disc-square
fact (`an_geometric_le_alternating` in `AlternatingFamilyMonodromy`).

This is the precise interface the even and odd Serre-family descent agents build against. -/
theorem galActionHom_range_eq_alternating_of_quadratic_disc
    {K K' : Type*} [Field K] [Field K'] [Algebra K K'] [CharZero K]
    (f : K[X]) (hf_sep : f.Separable) {n : ℕ} (hf_deg : f.natDegree = n) (hn : 3 ≤ n)
    (hSn : Function.Surjective (Gal.galActionHom f f.SplittingField))
    [FiniteDimensional K K'] (hK'_deg : Module.finrank K K' = 2)
    (hle : (Gal.galActionHom (f.map (algebraMap K K'))
             (f.map (algebraMap K K')).SplittingField).range
          ≤ alternatingGroup ((f.map (algebraMap K K')).rootSet
             (f.map (algebraMap K K')).SplittingField)) :
    (Gal.galActionHom (f.map (algebraMap K K'))
        (f.map (algebraMap K K')).SplittingField).range
      = alternatingGroup ((f.map (algebraMap K K')).rootSet
          (f.map (algebraMap K K')).SplittingField) := by
  set g := f.map (algebraMap K K') with hg
  -- `g` is separable of degree `n`, so its root set has `n` elements.
  have hg_sep : g.Separable := hf_sep.map
  have hg_deg : g.natDegree = n := by
    rw [hg, natDegree_map_eq_of_injective (algebraMap K K').injective, hf_deg]
  have hcardRoot : Fintype.card (g.rootSet g.SplittingField) = n := by
    rw [card_rootSet_eq_natDegree hg_sep (SplittingField.splits g), hg_deg]
  -- Supply the cardinality hypothesis via the descent, then invoke the group-theoretic core.
  exact galActionHom_range_eq_alternating_of_card g hcardRoot
    (card_gal_descent_of_quadratic f hf_sep hf_deg hn hSn hK'_deg hle)

end QuadraticDescent

end
