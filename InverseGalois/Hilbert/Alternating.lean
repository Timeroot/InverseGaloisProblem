/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Cyclic
import InverseGalois.Hilbert.RegularExtension
import InverseGalois.Resolvent.PolynomialGaloisTheory
import InverseGalois.Hilbert.AlternatingFamilyAnalytic
import InverseGalois.Hilbert.AlternatingFamilyOddAnalytic

/-!
# Alternating groups are inverse Galois groups (via Hilbert irreducibility)

This is the alternating-group analogue of the symmetric-group construction, built on the
group-agnostic core in `Hilbert/RegularExtension.lean` (`realizable_of_embeds_and_root` /
`IsInverseGalois.of_regular_family`).

## Structure

* `an_realizable_of_root` — the single-polynomial reduction: a separable degree-`n` polynomial
  `f` whose **discriminant is a square in `ℚ`** and whose splitting field contains a root of an
  irreducible degree-`n!/2` polynomial realizes `Aₙ`.  (The square discriminant supplies the
  embedding `Gal f ↪ Aₙ` via `exists_gal_embeds_alternating`; the rest is
  `realizable_of_embeds_and_root`.)

* `exists_alternating_resolvent_family` — **the deep geometric input** (currently `sorry`): a
  regular `Aₙ`-resolvent family over `ℚ(T)` (Mestre's square-discriminant construction).  See
  its docstring for the decomposition.

* `alternating_inverse_galois` — every `Aₙ` is an inverse Galois group over `ℚ`.  Unconditional
  for `n ≤ 3`; for `n ≥ 4` it feeds the family into the reusable `of_regular_family` core.

## Toward the rigidity method

The A_n case is deliberately assembled through `IsInverseGalois.of_regular_family`, the same
group-agnostic "regular `H`-extension of `ℚ(T)` ⟹ `IsInverseGalois H`" seam that the symmetric
case fits and that the rigidity method will target.  The only A_n-specific pieces are (a) the
square-discriminant *landing certificate* `Gal(F(t)) ↪ Aₙ` (from
`exists_gal_embeds_alternating`) and (b) the geometric family itself
(`exists_alternating_resolvent_family`). -/

open Polynomial

noncomputable section

namespace IsInverseGalois

/-- **The single-polynomial alternating-group reduction.**

If `f` is separable of degree `n ≥ 2`, its discriminant `discSq` (of the roots) is a square in
`ℚ`, and its splitting field contains a root of an irreducible polynomial `g` of degree `n!/2`,
then `Aₙ = alternatingGroup (Fin n)` is an inverse Galois group over `ℚ`.

Instantiates `realizable_of_embeds_and_root` at `H = alternatingGroup (Fin n)`: the
square-discriminant hypothesis supplies the embedding `Gal f ↪ Aₙ` via
`exists_gal_embeds_alternating`, and `|Aₙ| = n!/2` matches the resolvent degree. -/
theorem an_realizable_of_root (n : ℕ) (hn : 2 ≤ n)
    (f : ℚ[X]) (hf : f.Separable) (hdeg : f.natDegree = n)
    (v : Fin n ≃ f.rootSet f.SplittingField)
    (h_sq : ∃ d : ℚ, discSq (fun i => (v i : f.SplittingField)) =
      (algebraMap ℚ f.SplittingField d) ^ 2)
    (g : ℚ[X]) (hg : Irreducible g) (hgdeg : g.natDegree = n.factorial / 2)
    (α : f.SplittingField) (hα : (aeval α) g = 0) :
    IsInverseGalois (alternatingGroup (Fin n)) := by
  have hntriv : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  -- The half-discriminant is nonzero because the roots are distinct (Vandermonde).
  have h_ne : discElem (fun i ↦ (v i : f.SplittingField)) ≠ 0 := by
    unfold discElem
    rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
    push_neg
    exact fun i j h ↦ (Subtype.val_injective.comp v.injective) h
  have h_alt_card : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨g', hg'inj⟩ := exists_gal_embeds_alternating f hf.ne_zero v h_sq h_ne
  exact realizable_of_embeds_and_root f hf hdeg (alternatingGroup (Fin n)) g' hg'inj
    g hg (hgdeg.trans h_alt_card.symm) α hα

/-- **The deep geometric input: an `Aₙ`-resolvent family (currently `sorry`).**

For every `n ≥ 2` there is a bivariate pair `(F, G) ∈ ℚ[T][X] × ℚ[T][Y]` where:

* `F` is monic in `X` of degree `n`, and — the crucial `Aₙ`-specific feature — its
  **discriminant is identically a perfect square** in `ℚ[T]`, so every specialization
  `F(t, X)` has square discriminant and hence Galois group contained in `Aₙ`;
* `G` is monic in `Y` of degree `n!/2`, irreducible and **absolutely irreducible** over `ℚ(T)`
  (i.e. the *geometric* monodromy group is exactly `Aₙ`);
* `G` is a *resolvent* of `F`: for every `t`, each root of `G(t, Y)` lies in the splitting
  field of `F(t, X)` (concretely, `G` descends `∏_{σ ∈ Aₙ}(Y − ∑ᵢ cᵢ α_{σ(i)})`, the `Aₙ`-orbit
  of a generic linear form, of size `|Aₙ| = n!/2`);
* all but finitely many specializations of `F` are separable, with square discriminant
  (packaged as the per-`t` `discSq` conjunct — the landing certificate for `of_regular_family`).

**Status.** This is the genuine hard content — a regular `Aₙ`-extension of `ℚ(T)`.  The `Sₙ`
Morse family `Xⁿ − X − T` (`ResolventFamily`) is **not** reusable (its discriminant is not a
square), so a different family plus its own monodromy analysis is required.

**Decomposition (Mestre's construction), for whoever discharges this.** Following Mestre
(*Extensions régulières de `ℚ(T)` de groupe de Galois `Aₙ`*, J. Algebra 131 (1990)), take
`F(T, X) = h(X) − T · g(X)` with `h = ∏ᵢ (X − αᵢ)` (distinct rational `αᵢ`) and `g` a correction
term of degree `< n` chosen so that:
1. `disc F` is a perfect square in `ℚ[T]` (the `Aₙ`-forcing condition; a Mestre ansatz solves
   for `g`) — yields the per-`t` `discSq` conjunct and monodromy `⊆ Aₙ`;
2. every finite inertia group is generated by a **3-cycle** (vs. a transposition in the `Sₙ`
   case) — with transitivity this forces geometric monodromy `= Aₙ`
   (`closure_three_cycles_eq_alternating`), giving absolute irreducibility of `G`.
The `Aₙ`-orbit resolvent `G` descends to `ℚ(T)` since its coefficients are `Aₙ`-invariant
`= ℚ[e₁,…,eₙ][δ]` with `δ = √disc F ∈ ℚ(T)` by (1); root-containment and cofinite separability
are then mechanical (as in the `Sₙ` `ResolventFamily`).  The `Sₙ` analytic stack
(`MorseSwap`/`NewtonPuiseux`/`SelmerMorse`) computes transposition-inertia; the `Aₙ` case needs
the analogous 3-cycle computation.

The reduction and `of_regular_family` plumbing around this `sorry` are fully proved, so
discharging this single statement completes `alternating_inverse_galois`. -/
theorem exists_alternating_resolvent_family (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F G : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧
      G.Monic ∧ G.natDegree = n.factorial / 2 ∧ Irreducible G ∧
      Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, (specialize F t).Separable →
        ∃ v : Fin n ≃ (specialize F t).rootSet (specialize F t).SplittingField,
        ∃ d : ℚ, discSq (fun i => (v i : (specialize F t).SplittingField)) =
          (algebraMap ℚ (specialize F t).SplittingField d) ^ 2) ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0) := by
  have hn2 : 2 ≤ n := by omega
  rcases Nat.even_or_odd n with heven | hodd
  · -- **Even `n`:** Serre's polynomial substituted family `serreAnFamily`.
    obtain ⟨G, hGmonic, hGdeg, hGres, hGroot⟩ :=
      AlternatingFamily.exists_altResolvent n hn2 heven
    exact ⟨AlternatingFamily.serreAnFamily n, G,
      AlternatingFamily.serreAnFamily_monic n hn2,
      AlternatingFamily.serreAnFamily_natDegree n hn2,
      hGmonic, hGdeg,
      AlternatingFamily.anResolvent_irreducible n hn heven G hGmonic hGres,
      AlternatingFamily.anResolvent_abs_irreducible n hn heven G hGmonic hGres,
      AlternatingFamily.serreAnFamily_separable_cofinite n hn2,
      AlternatingFamily.serreAnFamily_disc_isSquare_of_separable n hn2 heven,
      hGroot⟩
  · -- **Odd `n`:** the conic family `serreAnFamilyOdd` (Serre §4.5, quadratic-discriminant
    -- case: `∆ ∼ n·T(T−1)`, rationally parametrised by `T = c/(c−U²)`).  Assembled exactly as the
    -- even branch, from the odd algebraic stack (`AlternatingFamilyOdd`) plus the three odd
    -- analytic leaves (`AlternatingFamilyOddAnalytic`).
    obtain ⟨G, hGmonic, hGdeg, hGres, hGroot⟩ :=
      AlternatingFamily.exists_altResolvent_odd n hn2 hodd
    exact ⟨AlternatingFamily.serreAnFamilyOdd n, G,
      AlternatingFamily.serreAnFamilyOdd_monic n hn2,
      AlternatingFamily.serreAnFamilyOdd_natDegree n hn2,
      hGmonic, hGdeg,
      AlternatingFamily.anResolvent_irreducible_odd n hn2 hodd G hGmonic hGres,
      AlternatingFamily.anResolvent_abs_irreducible_odd n hn2 hodd G hGmonic hGres,
      AlternatingFamily.serreAnFamilyOdd_separable_cofinite n hn2,
      AlternatingFamily.serreAnFamilyOdd_disc_isSquare_of_separable n hn2 hodd,
      hGroot⟩

/-- A subsingleton group is trivially an inverse Galois group (realized by `ℚ` itself). -/
theorem isInverseGalois_of_subsingleton {G : Type*} [Group G] [Subsingleton G] :
    IsInverseGalois G :=
  have : Unique G := uniqueOfSubsingleton 1
  unit.of_mulEquiv (MulEquiv.ofUnique (M := Unit))

/-- **Every alternating group `Aₙ` is an inverse Galois group over `ℚ`.**

The cases `n ≤ 3` are unconditional: `A₀, A₁, A₂` are trivial and `A₃ ≅ ℤ/3` is cyclic
(`of_isCyclic`).  For `n ≥ 4` the geometric family `exists_alternating_resolvent_family` is fed
into the reusable regular-extension core `of_regular_family` (the square-discriminant conjunct
providing the `Gal(F(t)) ↪ Aₙ` landing certificate), so the theorem currently depends — only for
`n ≥ 4` — on the single geometric `sorry`. -/
theorem alternating_inverse_galois (n : ℕ) :
    IsInverseGalois (alternatingGroup (Fin n)) := by
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n
    · -- `A₀` trivial
      have : Subsingleton (alternatingGroup (Fin 0)) :=
        ⟨fun a b ↦ Subtype.ext (Equiv.ext fun x ↦ x.elim0)⟩
      exact isInverseGalois_of_subsingleton
    · -- `A₁` trivial
      have : Subsingleton (alternatingGroup (Fin 1)) :=
        ⟨fun a b ↦ Subtype.ext (Equiv.ext fun x ↦ Subsingleton.elim _ _)⟩
      exact isInverseGalois_of_subsingleton
    · -- `A₂` trivial (`|A₂| = 1`)
      have hcard : Nat.card (alternatingGroup (Fin 2)) = 1 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have : Subsingleton (alternatingGroup (Fin 2)) :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      exact isInverseGalois_of_subsingleton
    · -- `A₃ ≅ ℤ/3` cyclic
      have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
      exact of_isCyclic _
  · -- `n ≥ 4`: feed the geometric family into the reusable `of_regular_family` core.
    obtain ⟨F, G, hFmonic, hFdeg, hGmonic, hGdeg, hGirr, hGabs, hFsep, hdisc, hroot⟩ :=
      exists_alternating_resolvent_family n (by omega)
    have hntriv : Nontrivial (Fin n) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
    have h_alt_card : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    -- The square-discriminant conjunct supplies the landing certificate `Gal(F(t)) ↪ Aₙ`.
    have hland (t : ℤ) (ht : (specialize F t).Separable) :
        ∃ g' : (specialize F t).Gal →* alternatingGroup (Fin n), Function.Injective g' := by
      obtain ⟨v, d, hd⟩ := hdisc t ht
      have h_ne : discElem (fun i ↦ (v i : (specialize F t).SplittingField)) ≠ 0 := by
        unfold discElem
        rw [← Matrix.det_vandermonde, Ne, Matrix.det_vandermonde_eq_zero_iff]
        push_neg
        exact fun i j h ↦ (Subtype.val_injective.comp v.injective) h
      exact exists_gal_embeds_alternating (specialize F t) ht.ne_zero v ⟨d, hd⟩ h_ne
    exact of_regular_family (alternatingGroup (Fin n)) F G hFmonic hFdeg hGmonic
      (hGdeg.trans h_alt_card.symm) hGirr hGabs hFsep hland hroot

end IsInverseGalois

end
