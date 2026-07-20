/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Hilbert.GaloisAction
import InverseGalois.Hilbert.HilbertIrreducibility
import InverseGalois.Resolvent.ResolventFamily

/-!

This file assembles the Hilbert-irreducibility construction realizing every symmetric
group `Sₙ` as a Galois group over `ℚ`. It combines a generic resolvent family with
`hilbert_irreducibility_theorem`, independently of the Dedekind specialization.

## Structure

* `card_gal_eq_factorial_of_root` — a *pure Galois-theory* reduction: a **separable**
  degree-`n` polynomial `f` over `ℚ` has `|Gal f| = n!` (equivalently `Gal f = Sₙ`) as
  soon as its splitting field contains a root of *some* irreducible polynomial of degree
  `n!`. This is the target of the resolvent construction. (Separability is enough; we do
  not need to assume `f` irreducible — that follows a posteriori, since `Gal f = Sₙ` is
  transitive.)

* `sn_realizable_of_root` — packages `card_gal_eq_factorial_of_root` into
  `IsInverseGalois (Equiv.Perm (Fin n))`.

* `exists_full_resolvent` — the deep input produced by HIT: for every `n` there is a
  **separable** degree-`n` polynomial `f` whose splitting field contains a root of an
  irreducible degree-`n!` polynomial `g`. This is where the generic-polynomial /
  specialization content enters.

* `perm_fin` — every `Sₙ` is an inverse Galois group, via the above. -/

open Polynomial

noncomputable section

namespace IsInverseGalois

/-- **Pure Galois-theory reduction.**

If `f` is a *separable* polynomial over `ℚ` of degree `n`, and the splitting field of
`f` contains a root of *some* irreducible polynomial `g` of degree `n!`, then
`|Gal f| = n!`, i.e. the Galois group is the full symmetric group `Sₙ`.

The upper bound `|Gal f| ≤ n!` is `galActionHom_injective` (the group embeds into the
permutations of the `n` roots). The lower bound `n! ≤ |Gal f|` comes from
`|Gal f| = [SplittingField : ℚ] ≥ [ℚ(α) : ℚ] = deg (minpoly α) = deg g = n!`, using that
`α` (a root of the irreducible `g`) generates a degree-`n!` subfield. -/
theorem card_gal_eq_factorial_of_root
    (f : ℚ[X]) (hf : f.Separable)
    (g : ℚ[X]) (hg : Irreducible g)
    (hgdeg : g.natDegree = f.natDegree.factorial)
    (α : f.SplittingField) (hα : (aeval α) g = 0) :
    Nat.card f.Gal = f.natDegree.factorial := by
  refine' le_antisymm _ _
  · have h_card_le : Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) := by
      apply_rules [Nat.card_le_card_of_injective]
      convert Polynomial.Gal.galActionHom_injective f f.SplittingField
      exact ⟨Polynomial.SplittingField.splits f⟩
    refine' le_trans h_card_le _
    haveI := Classical.decEq (Polynomial.rootSet f f.SplittingField)
    simp [Fintype.card_perm]
    rw [Polynomial.card_rootSet_eq_natDegree]
    · exact hf
    · exact Polynomial.SplittingField.splits f
  · have h_subfield : Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) =
        f.natDegree.factorial := by
      have h_minpoly : minpoly ℚ α = Polynomial.C (1 / g.leadingCoeff) * g := by
        refine' Eq.symm (minpoly.eq_of_irreducible_of_monic _ _ _)
        · rw [irreducible_mul_iff]
          aesop
        · aesop
        · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, div_mul_cancel₀]
          aesop
      rw [IntermediateField.adjoin.finrank]
      · rw [h_minpoly, Polynomial.natDegree_C_mul] <;> aesop
      · refine IsIntegral.of_finite ℚ α
    have h_subfield : Module.finrank ℚ f.SplittingField ≥ Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) := by
      have := Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ { α }) f.SplittingField
      exact Nat.le_of_dvd (Module.finrank_pos) (dvd_of_mul_right_eq _ this)
    have h_card : Nat.card f.Gal = Module.finrank ℚ f.SplittingField := by
      convert IsGalois.card_aut_eq_finrank ℚ f.SplittingField
      apply_rules [IsGalois.mk]
    linarith

/-- If `f` is separable and its Galois action on the complex roots is bijective, then the
symmetric group on `f.natDegree` letters is an inverse Galois group.

Unlike `IsInverseGalois.of_galActionHom_bijective'`, this result does not assume that `f`
is irreducible. -/
theorem of_galActionHom_bijective_sep (f : ℚ[X]) (hf : f.Separable)
    (hf_bij : Function.Bijective
      (@Polynomial.Gal.galActionHom _ _ f ℂ _ _ ⟨IsAlgClosed.splits _⟩)) :
    IsInverseGalois (Equiv.Perm (Fin f.natDegree)) := by
  have h_ig : IsInverseGalois (Equiv.Perm (f.rootSet ℂ)) :=
    ⟨f.SplittingField, inferInstance, inferInstance, inferInstance,
      { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
        to_normal := SplittingField.instNormal f },
      ⟨MulEquiv.ofBijective _ hf_bij⟩⟩
  have h_card : Fintype.card (f.rootSet ℂ) = Fintype.card (Fin f.natDegree) := by
    rw [Polynomial.card_rootSet_eq_natDegree hf (IsAlgClosed.splits _), Fintype.card_fin]
  exact h_ig.of_mulEquiv
    { Equiv.permCongr (Fintype.equivOfCardEq h_card) with
      map_mul' := fun σ τ => by
        ext
        simp [Equiv.permCongr] }

/-- The Galois action of a separable polynomial is bijective when its Galois group has
order `f.natDegree.factorial`.

Injectivity is the standard faithful action on the roots; equality of the finite source and
target cardinalities then gives surjectivity. -/
theorem galActionHom_bijective_of_card_eq_factorial_sep (f : ℚ[X]) (hf : f.Separable)
    (hf_card : Nat.card f.Gal = f.natDegree.factorial) :
    Function.Bijective
      (@Polynomial.Gal.galActionHom _ _ f ℂ _ _ ⟨IsAlgClosed.splits _⟩) := by
  letI : Fact ((f.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits _⟩
  let φ := Polynomial.Gal.galActionHom f ℂ
  have hφ_injective : Function.Injective φ :=
    Polynomial.Gal.galActionHom_injective f ℂ
  have hperm_card : Nat.card (Equiv.Perm (f.rootSet ℂ)) =
      f.natDegree.factorial := by
    simp [Fintype.card_perm,
      Polynomial.card_rootSet_eq_natDegree hf (IsAlgClosed.splits _)]
  haveI := Fintype.ofFinite f.Gal
  exact (Fintype.bijective_iff_injective_and_card φ).2
    ⟨hφ_injective, by
      simpa [Nat.card_eq_fintype_card] using hf_card.trans hperm_card.symm⟩

/-- A separable polynomial realizes the full symmetric group if its splitting field
contains a root of an irreducible polynomial whose degree is `f.natDegree.factorial`. -/
theorem sn_realizable_of_root
    (f : ℚ[X]) (hf : f.Separable)
    (g : ℚ[X]) (hg : Irreducible g)
    (hgdeg : g.natDegree = f.natDegree.factorial)
    (α : f.SplittingField) (hα : (aeval α) g = 0) :
    IsInverseGalois (Equiv.Perm (Fin f.natDegree)) := by
  exact of_galActionHom_bijective_sep f hf
    (galActionHom_bijective_of_card_eq_factorial_sep f hf
      (card_gal_eq_factorial_of_root f hf g hg hgdeg α hα))

/-- **Deep input: the generic resolvent family.**

For every `n ≥ 1` there is a bivariate pair `(F, G) ∈ ℚ[T][X] × ℚ[T][Y]` where:

* `F` is monic in `X` of degree `n` (the "generic" degree-`n` polynomial, up to a chosen
  one-parameter specialization), separable for all but finitely many specializations;
* `G` is monic in `Y` of degree `n!`, irreducible **and absolutely irreducible** over
  `ℚ(T)` (this is the statement that the generic Galois group is `Sₙ`, geometrically);
* `G` is a *resolvent* of `F`: for every `t`, each root of the specialization
  `G(t, Y)` lies in the splitting field of `F(t, X)`.

This packages the classical generic-polynomial / resolvent construction. Its proof is
factored through `ResolventFamily.exists_resolvent_family_core`, which develops the Morse
family, symmetric-function descent, and arithmetic and geometric irreducibility of the
resolvent.

**On the final conjunct `{t | Irreducible (specialize G t)}.Infinite`.** For an absolutely
irreducible `G` of `X`-degree `≥ 1`, Hilbert's Irreducibility Theorem
(`hilbert_irreducibility_theorem`) shows that `G` has infinitely many irreducible integer
specializations; this conjunct is therefore a *true consequence* of the preceding ones.

**Backwards decomposition.** This lemma is proved from the decomposition developed in
`InverseGalois.Resolvent.ResolventFamily`: `exists_resolvent_family_core` supplies the family
`F = Xⁿ − X − T` and the descended generic linear resolvent `G` with all conjuncts except
the last, and this file discharges the last conjunct via
`hilbert_irreducibility_theorem`. -/
theorem exists_resolvent_family (n : ℕ) (hn : 1 ≤ n) :
    ∃ (F G : Polynomial (Polynomial ℚ)),
      F.Monic ∧ F.natDegree = n ∧
      G.Monic ∧ G.natDegree = n.factorial ∧ Irreducible G ∧
      Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))) ∧
      {t : ℤ | ¬ (specialize F t).Separable}.Finite ∧
      (∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0) ∧
      {t : ℤ | Irreducible (specialize G t)}.Infinite := by
  obtain ⟨F, G, hFmonic, hFdeg, hGmonic, hGdeg, hGirr, hGabs, hFsep, hroot⟩ :=
    ResolventFamily.exists_resolvent_family_core n hn
  refine ⟨F, G, hFmonic, hFdeg, hGmonic, hGdeg, hGirr, hGabs, hFsep, hroot, ?_⟩
  -- The final conjunct is Hilbert's Irreducibility Theorem applied to the (absolutely)
  -- irreducible resolvent `G`, whose `Y`-degree `n! ≥ 1`.
  refine hilbert_irreducibility_theorem G hGirr ?_ hGabs
  rw [hGdeg]
  exact n.factorial_pos

/-- **The HIT glue.**

For every `n ≥ 1` there exists a separable degree-`n` polynomial `f` over `ℚ` whose
splitting field contains a root of an irreducible degree-`n!` polynomial `g`.

This is obtained from the generic resolvent family `exists_resolvent_family`: the set of
integers `t` with `G(t, Y)` irreducible (of degree `n!`) is infinite (the final conjunct of
`exists_resolvent_family`, itself the output of Hilbert's Irreducibility Theorem applied to
the absolutely irreducible `G`), and only finitely many `t` make `F(t, X)` inseparable, so
some `t₀` makes `f = F(t₀, X)` separable of degree `n` while `g = G(t₀, Y)` is irreducible of
degree `n!`; the resolvent property supplies the root of `g` inside the splitting field of
`f`. The irreducible-specialization fact is taken directly from
`exists_resolvent_family`, so this assembly does not repeat the Hilbert-irreducibility
argument. -/
theorem exists_full_resolvent (n : ℕ) (hn : 1 ≤ n) :
    ∃ (f : ℚ[X]) (g : ℚ[X]) (α : f.SplittingField),
      f.Separable ∧ f.natDegree = n ∧
      Irreducible g ∧ g.natDegree = n.factorial ∧ (aeval α) g = 0 := by
  obtain ⟨F, G, hFmonic, hFdeg, hGmonic, hGdeg, _, _, hFsep, hcontain, hinf⟩ :=
    exists_resolvent_family n hn
  obtain ⟨t₀, ht₀A, ht₀B⟩ := (hinf.diff hFsep).nonempty
  have hf_sep : (specialize F t₀).Separable := not_not.mp ht₀B
  obtain ⟨α, hα⟩ := hcontain t₀
  refine ⟨specialize F t₀, specialize G t₀, α, hf_sep, ?_, ht₀A, ?_, hα⟩
  · rw [specialize_monic_natDegree F hFmonic, hFdeg]
  · rw [specialize_monic_natDegree G hGmonic, hGdeg]

/-- Every finite symmetric group is an inverse Galois group over `ℚ`. -/
theorem perm_fin (n : ℕ) : IsInverseGalois (Equiv.Perm (Fin n)) := by
  cases n with
  | zero => exact unit.of_mulEquiv MulEquiv.ofUnique.symm
  | succ n =>
      obtain ⟨f, g, α, hf, hdeg, hg, hgdeg, hα⟩ :=
        exists_full_resolvent (n + 1) (Nat.succ_pos n)
      rw [← hdeg]
      exact sn_realizable_of_root f hf g hg (by simpa [hdeg] using hgdeg) α hα

end IsInverseGalois

end
