/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import InverseGalois.Core.Basic
import InverseGalois.Hilbert.HilbertIrreducibility

/-!
# Regular extensions of `ℚ(T)` and the inverse Galois property (group-agnostic core)

This file factors out the **reusable pipeline** shared by the symmetric-group construction, the
alternating-group construction, and — eventually — the rigidity method: a *regular*
`H`-extension of `ℚ(T)` (packaged as an absolutely-irreducible degree-`|H|` resolvent of a
degree-`n` family `F`, together with a per-specialization certificate that the Galois group
lands in the target subgroup `H ≤ Sₙ`) yields `IsInverseGalois H` by Hilbert irreducibility.

## Design (toward rigidity)

Everything here is stated for an arbitrary subgroup `H ≤ Equiv.Perm (Fin n)` and consumes only:

* a family `F` (monic, degree `n` in `X`) and a resolvent `G` (monic, degree `|H|`,
  absolutely irreducible — i.e. *geometric* monodromy is transitive on the `|H|` roots) that is
  a resolvent of `F`;
* a **landing certificate** `hland`: for every good specialization `t`, `Gal(F(t))` embeds into
  `H`.  This is the group-theoretic constraint that pins the Galois group inside the target — it
  is *trivial* for `H = ⊤` (the `Sₙ` case), comes from the **square discriminant** for
  `H = alternatingGroup` (the `Aₙ` case), and would come from the **rational rigid
  conjugacy-class structure** in the rigidity method.

The two ingredients `of_regular_family` does *not* fix — how the family/resolvent is produced,
and where the landing certificate comes from — are exactly the parts that differ between the
symmetric, alternating, and rigidity constructions. This is the intended seam.

## Main results

* `card_gal_ge_of_root` — a separable `f` whose splitting field contains a root of an
  irreducible `g` has `g.natDegree ≤ |Gal f|`.
* `realizable_of_embeds_and_root` — the per-specialization core: `Gal f ↪ H` plus a root of an
  irreducible degree-`|H|` polynomial gives `Gal f ≃* H`, hence `IsInverseGalois H`.
* `IsInverseGalois.of_regular_family` — the family-level statement: a regular resolvent family
  with a landing certificate yields `IsInverseGalois H`.
-/

open Polynomial

noncomputable section

namespace IsInverseGalois

/-- **Pure Galois-theory lower bound.**

If `f` is separable over `ℚ` and its splitting field contains a root `α` of an irreducible
polynomial `g`, then `g.natDegree ≤ |Gal f|`, via
`|Gal f| = [SplittingField : ℚ] ≥ [ℚ(α) : ℚ] = deg (minpoly α) = deg g`. -/
theorem card_gal_ge_of_root
    (f : ℚ[X]) (hf : f.Separable)
    (g : ℚ[X]) (hg : Irreducible g)
    (α : f.SplittingField) (hα : (aeval α) g = 0) :
    g.natDegree ≤ Nat.card f.Gal := by
  have hcard : Nat.card f.Gal = Module.finrank ℚ f.SplittingField :=
    Polynomial.Gal.card_of_separable hf
  rw [hcard]
  have h_finrank_adjoin :
      Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) = g.natDegree := by
    have h_minpoly : minpoly ℚ α = C (1 / g.leadingCoeff) * g := by
      refine Eq.symm (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_)
      · rw [irreducible_mul_iff]
        aesop
      · aesop
      · rw [Monic, leadingCoeff_mul, leadingCoeff_C, div_mul_cancel₀]
        aesop
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α), h_minpoly, natDegree_C_mul]
    aesop
  have h_finrank_ge :
      Module.finrank ℚ (↥(IntermediateField.adjoin ℚ {α})) ≤
        Module.finrank ℚ f.SplittingField := by
    have := Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {α}) f.SplittingField
    exact Nat.le_of_dvd Module.finrank_pos (dvd_of_mul_right_eq _ this)
  omega

/-- **The per-specialization core.**

Let `f` be separable of degree `n`, let `H ≤ Sₙ` be a subgroup of the permutations of the
roots, suppose `Gal f` **embeds** into `H` (`g'` injective — the landing certificate), and
suppose the splitting field contains a root of an irreducible polynomial `g` of degree `|H|`.
Then `Gal f ≃* H`, so `H` is an inverse Galois group.

The embedding gives `|Gal f| ≤ |H|`; the degree-`|H|` irreducible root gives `|H| ≤ |Gal f|`
(`card_gal_ge_of_root`); so `|Gal f| = |H|` and the injection is a bijection. -/
theorem realizable_of_embeds_and_root {n : ℕ}
    (f : ℚ[X]) (hf : f.Separable) (_hdeg : f.natDegree = n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (g' : f.Gal →* H) (hg'inj : Function.Injective g')
    (g : ℚ[X]) (hg : Irreducible g) (hgdeg : g.natDegree = Nat.card H)
    (α : f.SplittingField) (hα : (aeval α) g = 0) :
    IsInverseGalois H := by
  have hle1 : Nat.card f.Gal ≤ Nat.card H := Nat.card_le_card_of_injective g' hg'inj
  have hle2 : Nat.card H ≤ Nat.card f.Gal := hgdeg ▸ card_gal_ge_of_root f hf g hg α hα
  have heq : Nat.card f.Gal = Nat.card H := le_antisymm hle1 hle2
  have hbij : Function.Bijective g' := by
    have hft := Fintype.ofFinite f.Gal
    have hfh := Fintype.ofFinite H
    exact (Fintype.bijective_iff_injective_and_card _).2
      ⟨hg'inj, by simpa [Nat.card_eq_fintype_card] using heq⟩
  exact ⟨f.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal f },
    ⟨MulEquiv.ofBijective g' hbij⟩⟩

/-- **The family-level regular-realization core (the reusable seam).**

Given a subgroup `H ≤ Sₙ` and a *regular resolvent family* over `ℚ(T)` — a monic degree-`n`
family `F` and a monic, irreducible, **absolutely irreducible** degree-`|H|` resolvent `G` of
`F`, with all but finitely many specializations of `F` separable and a **landing certificate**
`hland` embedding `Gal(F(t)) ↪ H` at each separable specialization — the group `H` is an inverse
Galois group over `ℚ`.

Hilbert irreducibility (`hilbert_irreducibility_theorem`, applicable since `G` is absolutely
irreducible of positive degree) gives infinitely many `t` with `G(t)` irreducible; choosing one
that also keeps `F(t)` separable and feeding `realizable_of_embeds_and_root` finishes it.

Both the symmetric-group and alternating-group developments are instances of this lemma; it is
the shape the rigidity method will target for a general finite group `H`. -/
theorem of_regular_family {n : ℕ}
    (H : Subgroup (Equiv.Perm (Fin n)))
    (F G : Polynomial (Polynomial ℚ))
    (hFmonic : F.Monic) (hFdeg : F.natDegree = n)
    (hGmonic : G.Monic) (hGdeg : G.natDegree = Nat.card H)
    (hGirr : Irreducible G)
    (hGabs : Irreducible (G.map (mapRingHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
    (hFsep : {t : ℤ | ¬ (specialize F t).Separable}.Finite)
    (hland : ∀ t : ℤ, (specialize F t).Separable →
        ∃ g' : (specialize F t).Gal →* H, Function.Injective g')
    (hroot : ∀ t : ℤ, ∃ α : (specialize F t).SplittingField, (aeval α) (specialize G t) = 0) :
    IsInverseGalois H := by
  have hinf : {t : ℤ | Irreducible (specialize G t)}.Infinite := by
    refine hilbert_irreducibility_theorem G hGirr ?_ hGabs
    rw [hGdeg]; exact Nat.card_pos
  obtain ⟨t₀, ht₀A, ht₀B⟩ := (hinf.diff hFsep).nonempty
  have hf_sep : (specialize F t₀).Separable := not_not.mp ht₀B
  obtain ⟨g', hg'inj⟩ := hland t₀ hf_sep
  obtain ⟨α, hα⟩ := hroot t₀
  refine realizable_of_embeds_and_root (specialize F t₀) hf_sep ?_ H g' hg'inj
    (specialize G t₀) ht₀A ?_ α hα
  · rw [specialize_monic_natDegree F hFmonic, hFdeg]
  · rw [specialize_monic_natDegree G hGmonic, hGdeg]

end IsInverseGalois

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Monodromy criterion for the alternating group (rigidity-facing group theory).**

A subgroup `G ≤ Perm α` whose action on `α` is preprimitive, which contains a 3-cycle, and which
is contained in the alternating group, *equals* the alternating group.

This is the group-theoretic heart of "geometric monodromy `= Aₙ`" in the alternating (Mestre)
construction and in the rigidity method: **preprimitivity + a 3-cycle** give `Aₙ ≤ G` (Jordan's
theorem, `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`), while the
**square-discriminant / even-permutation** condition gives `G ≤ Aₙ`.  It is the `Aₙ` analogue of
the `Sₙ` generation criteria (`subgroup_eq_top_of_swap_and_cycle` /
`subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`). -/
theorem eq_alternatingGroup_of_isPreprimitive_of_isThreeCycle
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPreprimitive G α)
    {g : Equiv.Perm α} (h3g : g.IsThreeCycle) (hg : g ∈ G)
    (hle : G ≤ alternatingGroup α) :
    G = alternatingGroup α :=
  le_antisymm hle (alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG h3g hg)

end Equiv.Perm

end
