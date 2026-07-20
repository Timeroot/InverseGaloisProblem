/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Core.Basic
import InverseGalois.Groups.D5Polynomial
import InverseGalois.Groups.D5GroupFacts
import InverseGalois.Resolvent.PolynomialGaloisTheory

/-!
# D₅ as an Inverse Galois group — the resolvent proof (on-demand build)

## The argument

Let `f = X⁵ − 5X + 12 = X⁵ + C(-5)·X + C 12`, so in the resolvent normal form
`X⁵ + pX + q` we have `p = -5`, `q = 12`.

* **`5 ∣ |Gal f|`** — `f` is irreducible (`f_d5_irreducible`) of degree 5
  (`f_d5_natDegree`), so `natDegree_dvd_card`.
* **`2 ∣ |Gal f|`** — `f` has a non-real complex root (`f_d5_nonreal_root`), so complex
  conjugation gives an involution in the Galois group
  (`two_dvd_card_gal_of_nonreal_root`).
* **`|Gal f| ∣ 20`** — the sextic (Cayley) resolvent `R₆ = sexticResolvent (-5) 12`
  has the rational root `25` (`sexticResolvent_d5_root`), so by
  `card_gal_dvd_20_of_resolvent_root` the Galois group is conjugate into the Frobenius
  group `F₂₀`.
* **`Gal f ↪ A₅`** — the discriminant of `f` is `8000²`, a perfect square
  (`disc_value_d5`, `disc_elem_ne_zero_d5`), so `exists_gal_embeds_alternating` gives an
  injection `Gal f ↪ alternatingGroup (Fin 5)`.

Combining `10 ∣ |Gal f|` and `|Gal f| ∣ 20` gives `|Gal f| ∈ {10, 20}`; the embedding
into `A₅` rules out `20` (`A5_no_subgroup_order_20`), so `|Gal f| = 10`.  The same
embedding shows `Gal f` has no element of order 10 (`perm_fin5_no_order_ten`), so it is
non-cyclic, hence `Gal f ≅ D₅` (`iso_dihedral_five_of_card_ten`). -/

open Polynomial

noncomputable section

namespace D5

/-- `f_d5 = X⁵ − 5X + 12` written in the resolvent normal form `X⁵ + C(-5)·X + C 12`. -/
lemma f_d5_eq : f_d5 = X ^ 5 + C (-5 : ℚ) * X + C 12 := by
  simp only [f_d5, map_neg]
  ring

/-- The sextic resolvent of `X⁵ − 5X + 12` (`p = -5, q = 12`) has the rational root `25`.
This is the algebraic input that forces `|Gal f| ∣ 20`. -/
lemma sexticResolvent_d5_root : (sexticResolvent (-5 : ℚ) 12).IsRoot 25 := by
  simp only [sexticResolvent, Polynomial.IsRoot.def, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X]
  norm_num

/-- The square discriminant of `f_d5` embeds its Galois group into `A₅`.
This packages the discriminant data shared by the order and non-cyclicity arguments. -/
private lemma exists_gal_d5_embeds_alternating :
    ∃ g : f_d5.Gal →* alternatingGroup (Fin 5), Function.Injective g := by
  exact exists_gal_embeds_alternating f_d5 f_d5_ne_zero rootEnum_d5
    ⟨8000, by
      simp only [discSq, discElem]
      rw [disc_value_d5 rootEnum_d5, map_pow]⟩
    (disc_elem_ne_zero_d5 rootEnum_d5)

/-- The Galois group of `X⁵ - 5X + 12` does not have order 120.
This consequence belongs here with the alternating-group embedding rather than among the
polynomial and root computations in `D5Helpers`. -/
theorem card_gal_d5_ne_120 : Nat.card f_d5.Gal ≠ 120 := by
  obtain ⟨g, hg⟩ := exists_gal_d5_embeds_alternating
  exact ne_of_lt <| lt_of_le_of_lt (by simpa using Fintype.card_le_of_injective _ hg)
    (by native_decide)

/-- The Galois group of `X⁵ − 5X + 12` has order 10.

Irreducibility and the non-real root show that its order is divisible by 5 and 2,
respectively. The rational resolvent root makes the order divide 20. The only alternatives
are therefore 10 and 20, and the latter is impossible because the square discriminant embeds
the Galois group into `A₅`, which has no subgroup of order 20. -/
lemma card_gal_d5 : Nat.card f_d5.Gal = 10 := by
  have hdvd20 : Nat.card f_d5.Gal ∣ 20 :=
    card_gal_dvd_20_of_resolvent_root (-5) 12 (by norm_num) f_d5 f_d5_eq f_d5_irreducible 25
      sexticResolvent_d5_root
  have h5 : 5 ∣ Nat.card f_d5.Gal := f_d5_natDegree ▸ natDegree_dvd_card f_d5_irreducible
  obtain ⟨z, hz_root, hz_nonreal⟩ := f_d5_nonreal_root
  have h2 : 2 ∣ Nat.card f_d5.Gal :=
    two_dvd_card_gal_of_nonreal_root f_d5 f_d5_irreducible z hz_root hz_nonreal
  have h10 : 10 ∣ Nat.card f_d5.Gal := by
    simpa using
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 5 by norm_num) h2 h5
  obtain ⟨g', hg'⟩ := exists_gal_d5_embeds_alternating
  have hrange : Nat.card f_d5.Gal = Nat.card (g'.range) :=
    Nat.card_congr (MonoidHom.ofInjective hg').toEquiv
  have hpos : 0 < Nat.card f_d5.Gal := Nat.card_pos
  have hle : Nat.card f_d5.Gal ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd20
  have hne20 : Nat.card f_d5.Gal ≠ 20 := by
    intro h20
    exact A5_no_subgroup_order_20 g'.range (by rw [← hrange, h20])
  omega

/-- The Galois group of `X⁵ − 5X + 12` is isomorphic to `D₅`.

A cyclic group of order 10 would contain an element of order 10. The embedding into `A₅`
would send it to an order-10 permutation of five points, which is impossible. Thus the
order-10 Galois group is non-cyclic and hence dihedral. -/
lemma gal_iso_d5 : Nonempty (f_d5.Gal ≃* DihedralGroup 5) := by
  obtain ⟨g', hg'⟩ := exists_gal_d5_embeds_alternating
  refine iso_dihedral_five_of_card_ten card_gal_d5 ?_
  intro hcyc
  obtain ⟨x, hx⟩ : ∃ x : f_d5.Gal, orderOf x = 10 := by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_gal_d5]⟩
  have hord : orderOf (g' x) = 10 := by rw [orderOf_injective g' hg' x, hx]
  refine perm_fin5_no_order_ten ((alternatingGroup (Fin 5)).subtype (g' x)) ?_
  rw [orderOf_injective (alternatingGroup (Fin 5)).subtype Subtype.coe_injective (g' x), hord]

end D5

namespace IsInverseGalois

/-- `D₅` is an inverse Galois group, realized as the Galois group of `X⁵ − 5X + 12`. -/
theorem dihedral_five : IsInverseGalois (DihedralGroup 5) := by
  obtain ⟨e⟩ := D5.gal_iso_d5
  exact ⟨f_d5.SplittingField, inferInstance, inferInstance, inferInstance,
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField,
      to_normal := SplittingField.instNormal f_d5 },
    ⟨e⟩⟩

end IsInverseGalois

end
