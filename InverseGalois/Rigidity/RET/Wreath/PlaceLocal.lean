/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.RadicandIndep
import InverseGalois.Rigidity.RET.Genus.OrdUltra

/-!
# What a conjugate radicand looks like at a place private to one conjugate

Fix a place `Q` of a cover at which one translated conjugate `Θ j + c` meets one branch point `tᵢ₀`
simply, that is, at which `Θ j + c - tᵢ₀` has order exactly one.  Because the branch points are
distinct, the differences `tᵢ₀ - tᵢ` are nonzero constants and so are units at `Q`; the
ultrametric inequality then forces every other factor `Θ j + c - tᵢ` to be a unit at `Q`, and the
order of the whole radicand collapses to the single exponent `eᵢ₀`.

The same computation, applied to a different member `Θ j'` of the family, says that the `j'`-th
radicand is a unit at `Q` as soon as each difference `Θ j' - Θ j - (tⱼ - tᵢ₀)` is one.  That
condition does not mention the translation `c` at all, which is what makes it possible to arrange it
once and for all before choosing `c`: it excludes only the finitely many places at which one of
those finitely many nonzero functions has a zero or a pole.

Together the two computations produce, at a single place, exactly the pair of facts that certifies
independence of the conjugate radicands.

## Main results

* `Rigidity.RET.Wreath.ne_zero_of_ord_lt` — a sum with unequal orders is nonzero.
* `Rigidity.RET.Wreath.ord_shift_eq_zero` — a translated conjugate is a unit at the other branch
  points of the place where it meets one of them simply.
* `Rigidity.RET.Wreath.ord_conjRadicand_self` — the order of the radicand of that conjugate is the
  exponent of the branch point it meets.
* `Rigidity.RET.Wreath.ord_conjRadicand_other` — the radicands of the other conjugates are units
  there.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

variable {F : Type*} [Field F] [Algebra k F] {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Algebra R F] [IsFractionRing R F] {v : HeightOneSpectrum R}

omit [Algebra k F] in
/-- **A sum of two elements of unequal orders is nonzero.**  Were it zero the two would be
negatives of each other, and negation does not change the order. -/
theorem ne_zero_of_ord_lt {x y : F} (hlt : ord F v x < ord F v y) : x + y ≠ 0 := by
  intro h
  have hy : y = -x := by linear_combination h
  rw [hy, ord_neg] at hlt
  exact lt_irrefl _ hlt

variable {ι : Type*} {r : ℕ} {Θ : ι → F} {t : Fin r → k} {e : Fin r → ℕ} {c : k}

/-- **Away from the branch point it meets, a translated conjugate is a unit.**  The difference
between two factors is a nonzero constant, which is a unit, and a unit added to something of
positive order is again a unit. -/
theorem ord_shift_eq_zero (hconst : ∀ a : k, a ≠ 0 → ord F v (algebraMap k F a) = 0)
    {u : F} {i₀ i : Fin r} (hne : t i₀ ≠ t i)
    (h₀ : ord F v (u - algebraMap k F (t i₀)) = 1) :
    u - algebraMap k F (t i) ≠ 0 ∧ ord F v (u - algebraMap k F (t i)) = 0 := by
  have htne : t i₀ - t i ≠ 0 := sub_ne_zero.2 hne
  have hx0 : algebraMap k F (t i₀ - t i) ≠ 0 := fun hz =>
    htne ((algebraMap k F).injective (by rw [hz, map_zero]))
  have hxo : ord F v (algebraMap k F (t i₀ - t i)) = 0 := hconst _ htne
  have hlt : ord F v (algebraMap k F (t i₀ - t i)) < ord F v (u - algebraMap k F (t i₀)) := by
    rw [hxo, h₀]
    norm_num
  have hsum : algebraMap k F (t i₀ - t i) + (u - algebraMap k F (t i₀))
      = u - algebraMap k F (t i) := by
    rw [map_sub]
    ring
  refine ⟨hsum ▸ ne_zero_of_ord_lt hlt, ?_⟩
  rw [← hsum, ord_add_of_ord_lt hx0 hlt, hxo]

/-- **The radicand of the conjugate meeting a branch point has that point's exponent as its
order.** -/
theorem ord_conjRadicand_self (hconst : ∀ a : k, a ≠ 0 → ord F v (algebraMap k F a) = 0)
    (hinj : Function.Injective t) {j : ι} {i₀ : Fin r}
    (h₀ : ord F v (Θ j + algebraMap k F c - algebraMap k F (t i₀)) = 1) :
    ord F v (conjRadicand Θ t e c j) = e i₀ := by
  have hne : ∀ i, Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0 := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      intro hz
      rw [hz, ord_zero] at h₀
      exact absurd h₀ (by norm_num)
    · exact (ord_shift_eq_zero hconst (fun heq => hi (hinj heq).symm) h₀).1
  refine ord_eval₂_multiA_eq (algebraMap k F) t e _ v hne h₀ fun i hi => ?_
  exact (ord_shift_eq_zero hconst (fun heq => hi (hinj heq).symm) h₀).2

/-- **The radicands of the other conjugates are units at such a place.**  The difference between a
factor of another conjugate's radicand and the factor with the simple zero is one of the
translation-free functions `Θ j' - Θ j - (tⱼ - tᵢ₀)`, assumed to be a unit here. -/
theorem ord_conjRadicand_other {j j' : ι} {i₀ : Fin r}
    (h₀ : ord F v (Θ j + algebraMap k F c - algebraMap k F (t i₀)) = 1)
    (hF : ∀ l, Θ j' - Θ j - (algebraMap k F (t l) - algebraMap k F (t i₀)) ≠ 0 ∧
      ord F v (Θ j' - Θ j - (algebraMap k F (t l) - algebraMap k F (t i₀))) = 0) :
    ord F v (conjRadicand Θ t e c j') = 0 := by
  have key : ∀ l, Θ j' + algebraMap k F c - algebraMap k F (t l) ≠ 0 ∧
      ord F v (Θ j' + algebraMap k F c - algebraMap k F (t l)) = 0 := by
    intro l
    have hlt : ord F v (Θ j' - Θ j - (algebraMap k F (t l) - algebraMap k F (t i₀))) <
        ord F v (Θ j + algebraMap k F c - algebraMap k F (t i₀)) := by
      rw [(hF l).2, h₀]
      norm_num
    have hsum : Θ j' - Θ j - (algebraMap k F (t l) - algebraMap k F (t i₀)) +
        (Θ j + algebraMap k F c - algebraMap k F (t i₀)) =
        Θ j' + algebraMap k F c - algebraMap k F (t l) := by ring
    refine ⟨hsum ▸ ne_zero_of_ord_lt hlt, ?_⟩
    rw [← hsum, ord_add_of_ord_lt (hF l).1 hlt, (hF l).2]
  exact ord_eval₂_multiA_eq_zero (algebraMap k F) t e _ v (fun l => (key l).1) fun l => (key l).2

end Rigidity.RET.Wreath
