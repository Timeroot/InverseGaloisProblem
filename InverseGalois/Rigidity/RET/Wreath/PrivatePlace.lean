/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Wreath.PlaceLocal
import InverseGalois.Rigidity.RET.Wreath.ThetaSimple
import InverseGalois.Rigidity.RET.Wreath.ParamFinite

/-!
# Almost every translation gives every conjugate a place of its own

The conjugate radicands `∏ᵢ (Θ j + c - tᵢ)^{eᵢ}` are independent modulo `n`-th powers as soon as
each member of the family owns a place at which its radicand is visible and the radicands of all
the other members are invisible.  Such a place is found one conjugate at a time, and the search is
purely local: a member `Θ j` of the family is transcendental over the constants, so reading the
ambient field through it presents that field as a finite map to the line with coordinate `Θ j`, and
on such a map all but finitely many points of the line are met simply, that is, at a place where
the coordinate takes the corresponding value to order exactly one.

The place produced this way has to do two jobs, and only the first of them is about `Θ j`.  The
second is that the *other* conjugates must be units there, and by the ultrametric computation of
`PlaceLocal` this happens as soon as the finitely many differences `Θ j' - Θ j - (t l - t i)` are
units at the place.  Those differences do not involve the translation `c` at all: they are finitely
many nonzero functions — nonzero precisely because no two members of the family differ by a
constant — and a nonzero function has zeros and poles at only finitely many places.  So the places
to avoid can be fixed before the translation is chosen, and avoiding them costs only finitely many
further values of the coordinate.

Turning a value of the coordinate into a value of the translation is the substitution `α = tᵢ - c`,
which converts a finite set of forbidden values of `α` into a finite set of forbidden values of
`c`.  Collecting the exclusions over the finitely many members of the family and the finitely many
branch points leaves all but finitely many translations good, and for a good translation the two
order computations of `PlaceLocal` feed the abstract independence criterion of `RadicandIndep`
directly.

## Main results

* `Rigidity.RET.Wreath.LineMap.finite_ord_ne_zero` — a finite family of functions has zeros and
  poles at only finitely many places.
* `Rigidity.RET.Wreath.LineMap.finite_not_exists_ord_eq_one_avoiding` — all but finitely many
  points of the line are met simply away from the zeros and poles of a finite family.
* `Rigidity.RET.Wreath.LineMap.exists_finite_avoiding` — the same statement packaged as a finite
  set of forbidden values.
* `Rigidity.RET.Wreath.exists_private_valuation` — for all but finitely many translations, one
  member of a family owns a valuation seeing its own radicand and no other.
* `Rigidity.RET.Wreath.exists_indep_radicands` — for all but finitely many translations the
  conjugate radicands are independent modulo `n`-th powers.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Rigidity.RET.Wreath

open GeomAKLB

set_option synthInstance.maxHeartbeats 400000

namespace LineMap

/-- **A finite family of functions is a unit at all but finitely many places.**  Each member has
nonzero order at only finitely many places, and a finite union of finite sets is finite. -/
theorem finite_ord_ne_zero (L : LineMap) {ι : Type*} [Finite ι] (g : ι → L.M) :
    {Q : HeightOneSpectrum L.R | ∃ a, ord L.M Q (g a) ≠ 0}.Finite := by
  have h : ∀ a : ι, {Q : HeightOneSpectrum L.R | ord L.M Q (g a) ≠ 0}.Finite := fun a =>
    Filter.eventually_cofinite.mp (ord_finite (g a))
  refine (Set.finite_iUnion h).subset fun Q hQ => ?_
  obtain ⟨a, ha⟩ := hQ
  exact Set.mem_iUnion.mpr ⟨a, ha⟩

/-- **All but finitely many values of the coordinate are taken simply away from the zeros and poles
of a finite family.**  The family rules out only finitely many places, and only finitely many
values of the coordinate are taken simply nowhere outside a prescribed finite set of places. -/
theorem finite_not_exists_ord_eq_one_avoiding (L : LineMap) {ι : Type*} [Finite ι] (g : ι → L.M) :
    {α : k | ¬ ∃ Q : HeightOneSpectrum L.R, (∀ a, ord L.M Q (g a) = 0) ∧
      ord L.M Q (L.T - algebraMap k L.M α) = 1}.Finite := by
  classical
  refine (finite_not_exists_ord_eq_one_notMem L (finite_ord_ne_zero L g).toFinset).subset ?_
  intro α hα hex
  obtain ⟨Q, hQZ, hQ1⟩ := hex
  refine hα ⟨Q, fun a => ?_, hQ1⟩
  by_contra hne
  exact hQZ ((Set.Finite.mem_toFinset _).mpr ⟨a, hne⟩)

/-- **Outside a finite set of values the coordinate is met simply at a place where a prescribed
finite family is a unit.**  This is the previous finiteness statement read as an exclusion: the
forbidden values are exactly the ones for which no such place exists. -/
theorem exists_finite_avoiding (L : LineMap) {ι : Type*} [Finite ι] (g : ι → L.M) :
    ∃ B : Set k, B.Finite ∧ ∀ α ∉ B, ∃ Q : HeightOneSpectrum L.R,
      (∀ a, ord L.M Q (g a) = 0) ∧ ord L.M Q (L.T - algebraMap k L.M α) = 1 := by
  refine ⟨_, finite_not_exists_ord_eq_one_avoiding L g, fun α hα => ?_⟩
  simpa only [Set.mem_setOf_eq, not_not] using hα

end LineMap

/-- **All but finitely many translations give one member of the family a valuation of its own.**
Reading the covering field through the member `Θ j`, the branch point `tᵢ` is met simply by the
translate `Θ j + c` at some place, and that place may be chosen to avoid the finitely many zeros
and poles of the translation-free differences `Θ j' - Θ j - (t l - t i)`.  There the order of the
`j`-th radicand is the exponent `eᵢ`, while every other radicand is a unit. -/
theorem exists_private_valuation (L : LineMap) {ι : Type*} [Finite ι] (Θ : ι → L.M) (j : ι)
    (hT : L.T = Θ j) (hsep : ∀ j' : ι, j ≠ j' → ∀ a : k, Θ j' - Θ j - algebraMap k L.M a ≠ 0)
    {r : ℕ} (t : Fin r → k) (hinj : Function.Injective t) (e : Fin r → ℕ) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S, ∀ i : Fin r,
      Θ j + algebraMap k L.M c - algebraMap k L.M (t i) ≠ 0 ∧
      ∃ V : L.M → ℤ,
        (∀ x y : L.M, x ≠ 0 → y ≠ 0 → V (x * y) = V x + V y) ∧
        V (conjRadicand Θ t e c j) = (e i : ℤ) ∧
        ∀ j' : ι, j' ≠ j → V (conjRadicand Θ t e c j') = 0 := by
  classical
  obtain ⟨B, hBfin, hB⟩ := LineMap.exists_finite_avoiding L
    (fun p : ι × Fin r × Fin r =>
      Θ p.1 - Θ j - (algebraMap k L.M (t p.2.1) - algebraMap k L.M (t p.2.2)))
  refine ⟨⋃ i : Fin r, (fun α : k => t i - α) '' B,
    Set.finite_iUnion fun i => hBfin.image _, ?_⟩
  intro c hc i
  have hci : t i - c ∉ B := by
    intro hmem
    exact hc (Set.mem_iUnion.mpr ⟨i, ⟨t i - c, hmem, by ring⟩⟩)
  obtain ⟨Q, hQg, hQ1⟩ := hB _ hci
  have harg : L.T - algebraMap k L.M (t i - c)
      = Θ j + algebraMap k L.M c - algebraMap k L.M (t i) := by
    rw [hT, map_sub]
    ring
  rw [harg] at hQ1
  have hconst : ∀ a : k, a ≠ 0 → ord L.M Q (algebraMap k L.M a) = 0 := fun a ha =>
    LineMap.ord_algebraMap_const L Q ha
  refine ⟨?_, ord L.M Q, fun x y hx hy => ord_mul Q hx hy, ?_, ?_⟩
  · intro h0
    rw [h0, ord_zero] at hQ1
    omega
  · exact ord_conjRadicand_self hconst hinj hQ1
  · intro j' hj'
    refine ord_conjRadicand_other hQ1 fun l => ⟨?_, hQg (j', l, i)⟩
    have hs := hsep j' hj'.symm (t l - t i)
    rwa [map_sub] at hs

/-- **For all but finitely many translations the conjugate radicands are independent modulo `n`-th
powers.**  Each member of the family is transcendental, so it presents the ambient field as a
finite map to the line and, outside a finite set of translations, owns a place at which its own
radicand has order the exponent of the branch point met there and every other radicand is a unit.
Excluding the finitely many bad translations of every member at once, a monomial in the radicands
that is an `n`-th power is seen by those places as a system of divisibilities which, the exponents
having no common factor with `n`, forces `n` to divide every exponent of the monomial. -/
theorem exists_indep_radicands {F : Type} [Field F] [Algebra k F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (Θ : ι → F)
    (htr : ∀ j, Transcendental k (Θ j))
    (hfin : ∀ j, @FiniteDimensional (RatFunc k) F _ _
      (@Algebra.toModule _ _ _ _ ((paramHom (M := F) (Θ j) (htr j)).toAlgebra)))
    (hsep : ∀ j j' : ι, j ≠ j' → ∀ a : k, Θ j' - Θ j - algebraMap k F a ≠ 0)
    {r : ℕ} (t : Fin r → k) (hinj : Function.Injective t) (e : Fin r → ℕ)
    {n : ℕ} (hgcd : Nat.gcd n (Finset.univ.gcd e) = 1) :
    ∃ S : Set k, S.Finite ∧ ∀ c ∉ S,
      (∀ (j : ι) (i : Fin r), Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0) ∧
      ∀ (m : ι → ℤ) (y : F), y ≠ 0 →
        y ^ n = ∏ j, conjRadicand Θ t e c j ^ m j → ∀ j, (n : ℤ) ∣ m j := by
  classical
  have key : ∀ j : ι, ∃ S : Set k, S.Finite ∧ ∀ c ∉ S, ∀ i : Fin r,
      Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0 ∧
      ∃ V : F → ℤ,
        (∀ x y : F, x ≠ 0 → y ≠ 0 → V (x * y) = V x + V y) ∧
        V (conjRadicand Θ t e c j) = (e i : ℤ) ∧
        ∀ j' : ι, j' ≠ j → V (conjRadicand Θ t e c j') = 0 := fun j =>
    exists_private_valuation (LineMap.ofParam F (Θ j) (htr j) (hfin j)) Θ j
      (LineMap.ofParam_T F (Θ j) (htr j) (hfin j)) (hsep j) t hinj e
  choose S hSfin hS using key
  refine ⟨⋃ j, S j, Set.finite_iUnion hSfin, ?_⟩
  intro c hc
  have hcj : ∀ j, c ∉ S j := fun j hmem => hc (Set.mem_iUnion.mpr ⟨j, hmem⟩)
  have hne : ∀ (j : ι) (i : Fin r), Θ j + algebraMap k F c - algebraMap k F (t i) ≠ 0 :=
    fun j i => (hS j c (hcj j) i).1
  refine ⟨hne, ?_⟩
  choose V hVadd hVself hVother using fun (j : ι) (i : Fin r) => (hS j c (hcj j) i).2
  exact fun m y hy hpow j => indep_of_private_valuations Θ t e c hgcd hne V hVadd hVself
    (fun j j' hj' i => hVother j i j' hj') m y hy hpow j

end Rigidity.RET.Wreath
