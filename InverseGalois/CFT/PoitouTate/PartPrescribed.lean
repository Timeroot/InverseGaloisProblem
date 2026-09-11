/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Prescribed

/-!
# A prescription made at part of the places of a set and left free at the rest

Prescribing the class of an `S`-unit at every place of `S` at once is more than the reciprocity law
allows: the classes of the `S`-units are their own orthogonal complement, so a prescription is met
exactly when it is orthogonal to all of them.  Leaving the class free at some of the places is a
weaker demand, and the condition weakens with it: the local condition imposing everything at a
place is dual to the condition imposing nothing, so the `S`-units to test a prescription against
are only those whose class is trivial at every place where the prescription is not made.

That turns the reciprocity obstruction into a statement about how well the free places see the
`S`-units.  If the only `S`-units trivial at every free place and at every infinite place are also
trivial at every place carrying the prescription, then each factor of the product of symbols has a
trivial argument, and the prescription is met with no condition on it at all: **the places where
the prescription is not made detect the `S`-units, and an arbitrary prescription at the remaining
places is the class of an `S`-unit.**

## Main statements

* `InverseGalois.CFT.localSymbolPiPairing_eq_one_of_forall`: a product of symbols in which every
  factor has a trivial argument is trivial.
* `InverseGalois.CFT.exists_sUnit_forall_mem_localClassHom_eq`: **a prescription made at part of
  the places of `S` and orthogonal to the `S`-units trivial at the remaining places is met there by
  the class of an `S`-unit.**
* `InverseGalois.CFT.exists_sUnit_forall_localClassHom_eq_of_detecting`: **a prescription supported
  at places the remaining ones detect the `S`-units at is met by the class of an `S`-unit**, with no
  orthogonality left to check.

## Tags

Selmer group, local conditions, norm residue symbol, Poitou-Tate duality, class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section PartPrescribed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- A product of norm residue symbols in which every factor has a trivial argument is trivial. -/
theorem localSymbolPiPairing_eq_one_of_forall
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (ι : Y → HeightOneSpectrum (𝓞 K))
    {a c : (y : Y) → localClasses (ι y) n} (h : ∀ y : Y, a y = 1 ∨ c y = 1) :
    localSymbolPiPairing hres hζ ι a c = 1 := by
  rw [localSymbolPiPairing_eq_piPairing, piPairing_apply]
  refine Finset.prod_eq_one fun y _ => ?_
  rcases h y with hy | hy
  · rw [hy, _root_.map_one, MonoidHom.one_apply]
  · rw [hy, _root_.map_one]

/-- The classes at a finite place of a number field inject into their own character group under the
norm residue symbol. -/
theorem injective_localClassPairing
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (localClassPairing hres hζ v) :=
  injective_localSymbolQuotDual (hres v) (isUnitValGen_one (valued_adicCompletion_surjective v))
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective)

/-- **A prescription made at part of the places of `S` is met there by the class of an `S`-unit**,
as soon as it is orthogonal to those `S`-units which are a local power at every infinite place and
whose class is trivial at each of the remaining places.  Nothing is asked at those places, and the
local condition imposing nothing is dual to the one imposing everything. -/
theorem exists_sUnit_forall_mem_localClassHom_eq (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (Ts : Set Y) (c : (y : Y) → localClasses (ι y) n)
    (hc : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      (∀ y ∉ Ts, localClassHom (ι y) n ((u : Kˣ)) = 1) →
      localSymbolPiPairing hres hζ ι (sUnitClassHom ι n u) c = 1) :
    ∃ g : ↥(sUnits K (Set.range ι)), ∀ y ∈ Ts, localClassHom (ι y) n ((g : Kˣ)) = c y := by
  classical
  set L : ∀ y : Y, Subgroup (localClasses (ι y) n) := fun y => if y ∈ Ts then ⊥ else ⊤ with hLdef
  have hLbot : ∀ y ∈ Ts, L y = ⊥ := fun y hy => by rw [hLdef]; exact if_pos hy
  have hLtop : ∀ y ∉ Ts, L y = ⊤ := fun y hy => by rw [hLdef]; exact if_neg hy
  have hcL : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      sUnitClassHom ι n u ∈ Subgroup.pi Set.univ
        (fun y => perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y)) →
      localSymbolPiPairing hres hζ ι (sUnitClassHom ι n u) c = 1 := by
    intro u huinf hperp
    refine hc u huinf fun y hy => ?_
    have hmem := (Subgroup.mem_pi _).1 hperp y (Set.mem_univ y)
    rw [hLtop y hy, perpSubgroupLeft_top (injective_localClassPairing hres hζ (ι y))] at hmem
    exact Subgroup.mem_bot.1 hmem
  obtain ⟨a, ha, l, hl, hal⟩ := exists_sUnitClass_mul_eq hn hres hζ hinj hnι hrepr L hcL
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, fun y hy => ?_⟩
  have hly : l y = 1 := by
    have hmem := (Subgroup.mem_pi _).1 hl y (Set.mem_univ y)
    rw [hLbot y hy] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hy2 : sUnitClassHom ι n g y * l y = c y := congrFun hal y
  rw [hly] at hy2
  exact (mul_one (sUnitClassHom ι n g y)).symm.trans hy2

/-- **A prescription supported at places which the remaining places of `S` detect the `S`-units at
is met by the class of an `S`-unit**, with no orthogonality left to check.

The prescription is tested against the `S`-units whose class is trivial at every place where it is
not made.  When those places already force the class to be trivial at every place carrying the
prescription, each factor of the product of symbols has a trivial argument: either the class of the
`S`-unit there, or the prescription itself. -/
theorem exists_sUnit_forall_localClassHom_eq_of_detecting (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (Ts Tp : Set Y) (c : (y : Y) → localClasses (ι y) n)
    (hcTs : ∀ y ∈ Ts, y ∉ Tp → c y = 1)
    (hdet : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      (∀ y ∉ Ts, localClassHom (ι y) n ((u : Kˣ)) = 1) →
      ∀ y ∈ Tp, localClassHom (ι y) n ((u : Kˣ)) = 1) :
    ∃ g : ↥(sUnits K (Set.range ι)), ∀ y ∈ Ts, localClassHom (ι y) n ((g : Kˣ)) = c y := by
  refine exists_sUnit_forall_mem_localClassHom_eq hn hres hζ hinj hnι hrepr Ts c
    fun u huinf hu => localSymbolPiPairing_eq_one_of_forall hres hζ ι fun y => ?_
  by_cases hy : y ∈ Tp
  · exact Or.inl (hdet u huinf hu y hy)
  · by_cases hys : y ∈ Ts
    · exact Or.inr (hcTs y hys hy)
    · exact Or.inl (hu y hys)

end PartPrescribed

end InverseGalois.CFT
