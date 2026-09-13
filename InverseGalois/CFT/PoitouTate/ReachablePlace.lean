/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.PoitouTate.UnramifiedOdd

/-!
# A unit ramified at one place and confined to a prescribed set of places

The divisor a prescription asks for at a named place is a unit of order prime to the exponent
there, of order divisible by the exponent at every other place except the ones of a prescribed
set.  Duality produces such a unit from nothing but a statement about the units it has to be tested
against: **a unit is ramified exactly at a named place, up to places of the prescribed set, as soon
as the only `S`-units unramified everywhere and locally trivial at the places of the set are
locally trivial at every place of `S` at all.**

The prescription answered is the one asking for a ramified class at the named place, asking nothing
at the places of the set and asking for an unramified class at the remaining places.  At an odd
prime exponent the complement of a condition of being unramified is contained in that condition at
**every** place, the places above the exponent included, so the units to test against are the ones
unramified away from the set, and the complement of the condition imposing nothing is the trivial
class, so at the places of the set those units are locally trivial.  Those are exactly the units the
hypothesis speaks about, and it says their whole class vanishes, which makes them pair trivially
with the prescription.

The hypothesis is not a technicality but the whole arithmetic of the matter: the units it speaks
about are those whose exponent-th root generates an extension unramified everywhere and split at the
places of the set, so it asks that the places of the set detect that extension.  Nothing else is
needed, and nothing less will do.

## Main results

* `InverseGalois.CFT.exists_placeValue_not_dvd_of_forall_localClassHom_eq_one`: **a unit of order
  prime to the exponent at a named place and of order divisible by it away from a prescribed set of
  places**, produced from the vanishing of the units the duality tests against.

## Tags

Selmer group, local conditions, unramified, norm residue symbol, Poitou-Tate duality,
class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Reachable

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- **A unit of a number field of order prime to the exponent at one named place and of order
divisible by the exponent at every place outside a prescribed set.**

The prescription answered asks for a ramified class at the named place, nothing at the places of the
prescribed set, and an unramified class at the remaining places of the finite set the duality is run
over — a set containing every place above the exponent.  The units it has to be tested against are
those which are unramified away from the prescribed set and locally trivial at the places of it, the
complement of a condition of being unramified being contained in that condition at an odd prime
exponent and the complement of the condition imposing nothing being the trivial class; the
hypothesis says those units have trivial class at every place, so they pair trivially with anything
the prescription names.

Outside the finite set the unit is a unit of that set and so has no order at all. -/
theorem exists_placeValue_not_dvd_of_forall_localClassHom_eq_one (hn : n.Prime) (hodd : Odd n)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (Sp : Set (HeightOneSpectrum (𝓞 K))) (y₀ : Y)
    (hfree : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      (∀ y : Y, ι y ∉ Sp → (n : ℤ) ∣ placeValue (ι y) ((u : Kˣ))) →
      (n : ℤ) ∣ placeValue (ι y₀) ((u : Kˣ)) →
      (∀ y : Y, y ≠ y₀ → ι y ∈ Sp → localClassHom (ι y) n ((u : Kˣ)) = 1) →
      ∀ y : Y, localClassHom (ι y) n ((u : Kˣ)) = 1) :
    ∃ a : Kˣ, ¬ (n : ℤ) ∣ placeValue (ι y₀) a ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ≠ ι y₀ → ¬ (n : ℤ) ∣ placeValue v a → v ∈ Sp := by
  classical
  haveI : Fact (1 < n) := ⟨hn.one_lt⟩
  obtain ⟨cw, hcw⟩ := surjective_unitValModQuot
    (isUnitValGen_one (valued_adicCompletion_surjective (ι y₀)))
    (Multiplicative.ofAdd (1 : ZMod n))
  obtain ⟨c, hcy₀, hcne⟩ :
      ∃ c : (y : Y) → localClasses (ι y) n, c y₀ = cw ∧ ∀ y : Y, y ≠ y₀ → c y = 1 :=
    ⟨Function.update (fun _ => 1) y₀ cw, Function.update_self _ _ _,
      fun y hy => Function.update_of_ne hy _ _⟩
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ∀ y : Y, Subgroup (localClasses (ι y) n),
      (∀ y : Y, (y = y₀ ∨ ι y ∉ Sp) → L y = localUnramified (ι y) n) ∧
        ∀ y : Y, ¬ (y = y₀ ∨ ι y ∉ Sp) → L y = ⊤ :=
    ⟨fun y => if y = y₀ ∨ ι y ∉ Sp then localUnramified (ι y) n else ⊤,
      fun _ hy => if_pos hy, fun _ hy => if_neg hy⟩
  have hpair : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      sUnitClassHom ι n u ∈ Subgroup.pi Set.univ
        (fun y => perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y)) →
      localSymbolPiPairing hres hζ ι (sUnitClassHom ι n u) c = 1 := by
    intro u huinf hb
    have hby : ∀ y : Y, sUnitClassHom ι n u y
        ∈ perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y) :=
      fun y => (Subgroup.mem_pi _).1 hb y (Set.mem_univ y)
    have hunr : ∀ y : Y, (y = y₀ ∨ ι y ∉ Sp) → (n : ℤ) ∣ placeValue (ι y) ((u : Kˣ)) := by
      intro y hy
      refine (localClassHom_mem_localUnramified_iff (ι y) _).1 ?_
      have h := hby y
      rw [hL1 y hy] at h
      exact perpSubgroupLeft_localUnramified_le_of_odd hres hζ hn hodd (ι y) h
    have hone : ∀ y : Y, y ≠ y₀ → ι y ∈ Sp → localClassHom (ι y) n ((u : Kˣ)) = 1 := by
      intro y hy hyS
      have h := hby y
      rw [hL2 y (by push_neg; exact ⟨hy, hyS⟩),
        perpSubgroupLeft_localClassPairing_top hres hζ (ι y)] at h
      exact Subgroup.mem_bot.1 h
    have hall := hfree u huinf (fun y hy => hunr y (Or.inr hy)) (hunr y₀ (Or.inl rfl)) hone
    have h1 : sUnitClassHom ι n u = 1 := funext fun y => hall y
    simp only [h1, _root_.map_one, MonoidHom.one_apply]
  obtain ⟨a, ha, l, hl, hal⟩ :=
    exists_sUnitClass_mul_eq hn hres hζ hinj hnι hrepr L (c := c) hpair
  obtain ⟨g, rfl⟩ := ha
  have hlmem : ∀ y : Y, (y = y₀ ∨ ι y ∉ Sp) → l y ∈ localUnramified (ι y) n := by
    intro y hy
    rw [← hL1 y hy]
    exact (Subgroup.mem_pi _).1 hl y (Set.mem_univ y)
  refine ⟨(g : Kˣ), fun hdvd => ?_, fun v hv hdvd => ?_⟩
  · have hgunr : sUnitClassHom ι n g y₀ ∈ localUnramified (ι y₀) n :=
      (localClassHom_mem_localUnramified_iff (ι y₀) _).2 hdvd
    have hcwmem : cw ∈ localUnramified (ι y₀) n := by
      rw [← hcy₀, ← congrFun hal y₀]
      exact Subgroup.mul_mem _ hgunr (hlmem y₀ (Or.inl rfl))
    have h1 : Multiplicative.ofAdd (1 : ZMod n) = 1 := by
      rw [← hcw]
      exact MonoidHom.mem_ker.1 hcwmem
    exact one_ne_zero (ofAdd_eq_one.1 h1)
  · by_cases hvr : v ∈ Set.range ι
    · obtain ⟨y, rfl⟩ := hvr
      by_cases hy : y = y₀ ∨ ι y ∉ Sp
      · refine absurd ?_ hdvd
        refine (localClassHom_mem_localUnramified_iff (ι y) _).1 ?_
        have hyne : y ≠ y₀ := fun h => hv (by rw [h])
        have hyy : sUnitClassHom ι n g y * l y = 1 := by
          have h := congrFun hal y
          rw [hcne y hyne] at h
          exact h
        have hgy : sUnitClassHom ι n g y = (l y)⁻¹ := eq_inv_iff_mul_eq_one.2 hyy
        rw [show localClassHom (ι y) n ((g : Kˣ)) = sUnitClassHom ι n g y from rfl, hgy]
        exact Subgroup.inv_mem _ (hlmem y hy)
      · push_neg at hy
        exact hy.2
    · refine absurd ?_ hdvd
      rw [placeValue_eq_zero_of_mem_sUnits g.2 hvr]
      exact dvd_zero _

end Reachable

end InverseGalois.CFT
