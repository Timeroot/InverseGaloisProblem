/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.GlobalClasses
import InverseGalois.CFT.PoitouTate.SUnitReduce
import InverseGalois.CFT.PoitouTate.UnramifiedPerp

/-!
# A unit ramified at one place and confined to a prescribed set of places

The divisor a prescription asks for at a named place is a unit of order prime to the exponent
there, of order divisible by the exponent at every other place except the ones of a prescribed
set.  Duality produces such a unit from nothing but a statement about the units it has to be tested
against: **a unit is ramified exactly at a named place, up to places of the prescribed set, as soon
as the only `S`-units unramified everywhere and locally trivial at the places of the set are
locally trivial at every place of `S` at all.**

The prescription answered is the one asking for a ramified class at the named place, asking nothing
at the places of the set and asking for an unramified class at the remaining places.  At a prime
exponent the complement of a condition of being unramified is contained in that condition at
**every** place, the places above the exponent included, so the units to test against are the ones
unramified away from the set, and the complement of the condition imposing nothing is the trivial
class, so at the places of the set those units are locally trivial.  Those are exactly the units the
hypothesis speaks about, and it says their whole class vanishes, which makes them pair trivially
with the prescription.

Two more sets of places may be prescribed at no cost.  At finitely many places the unit may be asked
for the trivial class outright, by naming the trivial condition there: its complement is everything,
so nothing whatever is asked of the units tested against at those places, and the divisibility they
are asked for elsewhere is simply not asked for there.  And at finitely many further places the unit
may be asked for an order divisible by the exponent, by naming the unramified condition there
instead of the trivial one, which costs the tested units the same divisibility.

The hypothesis is not a technicality but the whole arithmetic of the matter: the units it speaks
about are those whose exponent-th root generates an extension unramified everywhere and split at the
places of the set, so it asks that the places of the set detect that extension.  Nothing else is
needed, and nothing less will do.

## Main results

* `InverseGalois.CFT.exists_placeValue_not_dvd_of_forall_localClassHom_eq_one`: **a unit of order
  prime to the exponent at a named place, of trivial class at a prescribed set of places, of order
  divisible by the exponent at a second prescribed set and away from a third**, produced from the
  vanishing of the units the duality tests against.

## Tags

Selmer group, local conditions, unramified, norm residue symbol, Poitou-Tate duality,
class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Reachable

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- **A unit of a number field of order prime to the exponent at one named place, of trivial class
at a prescribed set of places, of order divisible by the exponent at a second prescribed set and at
every place outside a third.**

The prescription answered asks for a ramified class at the named place, nothing at the places of the
confining set, the trivial class at the places the unit must stay a local power at, and an
unramified class at the remaining places of the finite set the duality is run over — a set
containing every place above the exponent.  The units it has to be tested against are those which
are unramified away from the confining set and locally trivial at the places of it, the complement
of a condition of being unramified being contained in that condition at a prime exponent, the
complement of the condition imposing nothing being the trivial class, and the complement of the
trivial condition being everything; the hypothesis says those units have trivial class at every
place, so they pair trivially with anything the prescription names.

Outside the finite set the unit is a unit of that set and so has no order at all. -/
theorem exists_placeValue_not_dvd_of_forall_localClassHom_eq_one (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (Tz Xex Sp : Set (HeightOneSpectrum (𝓞 K))) (y₀ : Y) (hy₀Tz : ι y₀ ∉ Tz)
    (hy₀Xex : ι y₀ ∉ Xex)
    (hfree : ∀ u : ↥(sUnits K (Set.range ι)),
      (∀ w : InfinitePlace K, infClassHom w n ((u : Kˣ)) = 1) →
      (∀ y : Y, ι y ∉ Tz → (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) →
        (n : ℤ) ∣ placeValue (ι y) ((u : Kˣ))) →
      (∀ y : Y, ι y ∉ Tz → y ≠ y₀ → ι y ∈ Sp → ι y ∉ Xex →
        localClassHom (ι y) n ((u : Kˣ)) = 1) →
      ∀ y : Y, localClassHom (ι y) n ((u : Kˣ)) = 1) :
    ∃ a : Kˣ, ¬ (n : ℤ) ∣ placeValue (ι y₀) a ∧
      (∀ y : Y, ι y ∈ Tz → localClassHom (ι y) n a = 1) ∧
      (∀ y : Y, ι y ∈ Xex → (n : ℤ) ∣ placeValue (ι y) a) ∧
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
  obtain ⟨L, hL0, hL1, hL2⟩ : ∃ L : ∀ y : Y, Subgroup (localClasses (ι y) n),
      (∀ y : Y, ι y ∈ Tz → L y = ⊥) ∧
      (∀ y : Y, ι y ∉ Tz → (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) →
        L y = localUnramified (ι y) n) ∧
        ∀ y : Y, ι y ∉ Tz → ¬ (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) → L y = ⊤ :=
    ⟨fun y => if ι y ∈ Tz then ⊥
        else if y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex then localUnramified (ι y) n else ⊤,
      fun _ hy => if_pos hy, fun _ hy hy' => (if_neg hy).trans (if_pos hy'),
      fun _ hy hy' => (if_neg hy).trans (if_neg hy')⟩
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
    have hunr : ∀ y : Y, ι y ∉ Tz → (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) →
        (n : ℤ) ∣ placeValue (ι y) ((u : Kˣ)) := by
      intro y hyTz hy
      refine (localClassHom_mem_localUnramified_iff (ι y) _).1 ?_
      have h := hby y
      rw [hL1 y hyTz hy] at h
      exact perpSubgroupLeft_localUnramified_le hres hζ hn (ι y) h
    have hone : ∀ y : Y, ι y ∉ Tz → y ≠ y₀ → ι y ∈ Sp → ι y ∉ Xex →
        localClassHom (ι y) n ((u : Kˣ)) = 1 := by
      intro y hyTz hy hyS hyX
      have h := hby y
      rw [hL2 y hyTz (by push_neg; exact ⟨hy, hyS, hyX⟩),
        perpSubgroupLeft_localClassPairing_top hres hζ (ι y)] at h
      exact Subgroup.mem_bot.1 h
    have hall := hfree u huinf hunr hone
    have h1 : sUnitClassHom ι n u = 1 := funext fun y => hall y
    simp only [h1, _root_.map_one, MonoidHom.one_apply]
  obtain ⟨a, ha, l, hl, hal⟩ :=
    exists_sUnitClass_mul_eq hn hres hζ hinj hnι hrepr L (c := c) hpair
  obtain ⟨g, rfl⟩ := ha
  have hlmem : ∀ y : Y, ι y ∉ Tz → (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) →
      l y ∈ localUnramified (ι y) n := by
    intro y hyTz hy
    rw [← hL1 y hyTz hy]
    exact (Subgroup.mem_pi _).1 hl y (Set.mem_univ y)
  have hgone : ∀ y : Y, ι y ∈ Tz → sUnitClassHom ι n g y = 1 := by
    intro y hy
    have hyne : y ≠ y₀ := fun h => hy₀Tz (h ▸ hy)
    have hl1 : l y = (1 : localClasses (ι y) n) := by
      have h := (Subgroup.mem_pi _).1 hl y (Set.mem_univ y)
      rw [hL0 y hy] at h
      exact Subgroup.mem_bot.1 h
    have h : sUnitClassHom ι n g y * l y = 1 := by
      have h' := congrFun hal y
      rwa [hcne y hyne] at h'
    rw [hl1] at h
    exact (mul_one _).symm.trans h
  have hgoneu : ∀ y : Y, ι y ∈ Tz → localClassHom (ι y) n ((g : Kˣ)) = 1 := by
    intro y hy
    rw [show localClassHom (ι y) n ((g : Kˣ)) = sUnitClassHom ι n g y from rfl]
    exact hgone y hy
  have hgunr : ∀ y : Y, y ≠ y₀ → ι y ∉ Tz → (y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex) →
      localClassHom (ι y) n ((g : Kˣ)) ∈ localUnramified (ι y) n := by
    intro y hyne hyTz hy
    have h := congrFun hal y
    rw [hcne y hyne] at h
    have hgy : sUnitClassHom ι n g y = (l y)⁻¹ := eq_inv_iff_mul_eq_one.2 h
    rw [show localClassHom (ι y) n ((g : Kˣ)) = sUnitClassHom ι n g y from rfl, hgy]
    exact Subgroup.inv_mem _ (hlmem y hyTz hy)
  refine ⟨(g : Kˣ), fun hdvd => ?_, hgoneu, fun y hy => ?_, fun v hv hdvd => ?_⟩
  · have hgu : sUnitClassHom ι n g y₀ ∈ localUnramified (ι y₀) n :=
      (localClassHom_mem_localUnramified_iff (ι y₀) _).2 hdvd
    have hcwmem : cw ∈ localUnramified (ι y₀) n := by
      rw [← hcy₀, ← congrFun hal y₀]
      exact Subgroup.mul_mem _ hgu (hlmem y₀ hy₀Tz (Or.inl rfl))
    have h1 : Multiplicative.ofAdd (1 : ZMod n) = 1 := by
      rw [← hcw]
      exact MonoidHom.mem_ker.1 hcwmem
    exact one_ne_zero (ofAdd_eq_one.1 h1)
  · refine (localClassHom_mem_localUnramified_iff (ι y) _).1 ?_
    by_cases hyTz : ι y ∈ Tz
    · rw [hgoneu y hyTz]
      exact one_mem _
    · exact hgunr y (fun h => hy₀Xex (h ▸ hy)) hyTz (Or.inr (Or.inr hy))
  · by_cases hvr : v ∈ Set.range ι
    · obtain ⟨y, rfl⟩ := hvr
      have hyne : y ≠ y₀ := fun h => hv (by rw [h])
      by_cases hyTz : ι y ∈ Tz
      · refine absurd ?_ hdvd
        refine (localClassHom_mem_localUnramified_iff (ι y) _).1 ?_
        rw [hgoneu y hyTz]
        exact one_mem _
      · by_cases hy : y = y₀ ∨ ι y ∉ Sp ∨ ι y ∈ Xex
        · refine absurd ?_ hdvd
          exact (localClassHom_mem_localUnramified_iff (ι y) _).1 (hgunr y hyne hyTz hy)
        · push_neg at hy
          exact hy.2.1
    · refine absurd ?_ hdvd
      rw [placeValue_eq_zero_of_mem_sUnits g.2 hvr]
      exact dvd_zero _

end Reachable

end InverseGalois.CFT
