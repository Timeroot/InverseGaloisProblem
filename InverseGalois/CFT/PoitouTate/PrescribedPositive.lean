/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.Prescribed

/-!
# Global classes prescribed at the finite places and trivial at the infinite ones

The self-duality of the classes of the `S`-units holds inside the local classes at the finite
places of `S` **together with the infinite places**, so the infinite places may be prescribed along
with the finite ones.  Asking for the trivial class at every infinite place is the opposite of
asking nothing there: the condition imposing nothing is dual to the condition imposing everything,
and the condition imposing everything — the trivial subgroup of admissible errors — is dual to the
condition imposing nothing on the `S`-units one tests against.

So the price of an `S`-unit which is a local power at every infinite place is that the assignment
of finite classes must pair trivially with **every** `S`-unit obeying the dual conditions at the
finite places, and not merely with those which happen to be local powers at infinity.

## Main results

* `InverseGalois.CFT.exists_sUnitClass_mul_eq_pos`: **an assignment of local classes orthogonal to
  the `S`-units obeying the dual conditions is congruent modulo the conditions to the class of an
  `S`-unit which is a local power at every infinite place.**
* `InverseGalois.CFT.exists_sUnitClass_mul_eq_unramified_pos`: the same for conditions which at
  each place either prescribe the class exactly or prescribe it up to an unramified class.

## Tags

Selmer group, local conditions, infinite place, totally positive, Poitou-Tate duality,
class field theory
-/

namespace InverseGalois.CFT

open IsDedekindDomain NumberField

section Positive

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  {P E : HeightOneSpectrum (𝓞 K) → ℕ} {Y : Type*} [Fintype Y]

/-- **An assignment of local classes orthogonal to the `S`-units obeying the dual conditions is
congruent modulo the conditions to the class of an `S`-unit which is a local power at every
infinite place.**  The classes of the `S`-units are their own orthogonal complement inside the
local classes at the places of `S` together with the infinite places; prescribing the trivial class
at each infinite place leaves no room at infinity, so the `S`-units to test against are all of
those obeying the dual conditions at the finite places. -/
theorem exists_sUnitClass_mul_eq_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (L : ∀ y : Y, Subgroup (localClasses (ι y) n))
    {c : (y : Y) → localClasses (ι y) n}
    (hc : ∀ u : ↥(sUnits K (Set.range ι)),
      sUnitClassHom ι n u ∈ Subgroup.pi Set.univ
        (fun y => perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y)) →
      localSymbolPiPairing hres hζ ι (sUnitClassHom ι n u) c = 1) :
    ∃ g : ↥(sUnits K (Set.range ι)), (∀ w : InfinitePlace K, infClassHom w n ((g : Kˣ)) = 1) ∧
      ∃ l ∈ Subgroup.pi Set.univ L, sUnitClassHom ι n g * l = c := by
  classical
  haveI : ∀ y : Y, Finite (localClasses (ι y) n) := fun y => finite_localClasses (ι y)
  haveI : Finite ((y : Y) → localClasses (ι y) n) := Pi.finite
  haveI : ∀ w : InfinitePlace K, Finite (infClasses w n) :=
    fun w => finite_infClasses w (NeZero.ne n)
  haveI : Finite ((w : InfinitePlace K) → infClasses w n) := Pi.finite
  haveI : Finite (((y : Y) → localClasses (ι y) n) ×
    ((w : InfinitePlace K) → infClasses w n)) := inferInstance
  have hflipinf : Function.Injective (infSymbolPiPairing K n).flip :=
    injective_flip_infSymbolPiPairing K (NeZero.ne n)
  have hflip : Function.Injective (fullPairing hres hζ ι).flip := by
    rw [fullPairing]
    exact injective_flip_prodPairing
      (injective_flip_piPairing fun y => injective_flip_localSymbolQuotDual _ _ _) hflipinf
  have hperp : perpSubgroupLeft (A := ((y : Y) → localClasses (ι y) n) ×
          ((w : InfinitePlace K) → infClasses w n)) (fullPairing hres hζ ι)
        ((Subgroup.pi Set.univ L).prod (⊥ : Subgroup ((w : InfinitePlace K) → infClasses w n)))
      = (Subgroup.pi Set.univ fun y => perpSubgroupLeft (A := localClasses (ι y) n)
          (localClassPairing hres hζ (ι y)) (L y)).prod ⊤ := by
    rw [fullPairing, perpSubgroupLeft_prodPairing_prod, perpSubgroupLeft_bot,
      localSymbolPiPairing_eq_piPairing, perpSubgroupLeft_piPairing_pi]
  have hmain : ∃ x ∈ selmerGroupFull ι n, ∃ z ∈ (Subgroup.pi Set.univ L).prod
      (⊥ : Subgroup ((w : InfinitePlace K) → infClasses w n)),
      x * z = ((c, 1) : ((y : Y) → localClasses (ι y) n) ×
        ((w : InfinitePlace K) → infClasses w n)) := by
    refine exists_mul_eq_of_forall_pairing_eq_one hflip
      (perpSubgroup_selmerGroupFull hn hres hζ hinj hnι hrepr) fun b hb => ?_
    rw [hperp] at hb
    obtain ⟨hbS, hbP⟩ := Subgroup.mem_inf.1 hb
    obtain ⟨u, rfl⟩ := hbS
    rw [fullPairing, prodPairing_apply, _root_.map_one, mul_one]
    exact hc u (Subgroup.mem_prod.1 hbP).1
  obtain ⟨x, hx, z, hz, hxz⟩ := hmain
  obtain ⟨g, rfl⟩ := hx
  have hz2 : z.2 = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hz).2
  have hx2 : (fullClassHom ι n g).2 = 1 := by
    have h := congrArg Prod.snd hxz
    simp only [Prod.snd_mul, hz2] at h
    exact (mul_one _).symm.trans h
  exact ⟨g, fun w => congrFun hx2 w, z.1, (Subgroup.mem_prod.1 hz).1, congrArg Prod.fst hxz⟩

/-- **An assignment of local classes prescribed exactly at some places and up to an unramified
class at the others is met by the class of an `S`-unit which is a local power at every infinite
place**, as soon as it is orthogonal to every `S`-unit unramified at the places of the second
kind. -/
theorem exists_sUnitClass_mul_eq_unramified_pos (hn : n.Prime)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (P v) (E v))
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) {ι : Y → HeightOneSpectrum (𝓞 K)}
    (hinj : Function.Injective ι)
    (hnι : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((n : ℕ) : K) ≠ 1 → v ∈ Set.range ι)
    (hrepr : ∀ m : HeightOneSpectrum (𝓞 K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, m v = 0) →
      ∃ a : Kˣ, ∀ v ∉ Set.range ι, Rigidity.RET.ord K v (a : K) = m v)
    (L D : ∀ y : Y, Subgroup (localClasses (ι y) n))
    (hLD : ∀ y : Y, (L y = ⊥ ∧ D y = ⊤) ∨
      (FinitePlace.mk (ι y) ((n : ℕ) : K) = 1 ∧ L y = localUnramified (ι y) n ∧
        D y = localUnramified (ι y) n))
    {c : (y : Y) → localClasses (ι y) n}
    (hc : ∀ u : ↥(sUnits K (Set.range ι)),
      sUnitClassHom ι n u ∈ Subgroup.pi Set.univ D →
      localSymbolPiPairing hres hζ ι (sUnitClassHom ι n u) c = 1) :
    ∃ g : ↥(sUnits K (Set.range ι)), (∀ w : InfinitePlace K, infClassHom w n ((g : Kˣ)) = 1) ∧
      ∃ l ∈ Subgroup.pi Set.univ L, sUnitClassHom ι n g * l = c := by
  refine exists_sUnitClass_mul_eq_pos hn hres hζ hinj hnι hrepr L fun u hb => hc u ?_
  refine (Subgroup.mem_pi _).2 fun y _ => ?_
  have h := (Subgroup.mem_pi _).1 hb y (Set.mem_univ y)
  rcases hLD y with ⟨hL, hD⟩ | ⟨hv, hL, hD⟩
  · rw [hD]
    exact Subgroup.mem_top _
  · rw [hL, perpSubgroupLeft_localUnramified hres hζ hn hv] at h
    rwa [hD]

end Positive

end InverseGalois.CFT
