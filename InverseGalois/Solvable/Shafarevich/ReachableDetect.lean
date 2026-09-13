/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.ReachablePlace
import InverseGalois.CFT.Units.ClassSet
import InverseGalois.CFT.Units.StablePlaces
import InverseGalois.Solvable.Shafarevich.FlatPlaces

/-!
# Places detecting the powers make every place reachable

A place of a finite level is reached when a unit of the level has order prime to the exponent
there and order divisible by the exponent at every place except the ones sitting under a completely
decomposed place of the level.  Duality produces such a unit as soon as the units it has to be
tested against are trivial, and those are the units which are unramified everywhere — of order
divisible by the exponent at every place at once — and locally a power at the places the duality
imposes nothing at.

So the whole arithmetic of reachability is a detection statement: it is enough to exhibit finitely
many places, sitting under completely decomposed places of the level and away from the one being
asked for, at which being a local power already forces a unit unramified everywhere to be a power
of the level itself.  The units the duality tests against are then powers, and a power has trivial
class at every place at once, which is exactly what the duality asks of them.

The finite set of places the duality is run over is assembled from four pieces: the detecting
places and the place being asked for, which the prescription names, and the places carrying the
exponent together with a system of representatives of the ideal classes, which the duality needs in
order to realise a prescribed system of orders.  The last two are harmless, because away from the
detecting places and the named one the unit produced is only ever asked to be of order divisible by
the exponent, and a power is.

## Main results

* `InverseGalois.Shafarevich.isReachablePlace_of_detecting`: **a place of a finite level is reached
  once finitely many places sitting under completely decomposed places of the level detect the
  powers.**

## Tags

Shafarevich's theorem, place, completely decomposed, Poitou-Tate duality, Kummer theory,
class group
-/

namespace InverseGalois.Shafarevich

open InverseGalois.CFT IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### Detecting the powers at the decomposed places -/

section Detect

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **A place of a finite level is reached once finitely many places sitting under completely
decomposed places of that level detect the powers.**

The detecting places are asked to sit under completely decomposed places of the level and to avoid
the place being asked for; what they have to detect is that a unit of order divisible by the
exponent at every place, and a local power at each of them, is a power of the level.  The duality
is then run over those places together with the named one, the places carrying the exponent and a
system of representatives of the ideal classes, and the units it tests against are exactly the ones
the detection hypothesis speaks about, so they are powers and have trivial class everywhere. -/
theorem isReachablePlace_of_detecting {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    {K : IntermediateField k Ω} [NumberField ↥K] {E : IntermediateField k Ω}
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (w : HeightOneSpectrum (𝓞 ↥K))
    (X₀ : Finset (HeightOneSpectrum (𝓞 ↥K))) (hX₀w : w ∉ X₀)
    (hX₀split : ∀ v ∈ X₀, ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      Ideal.under (𝓞 ↥K) P = v.asIdeal → stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup)
    (hdet : ∀ u : (↥K)ˣ, (∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ placeValue v u) →
      (∀ v ∈ X₀, localClassHom v ℓ (u : (↥K)ˣ) = 1) → ∃ z : (↥K)ˣ, u = z ^ ℓ) :
    IsReachablePlace ℓ K E w := by
  classical
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hex : ∀ v : HeightOneSpectrum (𝓞 ↥K),
      ∃ p e : ℕ, HasResidueChar (v.adicCompletion ↥K) p e :=
    fun v => exists_hasResidueChar_adicCompletion v
  choose Pc Ec hres using hex
  obtain ⟨T, hTfin, hTrepr⟩ := exists_finite_ord_repr ↥K
  have hℓfin : {v : HeightOneSpectrum (𝓞 ↥K) | FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1}.Finite :=
    finite_setOf_finitePlace_natCast_ne_one hℓ.ne_zero
  obtain ⟨Sp, hSp⟩ : ∃ Sp : Set (HeightOneSpectrum (𝓞 ↥K)), ∀ v, v ∈ Sp ↔
      ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
        stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup :=
    ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Finset (HeightOneSpectrum (𝓞 ↥K)), ∀ v, v ∈ X ↔
      (v = w ∨ v ∈ X₀ ∨ v ∈ T ∨ FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1) :=
    ⟨insert w (X₀ ∪ (hTfin.toFinset ∪ hℓfin.toFinset)), fun v => by
      simp only [Finset.mem_insert, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hwX : w ∈ X := (hX w).2 (Or.inl rfl)
  have hrange : Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) = ↑X := Subtype.range_coe
  have hnι : ∀ v : HeightOneSpectrum (𝓞 ↥K), FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1 →
      v ∈ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) := by
    intro v hv
    rw [hrange]
    exact (hX v).2 (Or.inr (Or.inr (Or.inr hv)))
  have hrepr : ∀ m : HeightOneSpectrum (𝓞 ↥K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 ↥K) in Filter.cofinite, m v = 0) →
      ∃ a : (↥K)ˣ, ∀ v ∉ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)),
        Rigidity.RET.ord ↥K v (a : ↥K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hTrepr m hm
    refine ⟨a, fun v hv => ha v fun hvT => hv ?_⟩
    rw [hrange]
    exact (hX v).2 (Or.inr (Or.inr (Or.inl hvT)))
  have hfree : ∀ u : ↥(sUnits ↥K (Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)))),
      (∀ v : InfinitePlace ↥K, infClassHom v ℓ (u : (↥K)ˣ) = 1) →
      (∀ y : ↥X, (y : HeightOneSpectrum (𝓞 ↥K)) ∉ Sp →
        (ℓ : ℤ) ∣ placeValue (y : HeightOneSpectrum (𝓞 ↥K)) (u : (↥K)ˣ)) →
      (ℓ : ℤ) ∣ placeValue ((⟨w, hwX⟩ : ↥X) : HeightOneSpectrum (𝓞 ↥K)) (u : (↥K)ˣ) →
      (∀ y : ↥X, y ≠ ⟨w, hwX⟩ → (y : HeightOneSpectrum (𝓞 ↥K)) ∈ Sp →
        localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ) = 1) →
      ∀ y : ↥X, localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ) = 1 := by
    intro u _ hb hc hd
    have hall : ∀ v : HeightOneSpectrum (𝓞 ↥K), (ℓ : ℤ) ∣ placeValue v (u : (↥K)ˣ) := by
      intro v
      by_cases hvX : v ∈ X
      · by_cases hvw : v = w
        · rw [hvw]
          exact hc
        · by_cases hvSp : v ∈ Sp
          · refine (localClassHom_mem_localUnramified_iff v _).1 ?_
            have h : localClassHom v ℓ (u : (↥K)ˣ) = 1 :=
              hd ⟨v, hvX⟩ (fun h' => hvw (congrArg Subtype.val h')) hvSp
            rw [h]
            exact one_mem _
          · exact hb ⟨v, hvX⟩ hvSp
      · have hvr : v ∉ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) := by
          rw [hrange]
          exact fun h => hvX (Finset.mem_coe.1 h)
        rw [placeValue_eq_zero_of_mem_sUnits u.2 hvr]
        exact dvd_zero _
    have hX₀one : ∀ v ∈ X₀, localClassHom v ℓ (u : (↥K)ˣ) = 1 := by
      intro v hv
      have hvw : v ≠ w := fun h => hX₀w (h ▸ hv)
      have hvX : v ∈ X := (hX v).2 (Or.inr (Or.inl hv))
      exact hd ⟨v, hvX⟩ (fun h' => hvw (congrArg Subtype.val h')) ((hSp v).2 (hX₀split v hv))
    obtain ⟨z, hz⟩ := hdet (u : (↥K)ˣ) hall hX₀one
    intro y
    have h : localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ)
        = localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (z ^ ℓ) := by rw [hz]
    rw [h, _root_.map_pow]
    exact pow_eq_one_of_quotient_range_powMonoidHom ℓ _
  obtain ⟨a, ha1, ha2⟩ := exists_placeValue_not_dvd_of_forall_localClassHom_eq_one
    hℓ hodd hres hζ (ι := (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)))
    Subtype.val_injective hnι hrepr Sp ⟨w, hwX⟩ hfree
  exact ⟨a, ha1, fun v hv hdvd => (hSp v).1 (ha2 v hv hdvd)⟩

end Detect

end InverseGalois.Shafarevich
