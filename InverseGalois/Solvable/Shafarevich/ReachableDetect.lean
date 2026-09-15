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
there, trivial class at a prescribed finite set of places, order divisible by the exponent at a
second prescribed finite set, and order divisible by the exponent at every other place except the
ones sitting under a completely decomposed place of the level.  Duality produces such a unit as soon
as the units it has to be tested against are trivial, and those are the units which are of order
divisible by the exponent away from the first prescribed set — nothing at all being asked of them
there — and locally a power at the places the duality imposes nothing at.

So the whole arithmetic of reachability is a detection statement: it is enough to exhibit finitely
many places, sitting under completely decomposed places of the level and away from the one being
asked for and from the two prescribed sets, at which being a local power already forces a unit of
order divisible by the exponent away from the first set to be a power of the level itself.  The
units the duality tests against are then powers, and a power has trivial class at every place at
once, which is exactly what the duality asks of them.

The finite set of places the duality is run over is assembled from five pieces: the detecting
places, the place being asked for and the two prescribed sets, which the prescription names, and the
places carrying the exponent together with a system of representatives of the ideal classes, which
the duality needs in order to realise a prescribed system of orders.  The last is harmless, because
away from the detecting places, the named one and the prescribed sets the unit produced is only ever
asked to be of order divisible by the exponent, and a power is.

## Main results

* `InverseGalois.Shafarevich.exists_unit_reachable_of_detecting`: **a place of a finite level is
  reached once finitely many places sitting under completely decomposed places of the level detect
  the powers.**

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
the place being asked for and the two prescribed sets; what they have to detect is that a unit of
order divisible by the exponent away from the first prescribed set, and a local power at each of
them, is a power of the level.  The duality is then run over those places together with the named
one, the two prescribed sets, the places carrying the exponent and a system of representatives of
the ideal classes, and the units it tests against are exactly the ones the detection hypothesis
speaks about, so they are powers and have trivial class everywhere. -/
theorem exists_unit_reachable_of_detecting {ℓ : ℕ} (hℓ : ℓ.Prime)
    {K : IntermediateField k Ω} [NumberField ↥K] {E : IntermediateField k Ω}
    {ζ : ↥K} (hζ : IsPrimitiveRoot ζ ℓ) (Tz Xex : Set (HeightOneSpectrum (𝓞 ↥K)))
    (hTzfin : Tz.Finite) (hXexfin : Xex.Finite) (w : HeightOneSpectrum (𝓞 ↥K)) (hwTz : w ∉ Tz)
    (hwXex : w ∉ Xex) (X₀ : Finset (HeightOneSpectrum (𝓞 ↥K))) (hX₀w : w ∉ X₀)
    (hX₀Tz : ∀ v ∈ X₀, v ∉ Tz) (hX₀Xex : ∀ v ∈ X₀, v ∉ Xex)
    (hX₀split : ∀ v ∈ X₀, ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ →
      Ideal.under (𝓞 ↥K) P = v.asIdeal → stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup)
    (hdet : ∀ u : (↥K)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 ↥K), v ∉ Tz → (ℓ : ℤ) ∣ placeValue v u) →
      (∀ v ∈ X₀, localClassHom v ℓ (u : (↥K)ˣ) = 1) → ∃ z : (↥K)ˣ, u = z ^ ℓ) :
    ∃ u : (↥K)ˣ, ¬ (ℓ : ℤ) ∣ placeValue w u ∧
      (∀ v ∈ Tz, localClassHom v ℓ u = 1) ∧
      (∀ v ∈ Xex, (ℓ : ℤ) ∣ placeValue v u) ∧
      ∀ v : HeightOneSpectrum (𝓞 ↥K), v ≠ w → ¬ (ℓ : ℤ) ∣ placeValue v u →
        ∀ P : Ideal (𝓞 Ω), P.IsPrime → P ≠ ⊥ → Ideal.under (𝓞 ↥K) P = v.asIdeal →
          stabilizer Gal(Ω/k) P ≤ E.fixingSubgroup := by
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
      (v = w ∨ v ∈ X₀ ∨ v ∈ Tz ∨ v ∈ Xex ∨ v ∈ T ∨
        FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1) :=
    ⟨insert w (X₀ ∪ (hTzfin.toFinset ∪ (hXexfin.toFinset ∪
        (hTfin.toFinset ∪ hℓfin.toFinset)))), fun v => by
      simp only [Finset.mem_insert, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  have hwX : w ∈ X := (hX w).2 (Or.inl rfl)
  have hrange : Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) = ↑X := Subtype.range_coe
  have hnι : ∀ v : HeightOneSpectrum (𝓞 ↥K), FinitePlace.mk v ((ℓ : ℕ) : ↥K) ≠ 1 →
      v ∈ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) := by
    intro v hv
    rw [hrange]
    exact (hX v).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hv)))))
  have hrepr : ∀ m : HeightOneSpectrum (𝓞 ↥K) → ℤ,
      (∀ᶠ v : HeightOneSpectrum (𝓞 ↥K) in Filter.cofinite, m v = 0) →
      ∃ a : (↥K)ˣ, ∀ v ∉ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)),
        Rigidity.RET.ord ↥K v (a : ↥K) = m v := by
    intro m hm
    obtain ⟨a, ha⟩ := hTrepr m hm
    refine ⟨a, fun v hv => ha v fun hvT => hv ?_⟩
    rw [hrange]
    exact (hX v).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvT)))))
  have hfree : ∀ u : ↥(sUnits ↥K (Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)))),
      (∀ v : InfinitePlace ↥K, infClassHom v ℓ (u : (↥K)ˣ) = 1) →
      (∀ y : ↥X, (y : HeightOneSpectrum (𝓞 ↥K)) ∉ Tz →
        (y = ⟨w, hwX⟩ ∨ (y : HeightOneSpectrum (𝓞 ↥K)) ∉ Sp ∨
          (y : HeightOneSpectrum (𝓞 ↥K)) ∈ Xex) →
        (ℓ : ℤ) ∣ placeValue (y : HeightOneSpectrum (𝓞 ↥K)) (u : (↥K)ˣ)) →
      (∀ y : ↥X, (y : HeightOneSpectrum (𝓞 ↥K)) ∉ Tz → y ≠ ⟨w, hwX⟩ →
        (y : HeightOneSpectrum (𝓞 ↥K)) ∈ Sp → (y : HeightOneSpectrum (𝓞 ↥K)) ∉ Xex →
        localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ) = 1) →
      ∀ y : ↥X, localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ) = 1 := by
    intro u _ hb hd
    have hall : ∀ v : HeightOneSpectrum (𝓞 ↥K), v ∉ Tz →
        (ℓ : ℤ) ∣ placeValue v (u : (↥K)ˣ) := by
      intro v hvTz
      by_cases hvX : v ∈ X
      · by_cases hvw : v = w
        · exact hb ⟨v, hvX⟩ hvTz (Or.inl (Subtype.ext hvw))
        · by_cases hvXex : v ∈ Xex
          · exact hb ⟨v, hvX⟩ hvTz (Or.inr (Or.inr hvXex))
          · by_cases hvSp : v ∈ Sp
            · refine (localClassHom_mem_localUnramified_iff v _).1 ?_
              have h : localClassHom v ℓ (u : (↥K)ˣ) = 1 :=
                hd ⟨v, hvX⟩ hvTz (fun h' => hvw (congrArg Subtype.val h')) hvSp hvXex
              rw [h]
              exact one_mem _
            · exact hb ⟨v, hvX⟩ hvTz (Or.inr (Or.inl hvSp))
      · have hvr : v ∉ Set.range (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)) := by
          rw [hrange]
          exact fun h => hvX (Finset.mem_coe.1 h)
        rw [placeValue_eq_zero_of_mem_sUnits u.2 hvr]
        exact dvd_zero _
    have hX₀one : ∀ v ∈ X₀, localClassHom v ℓ (u : (↥K)ˣ) = 1 := by
      intro v hv
      have hvw : v ≠ w := fun h => hX₀w (h ▸ hv)
      have hvX : v ∈ X := (hX v).2 (Or.inr (Or.inl hv))
      exact hd ⟨v, hvX⟩ (hX₀Tz v hv) (fun h' => hvw (congrArg Subtype.val h'))
        ((hSp v).2 (hX₀split v hv)) (hX₀Xex v hv)
    obtain ⟨z, hz⟩ := hdet (u : (↥K)ˣ) hall hX₀one
    intro y
    have h : localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (u : (↥K)ˣ)
        = localClassHom (y : HeightOneSpectrum (𝓞 ↥K)) ℓ (z ^ ℓ) := by rw [hz]
    rw [h, _root_.map_pow]
    exact pow_eq_one_of_quotient_range_powMonoidHom ℓ _
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := exists_placeValue_not_dvd_of_forall_localClassHom_eq_one
    hℓ hres hζ (ι := (Subtype.val : ↥X → HeightOneSpectrum (𝓞 ↥K)))
    Subtype.val_injective hnι hrepr Tz Xex Sp ⟨w, hwX⟩ hwTz hwXex hfree
  refine ⟨a, ha1, fun v hv => ha2 ⟨v, (hX v).2 (Or.inr (Or.inr (Or.inl hv)))⟩ hv,
    fun v hv => ha3 ⟨v, (hX v).2 (Or.inr (Or.inr (Or.inr (Or.inl hv))))⟩ hv,
    fun v hv hdvd => (hSp v).1 (ha4 v hv hdvd)⟩

end Detect

end InverseGalois.Shafarevich
