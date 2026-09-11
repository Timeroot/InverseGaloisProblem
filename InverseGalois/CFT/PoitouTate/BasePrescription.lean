/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.CFT.PoitouTate.NormLocalPower
import InverseGalois.CFT.PoitouTate.TwoPlacesFree
import InverseGalois.CFT.Units.SplitCompletion

/-!
# The prescribed local behaviour carried down to the base field

The two-place construction produces a unit of the upper field realising a prescribed local
behaviour on a stable finite set of places and ramified at exactly two further places, both of them
completely split.  What one wants is a number of the base field, and the way down is the norm.

The norm is local–global compatible: at a place of the base the class of the norm is decided by the
classes of the element at the places above.  On the stable set the constructed unit and the
prescribed one have the same classes at every place above a given place, so their norms have the
same class there.  Away from that set the constructed unit is unramified at every place except the
two, so as long as the base place is unramified in the extension its norm is unramified as well.
And at the two exceptional places the decomposition group is trivial, so the completion of the base
is already the completion of the upper field and therefore contains the roots of unity the upper
field was assumed to contain; nothing at all is claimed about the class of the norm there beyond
what those roots of unity already give.

## Main results

* `InverseGalois.CFT.exists_base_places_norm_class_eq_of_split`: **a number of the base field which
  is a norm, whose class agrees with the class of the norm of the prescribed unit on the given set
  of places, and which is unramified away from that set except at two completely split places.**
* `InverseGalois.CFT.exists_base_norm_class_unramified_or_isPrimitiveRoot`: the same number, read as
  being unramified or living over a completion containing the roots of unity at every place outside
  the given set.

## Tags

number field, norm, place, local class, unramified, completely split, root of unity
-/

set_option synthInstance.maxHeartbeats 800000

namespace InverseGalois.CFT

open IsDedekindDomain MulAction NumberField

open scoped Pointwise

/-! ### The norm of the constructed unit -/

section Base

variable {k A K : Type} [Field k] [NumberField k] [Field A] [Algebra k A] [Normal k A]
  [IsAlgClosed A] [Field K] [NumberField K] [Algebra k K] [Algebra K A] [IsGalois k K]
  {Ω : IntermediateField k A} [NumberField ↥Ω] [Normal k ↥Ω] [Algebra K ↥Ω]
  [IsScalarTower k K ↥Ω] [IsScalarTower K ↥Ω A] [IsGalois K ↥Ω] {p : ℕ} [NeZero p]
  {Pc Ec : HeightOneSpectrum (𝓞 K) → ℕ}

/-- **A number of the base field which is a norm, whose class agrees with the class of the norm of
the prescribed unit on the given set of places, and which is unramified away from that set except at
two places completely split in the auxiliary field.**  The set of places is asked to be stable, to
contain those over the exponent and those ramified in the extension, and the prescribed unit to fail
to be a unit outside it only at places which are themselves completely split. -/
theorem exists_base_places_norm_class_eq_of_split (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T)
    (hTram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ T)
    {y : Kˣ}
    (hysplit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Rigidity.RET.ord K v (y : K) ≠ 0 →
      ∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = v ∧
        stabilizer Gal(↥Ω/k) w = ⊥)
    (hyunr : ∀ v ∈ T, localClassHom v p y ∈ localUnramified v p)
    (hyp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p y = 1) :
    ∃ Q R : HeightOneSpectrum (𝓞 K), ∃ x : kˣ,
      (∃ z : Kˣ, x = Units.map (Algebra.norm k : K →* k) z) ∧
      stabilizer Gal(K/k) Q = ⊥ ∧ stabilizer Gal(K/k) R = ⊥ ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = Q ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      (∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = R ∧
        stabilizer Gal(↥Ω/k) w = ⊥) ∧
      primeUnder (𝓞 k) Q ≠ primeUnder (𝓞 k) R ∧
      (∀ v ∈ T, primeUnder (𝓞 k) v ≠ primeUnder (𝓞 k) Q) ∧
      (∀ v ∈ T, primeUnder (𝓞 k) v ≠ primeUnder (𝓞 k) R) ∧
      (∀ v ∈ T, localClassHom (primeUnder (𝓞 k) v) p x
        = localClassHom (primeUnder (𝓞 k) v) p (Units.map (Algebra.norm k : K →* k) y)) ∧
      ∀ q : HeightOneSpectrum (𝓞 k), (∀ v ∈ T, primeUnder (𝓞 k) v ≠ q) →
        q ≠ primeUnder (𝓞 k) Q → q ≠ primeUnder (𝓞 k) R →
        localClassHom q p x ∈ localUnramified q p := by
  classical
  obtain ⟨Q, R, hQT, hRT, hQspl, hRspl, hQR, hQstab, hRstab, z, hzT, hzunr, -, -, -, -⟩ :=
    exists_two_places_sUnit_class_eq_of_split (Ω := Ω) (Tr := ∅) hp hodd hζ hres hTstable
      (Finset.empty_subset T) (fun _ v hv => absurd hv (Finset.notMem_empty v)) hpT hysplit
      (fun v hv _ => hyunr v hv) (fun _ _ v hv => absurd hv (Finset.notMem_empty v)) hyp
  have hTQ : ∀ v ∈ T, primeUnder (𝓞 k) v ≠ primeUnder (𝓞 k) Q := by
    intro v hv hcon
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(K/k)) hcon
    exact hQT (hσ ▸ hTstable σ v hv)
  have hTR : ∀ v ∈ T, primeUnder (𝓞 k) v ≠ primeUnder (𝓞 k) R := by
    intro v hv hcon
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(K/k)) hcon
    exact hRT (hσ ▸ hTstable σ v hv)
  refine ⟨Q, R, Units.map (Algebra.norm k : K →* k) z, ⟨z, rfl⟩, hQstab, hRstab, hQspl, hRspl,
    ?_, hTQ, hTR, fun v hv => ?_, fun q hq hqQ hqR => ?_⟩
  · intro hcon
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_primeUnder_eq (A := 𝓞 k) (G := Gal(K/k)) hcon.symm
    exact hQR σ hσ.symm
  · exact localClassHom_norm_eq_of_forall_eq k v hp.ne_zero z y
      fun σ => hzT (σ • v) (hTstable σ v hv)
  · obtain ⟨P, rfl⟩ := exists_primeUnder_eq (𝓞 k) (𝓞 K) q
    have hPT : P ∉ T := fun hc => hq P hc rfl
    refine localClassHom_norm_mem_localUnramified k P (not_not.1 fun hc => hPT (hTram P hc)) z
      fun σ => (localClassHom_mem_localUnramified_iff (σ • P) z).2 ?_
    refine hzunr (σ • P) (Finset.notMem_empty _) (fun hc => hqQ ?_) (fun hc => hqR ?_)
    · rw [← hc, primeUnder_smul_eq]
    · rw [← hc, primeUnder_smul_eq]

/-- **A number of the base field which is a norm, whose class agrees with the class of the norm of
the prescribed unit on the given set of places, and which at every place outside that set is either
unramified or lies over a completion containing the roots of unity.**  Away from the two
exceptional places the norm is unramified; at those two the base place is completely split, so its
completion is the completion of the upper field and carries the roots of unity that field was
assumed to contain. -/
theorem exists_base_norm_class_unramified_or_isPrimitiveRoot (hp : p.Prime) (hodd : 2 < p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hres : ∀ v : HeightOneSpectrum (𝓞 K), HasResidueChar (v.adicCompletion K) (Pc v) (Ec v))
    {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hTstable : ∀ (σ : Gal(K/k)) (v : HeightOneSpectrum (𝓞 K)), v ∈ T → σ • v ∈ T)
    (hpT : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.mk v ((p : ℕ) : K) ≠ 1 → v ∈ T)
    (hTram : ∀ v : HeightOneSpectrum (𝓞 K), ramIdx (𝓞 k) v ≠ 1 → v ∈ T)
    {y : Kˣ}
    (hysplit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Rigidity.RET.ord K v (y : K) ≠ 0 →
      ∃ w : HeightOneSpectrum (𝓞 ↥Ω), primeUnder (𝓞 K) w = v ∧
        stabilizer Gal(↥Ω/k) w = ⊥)
    (hyunr : ∀ v ∈ T, localClassHom v p y ∈ localUnramified v p)
    (hyp : ∀ v ∈ T, Pc v ∣ p → localClassHom v p y = 1) :
    ∃ x : kˣ, (∃ z : Kˣ, x = Units.map (Algebra.norm k : K →* k) z) ∧
      (∀ v ∈ T, localClassHom (primeUnder (𝓞 k) v) p x
        = localClassHom (primeUnder (𝓞 k) v) p (Units.map (Algebra.norm k : K →* k) y)) ∧
      ∀ q : HeightOneSpectrum (𝓞 k), (∀ v ∈ T, primeUnder (𝓞 k) v ≠ q) →
        localClassHom q p x ∈ localUnramified q p ∨
          ∃ ξ : q.adicCompletion k, IsPrimitiveRoot ξ p := by
  classical
  obtain ⟨Q, R, x, hxnorm, hQstab, hRstab, -, -, -, -, -, hxT, hxunr⟩ :=
    exists_base_places_norm_class_eq_of_split (Ω := Ω) hp hodd hζ hres hTstable hpT hTram
      hysplit hyunr hyp
  refine ⟨x, hxnorm, hxT, fun q hq => ?_⟩
  by_cases hqQ : q = primeUnder (𝓞 k) Q
  · exact Or.inr (hqQ ▸ exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot k Q hζ hQstab)
  by_cases hqR : q = primeUnder (𝓞 k) R
  · exact Or.inr (hqR ▸ exists_isPrimitiveRoot_adicCompletion_of_stabilizer_eq_bot k R hζ hRstab)
  exact Or.inl (hxunr q hq hqQ hqR)

end Base

end InverseGalois.CFT
