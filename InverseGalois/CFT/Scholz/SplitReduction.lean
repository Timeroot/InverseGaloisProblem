import Mathlib
import InverseGalois.CFT.Scholz.Induction

/-!
# The central step is only needed for non-split extensions

The Scholz–Reichardt induction is driven by one embedding step: a finite group `G` surjecting onto
`H` with central kernel of order `ℓ` must be realised as soon as `H` is.  When the surjection
admits a homomorphic section the step is free, because a central kernel with a section splits the
group as a direct product, and a direct product with a cyclic group of order `ℓ` is exactly what
the compositum construction of the split case produces.  The level is not even a cost: Serre's
condition at level `N + 1` implies it at level `N`, and the split case preserves the level.

So the arithmetic of the induction is confined to the extensions that do not split, which is where
the obstruction — a class in `H²(H, C_ℓ)` — is nonzero and class field theory is called for.

## Main definitions

* `InverseGalois.CFT.IsNonsplitCentralStepSolvable`: the central embedding step, restricted to
  surjections with no homomorphic section.

## Main results

* `InverseGalois.CFT.mulEquivProdOfSection`: a surjection with central kernel and a homomorphic
  section presents its source as the direct product of the kernel with the target.
* `InverseGalois.CFT.IsScholzRealizable.mono`: a realization at one level is a realization at every
  smaller level.
* `InverseGalois.CFT.IsCentralStepSolvable.of_nonsplit`: **the central step follows from its
  restriction to non-split extensions.**
-/

namespace InverseGalois.CFT

/-! ### Splitting a central extension -/

/-- **A surjection with central kernel and a homomorphic section splits as a direct product.**
The multiplication map `(z, h) ↦ z * s h` is a homomorphism because the kernel is central, and it
is inverted by `g ↦ (g * (s (f g))⁻¹, f g)`. -/
def mulEquivProdOfSection {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : f.ker ≤ Subgroup.center G) (s : H →* G) (hs : ∀ x, f (s x) = x) :
    ↥f.ker × H ≃* G where
  toFun p := (p.1 : G) * s p.2
  invFun g := (⟨g * (s (f g))⁻¹, by
    simp [MonoidHom.mem_ker, hs]⟩, f g)
  left_inv p := by
    have hz : f (p.1 : G) = 1 := p.1.2
    have hfp : f ((p.1 : G) * s p.2) = p.2 := by rw [map_mul, hz, hs, one_mul]
    refine Prod.ext (Subtype.ext ?_) hfp
    simp [hfp]
  right_inv g := by
    simp
  map_mul' p q := by
    have hcomm := Subgroup.mem_center_iff.mp (hf q.1.2) (s p.2)
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    rw [mul_assoc (p.1 : G) (s p.2), ← mul_assoc (s p.2), hcomm]
    group

/-! ### Levels -/

variable {G H : Type*} [Group G] [Group H] {ℓ N M : ℕ}

/-- **A realization at one level is a realization at every smaller level.**  Serre's condition
becomes weaker as the level drops, since a prime congruent to one modulo `ℓ ^ N` is congruent to
one modulo every smaller power. -/
theorem IsScholzRealizable.mono (h : IsScholzRealizable G ℓ N) (hMN : M ≤ N) :
    IsScholzRealizable G ℓ M :=
  h.elim fun R => ⟨{ R with isScholz := R.isScholz.mono hMN }⟩

/-! ### The reduction -/

/-- **The central embedding step for extensions that do not split.**  This is the property
`InverseGalois.CFT.IsCentralStepSolvable` with the surjections admitting a homomorphic section
removed from its scope. -/
def IsNonsplitCentralStepSolvable (ℓ : ℕ) : Prop :=
  ∀ (N : ℕ) {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H), IsPGroup ℓ G →
    Function.Surjective f → f.ker ≤ Subgroup.center G → Nat.card f.ker = ℓ →
    (¬ ∃ s : H →* G, ∀ x, f (s x) = x) →
    IsScholzRealizable H ℓ (N + 1) → IsScholzRealizable G ℓ N

/-- **The central step follows from its restriction to non-split extensions.**  A split extension
with central kernel of order `ℓ` is a direct product with a cyclic group of order `ℓ`, which the
compositum construction of the split case already realises, at the same level and hence a fortiori
at the level the step promises. -/
theorem IsCentralStepSolvable.of_nonsplit (hℓ : ℓ.Prime) (h : IsNonsplitCentralStepSolvable ℓ) :
    IsCentralStepSolvable ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro N G H _ _ _ f hpg hsurj hker hcard hH
  by_cases hsplit : ∃ s : H →* G, ∀ x, f (s x) = x
  · obtain ⟨s, hs⟩ := hsplit
    have hZ : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by simp
    have e : ↥f.ker ≃* Multiplicative (ZMod ℓ) := mulEquivOfPrimeCardEq hcard hZ
    refine isScholzRealizable_of_prod_cyclic hℓ ?_ (hH.mono (Nat.le_succ N))
    exact (mulEquivProdOfSection f hker s hs).symm.trans
      ((MulEquiv.prodCongr e (MulEquiv.refl H)).trans MulEquiv.prodComm)
  · exact h N f hpg hsurj hker hcard hsplit hH

end InverseGalois.CFT
