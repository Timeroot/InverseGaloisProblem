import Mathlib
import InverseGalois.CFT.Local.HilbertSymbol

/-!
# The Hilbert symbol under a field homomorphism

A homomorphism of fields carries a nontrivial point of the conic `z ^ 2 = a x ^ 2 + b y ^ 2` to a
nontrivial point of the conic with the transported coefficients, because a field homomorphism is
injective.  So isotropy is preserved, the symbol can only go up, and anisotropy over a larger
field forces anisotropy over the smaller one.  This is the mechanism by which a global Hilbert
symbol controls, and is controlled by, its local avatars.

## Main results

* `InverseGalois.CFT.Local.IsHilbertIsotropic.map`: isotropy is preserved by a field
  homomorphism.
* `InverseGalois.CFT.Local.hilbertSymbol_map_eq_one`: so is the value one of the symbol.
* `InverseGalois.CFT.Local.hilbertSymbol_eq_neg_one_of_map`: the contrapositive, which is how
  local obstructions are transported back to the base field.
* `InverseGalois.CFT.Local.hilbertSymbol_ratCast_eq_one`: the case of a field of characteristic
  zero, where the homomorphism is the canonical one from the rationals.
-/

namespace InverseGalois.CFT.Local

variable {K L : Type*} [Field K] [Field L]

/-- **Isotropy is preserved by a field homomorphism.**  A field homomorphism is injective, so it
carries a nontrivial point of the conic to a nontrivial point of the transported conic. -/
theorem IsHilbertIsotropic.map (f : K →+* L) {a b : K} (h : IsHilbertIsotropic a b) :
    IsHilbertIsotropic (f a) (f b) := by
  obtain ⟨x, y, z, hne, hz⟩ := h
  refine ⟨f x, f y, f z, ?_, ?_⟩
  · rintro ⟨hx, hy, hz0⟩
    refine hne ⟨?_, ?_, ?_⟩
    · exact (map_eq_zero_iff f f.injective).1 hx
    · exact (map_eq_zero_iff f f.injective).1 hy
    · exact (map_eq_zero_iff f f.injective).1 hz0
  · have := congrArg f hz
    simpa only [map_add, map_mul, map_pow] using this

/-- The Hilbert symbol of the images is one as soon as the Hilbert symbol of the arguments is. -/
theorem hilbertSymbol_map_eq_one (f : K →+* L) {a b : K} (h : hilbertSymbol a b = 1) :
    hilbertSymbol (f a) (f b) = 1 :=
  hilbertSymbol_eq_one_iff.2 ((hilbertSymbol_eq_one_iff.1 h).map f)

/-- An anisotropic form stays anisotropic when pulled back along a field homomorphism. -/
theorem hilbertSymbol_eq_neg_one_of_map (f : K →+* L) {a b : K}
    (h : hilbertSymbol (f a) (f b) = -1) : hilbertSymbol a b = -1 := by
  rcases hilbertSymbol_eq_one_or a b with h1 | h1
  · rw [hilbertSymbol_map_eq_one f h1] at h
    exact absurd h (by norm_num)
  · exact h1

/-- The symbol computed over a field extension dominates the symbol computed over the base. -/
theorem hilbertSymbol_algebraMap_eq_one [Algebra K L] {a b : K} (h : hilbertSymbol a b = 1) :
    hilbertSymbol (algebraMap K L a) (algebraMap K L b) = 1 :=
  hilbertSymbol_map_eq_one (algebraMap K L) h

/-- Over a field of characteristic zero the rational Hilbert symbol is dominated by the symbol of
the images of the arguments. -/
theorem hilbertSymbol_ratCast_eq_one [CharZero L] {a b : ℚ} (h : hilbertSymbol a b = 1) :
    hilbertSymbol (a : L) (b : L) = 1 :=
  hilbertSymbol_map_eq_one (Rat.castHom L) h

/-- A rational form that is anisotropic over some field of characteristic zero is already
anisotropic over the rationals. -/
theorem hilbertSymbol_rat_eq_neg_one_of_cast [CharZero L] {a b : ℚ}
    (h : hilbertSymbol (a : L) (b : L) = -1) : hilbertSymbol a b = -1 :=
  hilbertSymbol_eq_neg_one_of_map (Rat.castHom L) h

end InverseGalois.CFT.Local
