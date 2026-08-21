import Mathlib
import InverseGalois.CFT.Brauer.H2Brauer
import InverseGalois.CFT.GroupCohomology.Corestriction

/-!
# The degree of a splitting field kills the crossed product classes

The cohomology of a finite group in positive degrees is killed by the order of the group.  For
`H²(Gal(L/K), Lˣ)` that order is the degree `[L : K]`, so every Brauer class coming from a
crossed product of `L / K` has order dividing `[L : K]`.

## Main results

* `InverseGalois.CFT.brauerOfH2_pow_finrank`: the class attached to an element of
  `H²(Gal(L/K), Lˣ)` is killed by `[L : K]`.
* `InverseGalois.CFT.CrossedProduct.mk_csa_pow_finrank`: the Brauer class of a crossed product of
  `L / K` is killed by `[L : K]`.
-/

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The Brauer class attached to a class in `H²(Gal(L/K), Lˣ)` is killed by the degree of the
extension. -/
theorem brauerOfH2_pow_finrank (x : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    brauerOfH2 x ^ finrank K L = (1 : BrauerGroup K) := by
  have hcard : Nat.card Gal(L/K) = finrank K L := IsGalois.card_aut_eq_finrank K L
  have hzero : Nat.card Gal(L/K) • x = 0 :=
    natCard_nsmul_eq_zero (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) 1 x
  have hpow : brauerHom (Multiplicative.ofAdd x) ^ Nat.card Gal(L/K)
      = brauerHom (Multiplicative.ofAdd (Nat.card Gal(L/K) • x)) := by
    rw [← map_pow]
    rfl
  rw [← hcard]
  calc brauerOfH2 x ^ Nat.card Gal(L/K)
      = brauerHom (Multiplicative.ofAdd x) ^ Nat.card Gal(L/K) := rfl
    _ = brauerHom (Multiplicative.ofAdd (Nat.card Gal(L/K) • x)) := hpow
    _ = brauerHom (Multiplicative.ofAdd (0 : H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))) := by
        rw [hzero]
    _ = 1 := map_one brauerHom

namespace CrossedProduct

/-- **The Brauer class of a crossed product of `L / K` is killed by the degree `[L : K]`.** -/
theorem mk_csa_pow_finrank {f : Gal(L/K) × Gal(L/K) → Lˣ} (hf : IsMulCocycle₂ f) :
    (⟦csa hf⟧ : BrauerGroup K) ^ finrank K L = 1 := by
  rw [← brauerOfH2_apply hf]
  exact brauerOfH2_pow_finrank _

end CrossedProduct

end InverseGalois.CFT
