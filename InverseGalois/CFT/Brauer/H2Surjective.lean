import Mathlib
import InverseGalois.CFT.Brauer.CrossedProductRecognition
import InverseGalois.CFT.Brauer.Exponent
import InverseGalois.CFT.Brauer.SplittingSubfield

/-!
# The relative Brauer group is the second cohomology group

Let `L / K` be a finite Galois extension.  Every Brauer class split by `L` is represented by a
central simple `K`-algebra of dimension `[L : K] ^ 2` containing a copy of `L`, and such an
algebra is a crossed product of `L / K`.  Combined with the injectivity of the crossed product
homomorphism this identifies the relative Brauer group with the second cohomology group of the
Galois group with coefficients in the multiplicative group of `L`.

## Main results

* `InverseGalois.CFT.exists_brauerHom_eq`: the crossed product homomorphism surjects onto the
  relative Brauer group.
* `InverseGalois.CFT.brauerRelativeEquiv`: the resulting isomorphism
  `H²(Gal(L/K), Lˣ) ≃* Br(L / K)`.
* `InverseGalois.CFT.pow_finrank_eq_one_of_mem_relative`: consequently `Br(L / K)` is killed by
  the degree `[L : K]`.
-/

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Surjectivity of the crossed product homomorphism.**  Every Brauer class split by `L` is the
class of a crossed product of `L / K`. -/
theorem exists_brauerHom_eq (x : BrauerGroup K) (hx : x ∈ BrauerGroup.relative K L) :
    ∃ y, brauerHom (K := K) (L := L) y = x := by
  revert hx
  induction x using Quotient.inductionOn with
  | _ A =>
    intro hA
    obtain ⟨B, emb, hB, hrank⟩ := exists_csa_finrank_sq_of_mem_relative (L := L) A hA
    obtain ⟨c, hc, ⟨e⟩⟩ := exists_algEquiv_crossedProduct_of_finrank_sq emb hrank
    refine ⟨Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ hc)), ?_⟩
    rw [brauerHom_apply hc, ← hB]
    exact Quotient.sound (IsBrauerEquivalent.of_algEquiv e)

/-- The crossed product homomorphism, viewed as a homomorphism into the relative Brauer group. -/
noncomputable def brauerHomRelative :
    Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) →* BrauerGroup.relative K L :=
  MonoidHom.codRestrict brauerHom (BrauerGroup.relative K L) brauerHom_mem_relative

/-- The corestricted homomorphism is computed by the crossed product homomorphism. -/
theorem coe_brauerHomRelative
    (x : Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))) :
    (brauerHomRelative x : BrauerGroup K) = brauerHom x :=
  rfl

/-- The corestricted homomorphism is bijective. -/
theorem brauerHomRelative_bijective :
    Function.Bijective (brauerHomRelative (K := K) (L := L)) := by
  constructor
  · intro x y hxy
    exact brauerHom_injective (congrArg Subtype.val hxy)
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := exists_brauerHom_eq x hx
    exact ⟨y, Subtype.ext hy⟩

/-- **The relative Brauer group of a finite Galois extension is its second cohomology group.** -/
noncomputable def brauerRelativeEquiv :
    Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) ≃* BrauerGroup.relative K L :=
  MulEquiv.ofBijective brauerHomRelative brauerHomRelative_bijective

/-- The isomorphism is given by the crossed product construction. -/
theorem coe_brauerRelativeEquiv
    (x : Multiplicative (H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))) :
    (brauerRelativeEquiv x : BrauerGroup K) = brauerHom x :=
  rfl

/-- **The relative Brauer group is killed by the degree of the extension.** -/
theorem pow_finrank_eq_one_of_mem_relative (x : BrauerGroup K)
    (hx : x ∈ BrauerGroup.relative K L) : x ^ finrank K L = 1 := by
  obtain ⟨y, rfl⟩ := exists_brauerHom_eq x hx
  exact brauerOfH2_pow_finrank (Multiplicative.toAdd y)

end InverseGalois.CFT
