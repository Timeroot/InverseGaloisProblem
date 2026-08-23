import Mathlib
import InverseGalois.CFT.Brauer.CyclicBrauer
import InverseGalois.CFT.Brauer.H2Surjective
import InverseGalois.CFT.NormSubgroup

/-!
# The relative Brauer group of a cyclic extension

Let `L / K` be a finite cyclic Galois extension with generator `σ₀` of `Gal(L/K)`.  The cyclic
algebra construction `a ↦ (L / K, σ₀, a)` is a homomorphism `Kˣ →* Br(K)` whose image is the
relative Brauer group `Br(L / K)` and whose kernel is the group of norms from `Lˣ`.  Consequently
`Br(L / K)` is the quotient of `Kˣ` by the norms.

## Main results

* `InverseGalois.CFT.exists_cyclicBrauerHom_eq`: the cyclic algebra homomorphism surjects onto the
  relative Brauer group.
* `InverseGalois.CFT.ker_cyclicBrauerHom`: the kernel of the cyclic algebra homomorphism is the
  group of norms.
* `InverseGalois.CFT.cyclicBrauerEquiv`: **the main result**, the isomorphism
  `Kˣ / N(Lˣ) ≃* Br(L / K)`, computed on cosets by
  `InverseGalois.CFT.coe_cyclicBrauerEquiv_mk`.
* `InverseGalois.CFT.relative_eq_bot_iff`: `Br(L / K)` is trivial exactly when every unit of `K`
  is a norm from `L`.
-/

open Module

namespace InverseGalois.CFT

open groupCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {σ₀ : Gal(L/K)} (hσ₀ : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers σ₀)

/-! ### Surjectivity onto the relative Brauer group -/

/-- **Every Brauer class split by a cyclic extension is a cyclic algebra.**  The cyclic algebra
homomorphism surjects onto the relative Brauer group `Br(L / K)`. -/
theorem exists_cyclicBrauerHom_eq (x : BrauerGroup K) (hx : x ∈ BrauerGroup.relative K L) :
    ∃ a : Kˣ, cyclicBrauerHom hσ₀ a = x := by
  obtain ⟨y, rfl⟩ := exists_brauerHom_eq x hx
  obtain ⟨f, hf, hy⟩ := exists_isMulCocycle₂_H2π_eq (Multiplicative.toAdd y)
  obtain ⟨a, ha⟩ := exists_mk_csa_eq_cyclicBrauerHom hσ₀ hf
  refine ⟨a, ?_⟩
  have hb : brauerHom (K := K) (L := L) y = ⟦CrossedProduct.csa hf⟧ := by
    show brauerOfH2 (Multiplicative.toAdd y) = _
    rw [← hy, brauerOfH2_apply hf]
  rw [hb, ha]

/-! ### The group of norms -/

/-- **The kernel of the cyclic algebra homomorphism is the group of norms.** -/
theorem ker_cyclicBrauerHom : (cyclicBrauerHom hσ₀).ker = normSubgroup K L := by
  ext a
  rw [mem_ker_cyclicBrauerHom_iff hσ₀, mem_normSubgroup_iff]

/-! ### The relative Brauer group as a quotient of the units -/

/-- The cyclic algebra homomorphism, viewed as a homomorphism into the relative Brauer group. -/
noncomputable def cyclicBrauerHomRelative : Kˣ →* BrauerGroup.relative K L :=
  MonoidHom.codRestrict (cyclicBrauerHom hσ₀) (BrauerGroup.relative K L)
    (cyclicBrauerHom_mem_relative hσ₀)

/-- The corestricted homomorphism is computed by the cyclic algebra homomorphism. -/
theorem coe_cyclicBrauerHomRelative (a : Kˣ) :
    (cyclicBrauerHomRelative hσ₀ a : BrauerGroup K) = cyclicBrauerHom hσ₀ a :=
  rfl

/-- The corestricted homomorphism is surjective. -/
theorem cyclicBrauerHomRelative_surjective :
    Function.Surjective (cyclicBrauerHomRelative hσ₀) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha⟩ := exists_cyclicBrauerHom_eq hσ₀ x hx
  exact ⟨a, Subtype.ext ha⟩

/-- The kernel of the corestricted homomorphism is the group of norms. -/
theorem ker_cyclicBrauerHomRelative :
    (cyclicBrauerHomRelative hσ₀).ker = normSubgroup K L := by
  rw [← ker_cyclicBrauerHom hσ₀]
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj, coe_cyclicBrauerHomRelative]
  rfl

/-- **The relative Brauer group of a cyclic extension.**  For a finite cyclic Galois extension
`L / K` the group `Br(L / K)` is the quotient of `Kˣ` by the norms from `Lˣ`. -/
noncomputable def cyclicBrauerEquiv :
    (Kˣ ⧸ normSubgroup K L) ≃* BrauerGroup.relative K L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_cyclicBrauerHomRelative hσ₀)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (cyclicBrauerHomRelative_surjective hσ₀))

/-- The isomorphism is given on a coset by the cyclic algebra construction. -/
theorem coe_cyclicBrauerEquiv_mk (a : Kˣ) :
    (cyclicBrauerEquiv hσ₀ (QuotientGroup.mk a) : BrauerGroup K) = cyclicBrauerHom hσ₀ a :=
  rfl

include hσ₀ in
/-- **The relative Brauer group is trivial exactly when every unit is a norm.** -/
theorem relative_eq_bot_iff :
    BrauerGroup.relative K L = ⊥ ↔ ∀ a : Kˣ, ∃ b : Lˣ, Algebra.norm K (b : L) = (a : K) := by
  constructor
  · intro h a
    rw [← mem_ker_cyclicBrauerHom_iff hσ₀, MonoidHom.mem_ker]
    have hmem := cyclicBrauerHom_mem_relative hσ₀ a
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨a, rfl⟩ := exists_cyclicBrauerHom_eq hσ₀ x hx
    rw [← MonoidHom.mem_ker, mem_ker_cyclicBrauerHom_iff hσ₀]
    exact h a

end InverseGalois.CFT
