/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import InverseGalois.Rigidity.RET.Analytic.InfinityGerm
import InverseGalois.Rigidity.RET.Analytic.GermScale
import InverseGalois.Rigidity.RET.Local.TaylorRescale
import InverseGalois.Rigidity.RET.Local.Rescale

/-!
# The Laurent expansion of a meromorphic germ

A germ meromorphic at the origin has a Laurent expansion: finitely many negative powers followed
by the Taylor series of a holomorphic germ.  This file constructs that expansion as a ring
homomorphism of the field of meromorphic germs into formal Laurent series, and records the three
identities it has to satisfy to be useful.

The construction is a localisation.  A holomorphic germ has a Taylor series, and two holomorphic
germs with the same germ away from the origin have the same Taylor series, so the Taylor series
descends to the subring of holomorphic germs of the germ field.  Every meromorphic germ is a
holomorphic germ divided by a power of the coordinate, which is exactly the statement that the
germ field is the localisation of the holomorphic germs at the powers of the coordinate; the
Taylor series then extends uniquely, because a power of the coordinate becomes a power of the
formal variable, which is invertible in Laurent series.

## Main definitions

* `Rigidity.RET.Analytic.smoothToMero` — a smooth germ at the origin, as a meromorphic germ.
* `Rigidity.RET.Analytic.holoGerms` — the subring of holomorphic germs of the germ field.
* `Rigidity.RET.Analytic.taylorHolo` — the Taylor series of a holomorphic germ.
* `Rigidity.RET.Analytic.meroExpand` — the Laurent expansion of a meromorphic germ.

## Main results

* `Rigidity.RET.Analytic.analyticAt_of_contDiffAt` — a smooth function of a complex variable is
  analytic.
* `Rigidity.RET.Analytic.isLocalization_meroGerm` — the germ field is the localisation of the
  holomorphic germs at the powers of the coordinate.
* `Rigidity.RET.Analytic.meroExpand_injective` — the Laurent expansion is injective.
* `Rigidity.RET.Analytic.meroExpand_invGerm` — the Laurent expansion of the parameter at infinity.
* `Rigidity.RET.Analytic.meroExpand_constHom` — the Laurent expansion of a constant.
* `Rigidity.RET.Analytic.meroExpand_scaleGerm` — the Laurent expansion turns a rotation of the
  coordinate into the rescaling of formal Laurent series.
-/

open Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Rigidity.RET.Analytic

open MeroGerm

/-! ### Smooth germs are holomorphic -/

/-- **A function of a complex variable that is smooth at a point is analytic there.**  It is
complex differentiable at every nearby point, which for a function of a complex variable is
analyticity. -/
theorem analyticAt_of_contDiffAt {x : ℂ} {f : ℂ → ℂ} (hf : ContDiffAt ℂ ∞ f x) :
    AnalyticAt ℂ f x := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
  have h1 : ContDiffAt ℂ (1 : ℕ) f x := hf.of_le (mod_cast le_top)
  filter_upwards [h1.eventually (by simp)] with z hz
  exact hz.differentiableAt (by simp)

theorem meromorphicAt_of_mem_smoothAt {x : ℂ} {f : ℂ → ℂ} (hf : f ∈ smoothAt x) :
    MeromorphicAt f x :=
  (analyticAt_of_contDiffAt (mem_smoothAt.mp hf)).meromorphicAt

/-- A **smooth germ at the origin, as a meromorphic germ**. -/
def smoothToMero : smoothAt (0 : ℂ) →+* MeroGerm (0 : ℂ) where
  toFun F := of (meromorphicAt_of_mem_smoothAt F.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem smoothToMero_apply (F : smoothAt (0 : ℂ)) :
    smoothToMero F = of (meromorphicAt_of_mem_smoothAt F.2) := rfl

theorem smoothToMero_eq_of (F : smoothAt (0 : ℂ)) {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (h : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (F : ℂ → ℂ) u = f u) : smoothToMero F = of hf :=
  of_congr (meromorphicAt_of_mem_smoothAt F.2) hf h

/-- **A smooth germ vanishing away from the origin has vanishing Taylor series.** -/
theorem taylorHom_eq_zero_of_smoothToMero_eq_zero {F : smoothAt (0 : ℂ)}
    (h : smoothToMero F = 0) : taylorHom 0 F = 0 := by
  have h' : ∀ᶠ u in 𝓝[≠] (0 : ℂ), (F : ℂ → ℂ) u = 0 :=
    (of_eq_zero_iff (meromorphicAt_of_mem_smoothAt F.2)).1 h
  have h0 : taylorHom 0 F = taylorHom 0 (0 : smoothAt (0 : ℂ)) :=
    taylorHom_congr_of_punctured F 0 (by filter_upwards [h'] with u hu; simpa using hu)
  rw [h0, map_zero]

/-! ### The subring of holomorphic germs -/

/-- The **holomorphic germs**: the germs at the origin of the functions smooth there, inside the
field of meromorphic germs. -/
abbrev holoGerms : Subring (MeroGerm (0 : ℂ)) := smoothToMero.range

theorem algebraMap_holoGerms (b : ↥holoGerms) :
    algebraMap (↥holoGerms) (MeroGerm (0 : ℂ)) b = (b : MeroGerm (0 : ℂ)) := rfl

/-- The **Taylor series of a holomorphic germ**: the Taylor series of any smooth function whose
germ it is. -/
def taylorHolo : ↥holoGerms →+* PowerSeries ℂ :=
  smoothToMero.rangeRestrict.liftOfSurjective (RingHom.rangeRestrict_surjective _)
    ⟨taylorHom 0, by
      intro F hF
      rw [RingHom.ker_rangeRestrict, RingHom.mem_ker] at hF
      exact RingHom.mem_ker.2 (taylorHom_eq_zero_of_smoothToMero_eq_zero hF)⟩

@[simp] theorem taylorHolo_rangeRestrict (F : smoothAt (0 : ℂ)) :
    taylorHolo (smoothToMero.rangeRestrict F) = taylorHom 0 F :=
  RingHom.liftOfSurjective_comp_apply _ _ _ F

/-- The **coordinate**, as a holomorphic germ. -/
def coordGerm : ↥holoGerms := smoothToMero.rangeRestrict (idGerm 0)

@[simp] theorem coe_coordGerm : (coordGerm : MeroGerm (0 : ℂ)) = smoothToMero (idGerm 0) := rfl

@[simp] theorem taylorHolo_coordGerm : taylorHolo coordGerm = PowerSeries.X := by
  rw [coordGerm, taylorHolo_rangeRestrict, taylorHom_id]

theorem coordGerm_ne_zero : coordGerm ≠ 0 := by
  intro h
  have h0 : taylorHolo coordGerm = 0 := by rw [h, map_zero]
  rw [taylorHolo_coordGerm] at h0
  have h1 := congrArg (PowerSeries.coeff (R := ℂ) 1) h0
  simp at h1

/-! ### The germ field is a localisation of the holomorphic germs -/

/-- **The field of meromorphic germs is the localisation of the holomorphic germs at the powers of
the coordinate.**  A germ meromorphic at the origin is by definition a germ holomorphic there
divided by a power of the coordinate. -/
instance isLocalization_meroGerm :
    IsLocalization (Submonoid.powers coordGerm) (MeroGerm (0 : ℂ)) where
  map_units := by
    rintro ⟨y, n, rfl⟩
    rw [algebraMap_holoGerms]
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    exact coordGerm_ne_zero (pow_eq_zero_iff' .. |>.1 (Subtype.ext (by simpa using h))).1
  surj := by
    intro z
    obtain ⟨f, hf, rfl⟩ := exists_of z
    obtain ⟨n, hn⟩ := id hf
    have hsm : ContDiffAt ℂ ∞ (fun u : ℂ => (u - 0) ^ n • f u) 0 := hn.contDiffAt
    refine ⟨⟨smoothToMero.rangeRestrict ⟨_, hsm⟩, ⟨coordGerm ^ n, n, rfl⟩⟩, ?_⟩
    show of hf * ((coordGerm : MeroGerm (0 : ℂ)) ^ n) = smoothToMero ⟨_, hsm⟩
    rw [coe_coordGerm, ← map_pow, smoothToMero_apply, smoothToMero_apply, of_mul]
    refine of_congr _ _ ?_
    filter_upwards with u
    show f u * u ^ n = (u - 0) ^ n • f u
    rw [sub_zero, smul_eq_mul, mul_comm]
  exists_of_eq := by
    intro a b h
    exact ⟨1, by rw [Subtype.ext h]⟩

/-! ### The Laurent expansion -/

theorem isUnit_taylorHolo_powers (y : ↥(Submonoid.powers coordGerm)) :
    IsUnit (((algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)).comp taylorHolo) y) := by
  obtain ⟨y, n, rfl⟩ := y
  refine isUnit_iff_ne_zero.2 ?_
  rw [RingHom.comp_apply,
    show ((⟨coordGerm ^ n, n, rfl⟩ : ↥(Submonoid.powers coordGerm)) :
      ↥holoGerms) = coordGerm ^ n from rfl, map_pow, taylorHolo_coordGerm, map_pow]
  refine pow_ne_zero _ ?_
  intro h
  have h1 : (PowerSeries.X : PowerSeries ℂ) = 0 :=
    (IsFractionRing.injective (PowerSeries ℂ) (LaurentSeries ℂ)) (by rw [h, map_zero])
  have h2 := congrArg (PowerSeries.coeff (R := ℂ) 1) h1
  simp at h2

/-- The **Laurent expansion** of a meromorphic germ at the origin: the unique extension to the
germ field of the Taylor series of a holomorphic germ. -/
def meroExpand : MeroGerm (0 : ℂ) →+* LaurentSeries ℂ :=
  IsLocalization.lift (M := Submonoid.powers coordGerm) isUnit_taylorHolo_powers

@[simp] theorem meroExpand_smoothToMero (F : smoothAt (0 : ℂ)) :
    meroExpand (smoothToMero F)
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (taylorHom 0 F) := by
  have h : smoothToMero F
      = algebraMap (↥holoGerms) (MeroGerm (0 : ℂ)) (smoothToMero.rangeRestrict F) := rfl
  rw [h, meroExpand, IsLocalization.lift_eq, RingHom.comp_apply, taylorHolo_rangeRestrict]

/-- **The Laurent expansion is injective**: it is a homomorphism out of a field. -/
theorem meroExpand_injective : Function.Injective meroExpand :=
  meroExpand.injective

/-! ### The identities -/

/-- **The Laurent expansion of the parameter at infinity** is the inverse of a power of the formal
variable. -/
theorem meroExpand_invGerm (d : ℕ) :
    meroExpand (invGerm d)
      = (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (PowerSeries.X ^ d))⁻¹ := by
  have hpow : smoothToMero ((idGerm 0) ^ d) = of (analyticAt_powFun d).meromorphicAt := rfl
  rw [invGerm_eq_inv, ← hpow, map_inv₀, meroExpand_smoothToMero, map_pow, taylorHom_id]

/-- **The Laurent expansion of a constant** is the constant formal series. -/
theorem meroExpand_constHom (c : ℂ) :
    meroExpand (constHom 0 c)
      = algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) (PowerSeries.C c) := by
  have hc : smoothToMero (constGerm 0 c) = constHom 0 c := rfl
  rw [← hc, meroExpand_smoothToMero, taylorHom_const]

/-- **A rotation of the coordinate of a smooth germ is a rotation of the coordinate of its germ.**
-/
theorem smoothToMero_scaleGerm {c : ℂ} (hc : c ≠ 0) (F : smoothAt (0 : ℂ)) :
    smoothToMero (_root_.Rigidity.RET.scaleGerm c F) = Analytic.scaleGerm hc (smoothToMero F) := by
  rw [smoothToMero_apply, smoothToMero_apply, scaleGerm_of]

/-- **The Laurent expansion turns a rotation of the coordinate into the rescaling of formal
Laurent series.** -/
theorem meroExpand_comp_scaleGerm {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    meroExpand.comp (Analytic.scaleGerm hc) = (laurentRescale hc).comp meroExpand := by
  refine IsLocalization.ringHom_ext (Submonoid.powers coordGerm) ?_
  ext b
  obtain ⟨F, hF⟩ := b.2
  have hb : algebraMap (↥holoGerms) (MeroGerm (0 : ℂ)) b = smoothToMero F := by
    rw [algebraMap_holoGerms, ← hF]
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hb,
    ← smoothToMero_scaleGerm hc F, meroExpand_smoothToMero, meroExpand_smoothToMero,
    taylorHom_scaleGerm hc1, laurentRescale_algebraMap]

theorem meroExpand_scaleGerm {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) (a : MeroGerm (0 : ℂ)) :
    meroExpand (Analytic.scaleGerm hc a) = laurentRescale hc (meroExpand a) :=
  RingHom.congr_fun (meroExpand_comp_scaleGerm hc hc1) a

end Rigidity.RET.Analytic

end
