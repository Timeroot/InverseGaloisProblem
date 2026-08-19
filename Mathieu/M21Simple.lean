import Mathieu.PSL34Simple
import Mathieu.M21IsoPSL34

/-!
# Simplicity of `M₂₁ ≅ PSL(3, 4)`

`M₂₁` (the three-point stabiliser in `M₂₄`, the group `≅ PSL(3, 4)`) is a simple group.  This is
an immediate transport of `PSL(3, GaloisField 2 2)`'s simplicity
(`PSL34.PSL34GF_isSimpleGroup`, proved via the Iwasawa criterion in `PSL34Simple.lean`) along the
isomorphism `M₂₁ ≅ PSL(3, 4)` (`M21_iso_PSL34`).

This is the point-stabiliser input that lets `M₂₂` simplicity move to the clean inductive
primitive-action route (the same route used for `M₁₂`, `M₂₃`, `M₂₄`).
-/

namespace Mathieu

open scoped MatrixGroups

/-- **`M₂₁` is a simple group.** (Transport of `PSL(3,4)` simplicity along `M₂₁ ≅ PSL(3,4)`.) -/
theorem M21_isSimpleGroup : IsSimpleGroup M21 := by
  obtain ⟨φ⟩ := M21_iso_PSL34
  haveI := PSL34.PSL34GF_isSimpleGroup
  exact MulEquiv.isSimpleGroup φ

end Mathieu
