import Mathieu.DefM11
import Mathieu.DefM12
import Mathieu.DefM22
import Mathieu.DefM23
import Mathieu.DefM24
import Mathieu.FastBFS
import Mathieu.EnumM11
import Mathieu.EnumM12Clean
import Mathieu.EnumM24Iso
import Mathieu.BasicM11
import Mathieu.BasicM12
import Mathieu.BasicM22
import Mathieu.BasicM23
import Mathieu.BasicM24
import Mathieu.SimpleCriterion
import Mathieu.InductiveSimple
import Mathieu.CosetSimple
import Mathieu.M11SimpleClean
import Mathieu.Primitivity
import Mathieu.Perfect
import Mathieu.M22Cycles
import Mathieu.M22CardClean
import Mathieu.Subgroups
import Mathieu.F4
import Mathieu.CardSL
import Mathieu.ProjF4
import Mathieu.EnumSL34
import Mathieu.PSL34
import Mathieu.TransPSL34
import Mathieu.EnumSL223
import Mathieu.EnumL211
import Mathieu.ActL211
import Mathieu.CoverL211
import Mathieu.FilterL211
import Mathieu.PSL211
import Mathieu.SL211Gen
import Mathieu.SL211Perfect
import Mathieu.PSL211Simple
import Mathieu.PSL223
import Mathieu.PSL
import Mathieu.M21IsoPSL34
import Mathieu.TransM21
import Mathieu.TransM22
import Mathieu.TransM23
import Mathieu.TransM24
import Mathieu.Golay
import Mathieu.M11Steiner
import Mathieu.M11ExceptionalTrans
import Mathieu.PerfectM22
import Mathieu.M11Simple
import Mathieu.M12Simple
import Mathieu.M22Simple
import Mathieu.M23Simple
import Mathieu.M24Simple

/-!
# The Mathieu groups

This library develops the five sporadic Mathieu groups `M₁₁`, `M₁₂`, `M₂₂`, `M₂₃`, `M₂₄`
as permutation groups, along with their basic properties, mutual subgroup relations,
relations to projective special linear groups, and to the Golay codes.

See `PLAN.md` at the project root for the overall goal list and proof strategy.
-/
