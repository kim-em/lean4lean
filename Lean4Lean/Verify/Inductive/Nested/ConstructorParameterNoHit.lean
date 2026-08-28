import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterPrefix
import Lean4Lean.Verify.VLCtx

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Every proof-relevant expansion stored in a paired translation context is
leaf-free.  This is the exact structural invariant needed while the common
constructor parameters are opened; unlike derivation locality, it makes no
claim about arbitrary typing or definitional-equality proofs. -/
inductive NestedNoHitCtx (leaf : Nat → VExpr → VExpr → Prop) :
    Nat → VLCtx → VLCtx → Prop
  | nil : NestedNoHitCtx leaf depth [] []
  | vlam
      (Hctx : NestedNoHitCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType)
      (HtypeNoHit : Htype.NoHit) :
      NestedNoHitCtx leaf (depth + 1)
        ((ofv, .vlam sourceType) :: source)
        ((ofv, .vlam targetType) :: target)
  | vlet
      (Hctx : NestedNoHitCtx leaf depth source target)
      (Htype : VExpr.NestedExprExpansion leaf depth sourceType targetType)
      (HtypeNoHit : Htype.NoHit)
      (Hvalue : VExpr.NestedExprExpansion leaf depth sourceValue targetValue)
      (HvalueNoHit : Hvalue.NoHit) :
      NestedNoHitCtx leaf depth
        ((ofv, .vlet sourceType sourceValue) :: source)
        ((ofv, .vlet targetType targetValue) :: target)

/-- A leaf-free paired context is literally the same local context on both
sides.  This is stronger and more useful here than an unrestricted context
definitional equality. -/
theorem NestedNoHitCtx.eq
    {leaf : Nat → VExpr → VExpr → Prop} {depth : Nat}
    {source target : VLCtx}
    (H : NestedNoHitCtx leaf depth source target) : source = target := by
  induction H with
  | nil => rfl
  | vlam _ Htype HtypeNoHit ih => simp [ih, HtypeNoHit.eq]
  | vlet _ Htype HtypeNoHit Hvalue HvalueNoHit ih =>
    simp [ih, HtypeNoHit.eq, HvalueNoHit.eq]

end VerifyInductive
end Lean4Lean
