import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationCoherence
import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment

/-! The actual application function query also recovers raw result-type
conversion. This evidence is independent of whether the requested codomain
support is empty and is needed by enclosing Pi prototype guards. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Read the raw codomain path from the same Pi answer used by application
code coherence. The literal argument typing comes from the prepared frame's
actual guard. No raw Pi-injectivity theorem or right-domain equality premise
is needed. -/
theorem SeededApplicationCodeInput.comparisonPath
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {leftLocals rightLocals : List Nat} {σ τ : Subst}
    {leftAvailable rightAvailable : Valuation}
    {A B a C D b : VExpr} {result : Profile n} {before : Footprint}
    (frame : SeededApplicationCodeInput env U registry target leftLocals σ leftAvailable A B a result before)
    (sameArgument : a.subst σ = b.subst τ)
    (functionAnswer : CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE A B) (.forallE C D) frame.profile) :
    TypeConversion env U target ((B.inst a).subst σ) ((D.inst b).subst τ) := by
  have rawArgument : env.HasType U target (a.subst σ) (A.subst σ) :=
    frame.guard.path.cast frame.guard.anchor.2.1
  have path := TypeRelated.literalPiBodyPath henv hTarget
    (by simpa only [SeededApplicationCodeInput.profile, subst] using functionAnswer.related)
    rawArgument
  simpa only [subst_inst, sameArgument] using path

end Lean4Lean.AnchoredSource.Adapted
