import Lean4Lean.Theory.Typing.AnchoredClosedTypeCertificate
import Lean4Lean.Theory.Typing.AnchoredNativeInitialObservation
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! A native observation retains a genuine closed source-type certificate.
It can be interpreted using the original header formation theorem and reused
in an enclosing source context without inventing variable requirements. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeConstantObservation.typeCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {demand : Profile n}
    (observation : NativeConstantObservation env U registry target name levels demand)
    (original : GradedJoint env U registry []
      (observation.signature.type.instL levels) (observation.signature.type.instL levels) (.sort level)) :
    TypeRelated env U registry target (observation.signature.type.instL levels)
      (observation.signature.type.instL levels) observation.typeSupport := by
  obtain ⟨_, typeWF⟩ := henv.constWF
    (observation.registered.recursorType observation.signature.typeOrigin)
  have closed := VExpr.WF.closedN henv ⟨_, typeWF⟩ trivial
  exact observation.typeCertificate.closedTypeCode henv hscoped hTarget closed.instL original

end Lean4Lean.AnchoredSource.Adapted
