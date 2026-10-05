import Lean4Lean.Theory.Typing.AnchoredNativeConstantTree

/-! The integrated mutual native syntax carries the exact finite children
used by the native replay construction. These structural projections neither
interpret those children nor replace them with synthesized observations. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {data : NativeRecursorData}

noncomputable def NativeCaptures.toSupport
    {program : SaturatedProgram data} {witnesses : List VExpr}
    {index : Nat} {required native : Footprint}
    (captures : NativeCaptures env U registry target program witnesses index required native) :
    NativeCaptureSupport env U registry target program witnesses index required native := by
  match captures with
  | .prefix required => exact .prefix required
  | .index naturalCertificate naturalResources declaredCertificate declaredResources
      naturalTyped declaredTyped alignment declaredCode nativeValue copiedValue pack covered previous =>
    exact .index {
      naturalSupport := _
      declaredSupport := _
      naturalFootprint := _
      naturalCertificate := naturalCertificate
      naturalResources := naturalResources
      declaredFootprint := _
      declaredCertificate := declaredCertificate
      declaredResources := declaredResources
      naturalTyped := naturalTyped
      declaredTyped := declaredTyped
      alignment := alignment
      declaredCode := declaredCode }
      nativeValue copiedValue pack covered previous.toSupport
  | .proof instruction captured sourceProof domainProof inhabitant pack previous =>
    exact .proof instruction captured sourceProof domainProof inhabitant pack previous.toSupport
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

noncomputable def NativePlan.toTree
    {levels : List VLevel} {signature : NativeConstantSignature data levels}
    {arguments : List VExpr} {demand : Profile n} {footprint : Footprint}
    (plan : NativePlan env U registry target signature arguments demand footprint) :
    NativeTelescopeTree env U registry target signature arguments demand footprint := by
  match plan with
  | .terminal program selected _ _ saturated noTrailing prefix_eq witnesses witnessLength
      witnessPrefix argumentAlignment argumentsEq body captures =>
    exact .terminal {
      program := program
      selected := selected
      saturated := saturated
      noTrailing := noTrailing
      prefix_eq := prefix_eq
      witnesses := witnesses
      witnessLength := witnessLength
      witnessPrefix := witnessPrefix
      argumentAlignment := argumentAlignment
      arguments_eq := argumentsEq
      bodyFootprint := _
      body := body
      captures := captures.toSupport }
  | .binder domainOrigin domainCode guard body pack covered =>
    exact .binder domainOrigin domainCode guard body.toTree pack covered
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
