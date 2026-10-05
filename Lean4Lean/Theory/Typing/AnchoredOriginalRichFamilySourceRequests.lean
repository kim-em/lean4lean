import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay

/-! Exact source requests through the consumed native family's finite code
adapter. The actual original argument endpoint survives padding and all
family-preserving code actions; descriptors are not identified syntactically. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def RichFamilySourceRequest
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (request : DataRequest (Profile n)) : Prop :=
  env.IsDefEq U target request.anchor (expression.subst σ) request.domain ∧
    Nonempty (RichFamilyArgumentQuery root env registry target source locals σ available expression request.input)

def RichFamilyRequestProperty
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (family : FamilyData (Profile n)) : Prop :=
  family.name = name ∧ List.Forall₂ (· ≈ ·) family.levels levels ∧
    List.Forall₂ (RichFamilySourceRequest root env registry target locals σ available) arguments family.arguments

theorem RichFamilySourceCapture.sourceRequest
    (capture : RichFamilySourceCapture root env registry target locals σ available arguments expression request) :
    RichFamilySourceRequest root env registry target locals σ available
      (expression.subst (nativeCaptureSubst arguments)) request := by
  rcases capture with ⟨index, rfl, bound, argument, anchor⟩
  simpa only [subst_bvar, nativeCaptureSubst, dif_pos bound] using
    (show RichFamilySourceRequest root env registry target locals σ available
      (arguments[arguments.length-1-index]'(by omega)) request from ⟨anchor, ⟨argument⟩⟩)

theorem RichFamilyConsumedCaptures.observations
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {consumed : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments requested}
    (packet : RichFamilyConsumedCaptures consumed) :
    List.Forall₂ (RichFamilySourceRequest root env registry target locals σ available)
      arguments packet.requests := by
  have sources := packet.sources
  have converted : List.Forall₂ (RichFamilySourceRequest root env registry target locals σ available)
      ((constantCaptureVariables consumed.anchors.length).map (·.subst (nativeCaptureSubst arguments)))
      packet.requests := by
    exact List.forall₂_map_left_iff.mpr (Lean4Lean.List.Forall₂.imp (fun _ _ source =>
      (Classical.choice source).sourceRequest) sources)
  rw [consumed.length] at converted
  have exactArguments :
      (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) = arguments := by
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
  rwa [exactArguments] at converted

theorem RichFamilySourceRequest.pad
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (request : RichFamilySourceRequest root env registry target locals σ available expression input) :
    RichFamilySourceRequest root env registry target locals σ available expression
      (input.map id Profile.pad) := by
  obtain ⟨path, ⟨argument⟩⟩ := request
  exact ⟨path, ⟨{ argument with query := argument.query.pad henv hscoped formed }⟩⟩

theorem RichFamilyRequestProperty.pad
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (property : RichFamilyRequestProperty root env registry target locals σ available name levels arguments family) :
    RichFamilyRequestProperty root env registry target locals σ available name levels arguments family.pad := by
  refine ⟨property.1, property.2.1, ?_⟩
  exact List.forall₂_map_right_iff.mpr (Lean4Lean.List.Forall₂.imp
    (fun _ _ head => head.pad henv hscoped formed) property.2.2)

/-- Family-preserving code programs transport the actual source requests.
The requested tuple may differ from the terminal tuple, including its grade. -/
theorem RichFamilyPlanConsumption.familyRequests
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (consumed : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n+1) (.family demand)) :
    RichFamilyRequestProperty root env registry target locals σ available name levels arguments demand := by
  obtain ⟨packet⟩ := consumed.familySourceCaptures henv hscoped formed
  have sourceProperty : RichFamilyRequestProperty root env registry target locals σ available name levels arguments
      ⟨name, levels, packet.relevant, packet.requests⟩ :=
    ⟨rfl, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl), packet.observations⟩
  have raised := (FamilyAtomProperty.raise_iff
    (property := RichFamilyRequestProperty root env registry target locals σ available name levels arguments)
    packet.bound (.family ⟨name, levels, packet.relevant, packet.requests⟩)).mpr sourceProperty
  have result := GeneralNormalAtomAdapter.familyProperty packet.adapter
    (property := RichFamilyRequestProperty root env registry target locals σ available name levels arguments)
    (fun source => source.pad henv hscoped formed) raised
  exact (FamilyAtomProperty.raise_iff consumed.bound (.family demand)).mp result

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
