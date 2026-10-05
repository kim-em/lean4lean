import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalLocatedDirect

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Only the earlier-header R edge of the actual primitive constant. -/
def PrimitiveHeaderCalls (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (locals : List Nat) (σ headerRealization : Subst) (available : Valuation) : Prop :=
  match reference with
  | .left (.constDF lookup wf otherWF count equiv levelWF closed ambient)
  | .right (.constDF lookup wf otherWF count equiv levelWF closed ambient) =>
    richSchedule .expressionReindex
      ((Closure.close (ambient.dependencyOrigin ordered) captured).cost +
       (Closure.close ((selectOriginalHeader ordered lookup wf).original.dependencyOrigin
         (selectOriginalHeader ordered lookup wf).ordered) []).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.constDF lookup wf otherWF count equiv levelWF closed ambient).dependencyOrigin ordered)
          captured).cost →
      RichCodeTransfer env U registry target (.ref (.left ambient))
        (.ref (.left (selectOriginalHeader ordered lookup wf).original))
        locals [] σ headerRealization available (fun _ => [])
  | _ => True

structure RichHeaderSelection (sourceEnv : VEnv) (U : Nat) (name : Name) (levels : List VLevel)
    (ordered : sourceEnv.Ordered) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  seed : List VLevel
  seedWF : ∀ level ∈ seed, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seed levels

noncomputable def RichHeaderSelection.header
    (selection : RichHeaderSelection sourceEnv U name levels ordered) :=
  selectOriginalHeader ordered selection.lookup selection.seedWF

theorem primitiveHeaderTransfer
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive)
    (calls : PrimitiveHeaderCalls env registry target ordered captured reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      RichCodeTransfer env U registry target reference.typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      refine ⟨⟨_, lookup, _, wf, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)⟩, ?_⟩
      intro relevant n profile footprint certificate resources
      exact replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient captured certificate resources calls
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      refine ⟨⟨_, lookup, _, wf, equiv⟩, ?_⟩
      intro relevant n profile footprint certificate resources
      exact replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient captured certificate resources calls

/-- Compute the actual constant packet and direct route from Located
provenance, then replay every query to its retained earlier original header. -/
theorem locatedConstantTransfer
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels) node
        (.ref (constantPrefix node).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix node).reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      RichCodeTransfer env U registry target node.typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  let packet := constantPrefix node
  obtain ⟨route⟩ := packet.directLocated location
  obtain ⟨selection, finish⟩ := primitiveHeaderTransfer ordered captured packet.reference rfl packet.primitive headerCalls
  exact ⟨selection, route.peelCode henv ordered captured (prefixCalls route) finish⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
