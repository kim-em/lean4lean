import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureSubstitution

/-! Whole rich capture discovery. This is the query-dependent input ledger,
not an inverse-substitution certificate. In particular metadata is retained
in its original source context, even when the matched expression is lifted
from a smaller context. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

/-- A capture match keeps the complete original query. `metadata` distinguishes
assigned-type/formation children from ordinary expression children. -/
structure RichCaptureCut (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (arguments : List VExpr) where
  sourceEnv : VEnv
  source : List VExpr
  expression : VExpr
  assigned : VExpr
  node : EndpointState sourceEnv U source expression assigned
  locals : List Nat
  realization : Subst
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  observation : RichObs sourceEnv env U registry target node locals realization profile footprint
  depth : Nat
  index : Nat
  bound : index < arguments.length
  expression_eq : expression = arguments[arguments.length - 1 - index].lift' (.skipN .refl depth)
  metadata : Bool

def RichCaptureCut.need (cut : RichCaptureCut env U registry target arguments) : Nat × Need :=
  (cut.index, .mk cut.rank cut.profile)

/-- The original occurrence realizes precisely the selected simultaneous
capture slot. This equality does not retype the occurrence in a base context. -/
theorem RichCaptureCut.selected (cut : RichCaptureCut env U registry target arguments) :
    cut.expression = (VExpr.bvar (cut.depth + cut.index)).subst
      ((Subst.ofList arguments).liftN cut.depth) :=
  cut.expression_eq.trans (capture_selected arguments cut.depth cut.index cut.bound).symm

private noncomputable def matchCapture (arguments : List VExpr) (depth : Nat) (expression : VExpr) :
    Option { index : Fin arguments.length //
      expression = arguments[arguments.length - 1 - index.val].lift' (.skipN .refl depth) } := by
  classical
  exact if h : ∃ index : Fin arguments.length,
      expression = arguments[arguments.length - 1 - index.val].lift' (.skipN .refl depth)
    then some ⟨h.choose, h.choose_spec⟩ else none

mutual
noncomputable def RichCert.captureCuts
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (arguments : List VExpr) (depth : Nat) (metadata : Bool) :
    List (RichCaptureCut env U registry target arguments) :=
  match matchCapture arguments depth expression with
  | some selected => [⟨sourceEnv, source, expression, assigned, node, locals, σ, _, profile, footprint,
      .code certificate, depth, selected.val.val, selected.val.isLt, selected.property, metadata⟩]
  | none => match certificate with
    | .legacy _ => []
    | .observe observation _ => observation.captureCuts arguments depth metadata
    | .pi _ _ domain _ rows =>
      domain.captureCuts arguments depth metadata ++ rows.captureCuts arguments depth metadata
    | .route _ certificate => certificate.captureCuts arguments depth metadata
    | .union left right => left.captureCuts arguments depth metadata ++ right.captureCuts arguments depth metadata
    | .pad certificate | .down certificate | .map _ certificate | .support _ certificate |
      .select certificate _ => certificate.captureCuts arguments depth metadata

noncomputable def RichRows.captureCuts
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint)
    (arguments : List VExpr) (depth : Nat) (metadata : Bool) :
    List (RichCaptureCut env U registry target arguments) :=
  match rows with
  | .nil => []
  | .cons _ certificate _ _ tail =>
    certificate.captureCuts arguments (depth + 1) metadata ++ tail.captureCuts arguments depth metadata

noncomputable def RichObs.captureCuts
    {node : EndpointState sourceEnv U source expression assigned}
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (arguments : List VExpr) (depth : Nat) (metadata : Bool) :
    List (RichCaptureCut env U registry target arguments) :=
  match matchCapture arguments depth expression with
  | some selected => [⟨sourceEnv, source, expression, assigned, node, locals, σ, _, profile, footprint,
      observation, depth, selected.val.val, selected.val.isLt, selected.property, metadata⟩]
  | none => match observation with
    | .legacy _ => []
    | .canonicalConst .. | .canonicalDelta .. | .rigidFamily .. | .family .. | .constructor .. => []
    | .code certificate => certificate.captureCuts arguments depth metadata
    | .projection _ _ _ major field _ _ =>
      major.captureCuts arguments depth metadata ++ field.captureCuts arguments depth true
    | .projectionSortable _ _ _ major _ _ _ field _ =>
      major.captureCuts arguments depth metadata ++ field.captureCuts arguments depth true
    | .app _ _ fn arg _ _ => fn.captureCuts arguments depth metadata ++ arg.captureCuts arguments depth metadata
    | .lam _ _ domain _ body _ _ =>
      domain.captureCuts arguments depth true ++ body.captureCuts arguments (depth + 1) metadata
    | .route _ observation => observation.captureCuts arguments depth metadata
    | .union left right => left.captureCuts arguments depth metadata ++ right.captureCuts arguments depth metadata
    | .view observation _ | .action observation _ | .select observation _ |
      .pad observation | .unpad observation => observation.captureCuts arguments depth metadata
end

/-- Declaration captures are not ordinary typed substitution operands. A
parameter retains its actual projection declaration and position, and a prior
field retains `j < current`; neither constructor asserts a fabricated typing
of that value at the declared header domain. -/
inductive OriginalCaptureSlot (sourceEnv : VEnv) (U : Nat) (source : List VExpr) : VExpr → Type where
  | typed {argument A : VExpr} {u : VLevel}
      (domain : EndpointRef sourceEnv U source A (.sort u))
      (owner : EndpointState sourceEnv U source argument A) : OriginalCaptureSlot sourceEnv U source argument
  | parameter {name : Name} {index : Nat} {major assigned : VExpr}
      {node : EndpointState sourceEnv U source (.proj name index major) assigned}
      (head : ProjectionHead node) (position : Fin head.parameters.length) :
      OriginalCaptureSlot sourceEnv U source head.parameters[position.val]
  | priorField {name : Name} {index : Nat} {major assigned : VExpr}
      {node : EndpointState sourceEnv U source (.proj name index major) assigned}
      (head : ProjectionHead node) (position : Nat) (earlier : position < index) :
      OriginalCaptureSlot sourceEnv U source (.proj name position head.sourceMajor)

structure OriginalCaptureBinding (sourceEnv : VEnv) (U : Nat) (source : List VExpr) where
  expression : VExpr
  origin : OriginalCaptureSlot sourceEnv U source expression

abbrev OriginalCaptureGraph (sourceEnv : VEnv) (U : Nat) (source : List VExpr) :=
  List (OriginalCaptureBinding sourceEnv U source)

def OriginalCaptureGraph.arguments (graph : OriginalCaptureGraph sourceEnv U source) : List VExpr :=
  graph.map OriginalCaptureBinding.expression

/-- Discovery against an original graph retains the exact declared/typed role
of the selected slot. No original owner is invented for an unused prior field. -/
def RichCaptureCut.slot
    {sourceEnv : VEnv} {source : List VExpr}
    (graph : OriginalCaptureGraph sourceEnv U source)
    (cut : RichCaptureCut env U registry target graph.arguments) :
    OriginalCaptureSlot sourceEnv U source
      (graph.arguments[graph.arguments.length - 1 - cut.index]'(by have := cut.bound; omega)) := by
  have bound : graph.arguments.length - 1 - cut.index < graph.length := by
    simpa [OriginalCaptureGraph.arguments] using
      (show graph.arguments.length - 1 - cut.index < graph.arguments.length by have := cut.bound; omega)
  simpa only [OriginalCaptureGraph.arguments, List.getElem_map] using
    (graph[graph.arguments.length - 1 - cut.index]'bound).origin

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
