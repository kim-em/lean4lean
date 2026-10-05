import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDisplays
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! A query-selected generated Pi body reconstructs a real source row.
Fresh binder caps keep the frozen row input unchanged; all additional
captured resources remain in the computed outer footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem lift_comp (raw commonLeft : Subst) (anchor : VExpr) :
    raw.lift.comp (commonLeft.cons anchor) = (raw.comp commonLeft).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

/-- This constructs the actual rich row at the destination's retained
original body. The only input query is the recursive body reply; no new
source typing at the displayed common annotation is asserted. -/
theorem CappedGeneratedQueryReply.piRow
    {base : OriginalCaptureBase env U registry target}
    {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.pi hu hv (.ref domain) body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (annotationEq : annotation = A.subst raw)
    (bodyEq : displayedBody = B.subst raw.lift)
    (henv : env.Ordered)
    (key : Key n) (ambient output : Profile n)
    (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key ambient)
    (sorted : output.HasType (.sort relevant))
    (answer : CappedGeneratedQueryReply base (commonCaps.push (Need.Fits key.input))
      (OriginalNestedDisplay.piBody location initial graph annotationEq bodyEq)
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) output) :
    ∃ outside, Nonempty (RichRows sourceEnv env U registry target (.ref domain) body
      (graph.locals base.locals) (raw.comp commonLeft) relevant ambient [(key, output)] outside) ∧
      outside.Available (fun index => answer.reply.available (index + 1)) := by
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := answer.reply.query.code henv sorted
  have localsEq : answer.reply.locals = Locals.push (graph.locals base.locals) := answer.reply.locals_eq
  have bodyCertificate : RichCert sourceEnv env U registry target body
      (Locals.push (graph.locals base.locals)) ((raw.comp commonLeft).cons key.anchor)
      relevant output footprint := by
    change RichCert sourceEnv env U registry target body answer.reply.locals
      (raw.lift.comp (commonLeft.cons key.anchor)) relevant output footprint at certificate
    simpa only [localsEq, lift_comp] using certificate
  obtain ⟨packed, outside, pack, covered, available⟩ := answer.capped.packBody resources
  refine ⟨outside, ?_, available⟩
  exact ⟨by simpa only [List.append_nil] using
    RichRows.cons guard bodyCertificate pack covered (RichRows.nil)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
