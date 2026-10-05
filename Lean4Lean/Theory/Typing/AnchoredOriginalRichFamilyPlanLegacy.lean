import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalConstructorSpine

/-! Attach a legacy family plan to the actual literal declaration telescope.
All original domain locations are computed from the retained header proof;
legacy certificates are embedded at those exact nodes without semantic calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private def castSpine
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {context : ContextDerivation headerEnv U source}
    {node : EndpointState headerEnv U source (wrapForalls first result) (.sort level)}
    (same : first = second)
    (spine : OriginalConstructorSpine (header := header) result context first node) :
    OriginalConstructorSpine (header := header) result context second
      (node.cast (congrArg (fun domains => wrapForalls domains result) same) rfl) := by
  cases same
  exact spine

theorem SortableFamilyPlan.atOriginalSpine
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {context : ContextDerivation headerEnv U source}
    {signature : ConstantTelescope declaredType}
    {node : EndpointState headerEnv U source
      (wrapForalls (signature.domains.drop arguments.length) signature.result) (.sort level)}
    (spine : OriginalConstructorSpine (header := header) signature.result context
      (signature.domains.drop arguments.length) node)
    (sourceEq : source = (signature.domains.take arguments.length).reverse)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) :
    Nonempty (RichFamilyPlan env U registry target header name levels signature context
      (nativeCaptureSubst arguments) arguments demand footprint) := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    have contextEq : source = signature.domains.reverse := by
      rw [sourceEq, saturated, List.take_length]
    exact ⟨.terminal saturated resultSort relevance (contextEq ▸ captures)⟩
  | .binder (domain := domain) (key := key) domainAt domainCode guard body pack covered =>
    have small := (List.getElem?_eq_some_iff.mp domainAt).1
    have selected := (List.getElem?_eq_some_iff.mp domainAt).2
    have rest : signature.domains.drop arguments.length =
        domain :: signature.domains.drop (arguments.length+1) := by
      rw [List.drop_eq_getElem_cons small, selected]
    have selectedSpine := castSpine rest spine
    cases selectedSpine with
    | binder hu hv route location lineage child =>
      have nextSource : domain :: source = (signature.domains.take (arguments ++ [key.anchor]).length).reverse := by
        simpa only [List.length_append, List.length_singleton, sourceEq] using
          (signature.prefixContext_cons domainAt).symm
      let childSpine := castSpine (show signature.domains.drop (arguments.length+1) =
        signature.domains.drop (arguments ++ [key.anchor]).length by simp) child
      have nextBody := SortableFamilyPlan.atOriginalSpine (arguments := arguments ++ [key.anchor])
        childSpine nextSource body
      obtain ⟨nextBody⟩ := nextBody
      exact ⟨.binder domainAt _ location lineage (.legacy domainCode) guard
        (by simpa only [nativeCaptureSubst_append] using nextBody) pack covered⟩
  | .view source change =>
    obtain ⟨source⟩ := SortableFamilyPlan.atOriginalSpine spine sourceEq source
    exact ⟨.view source change⟩
  | .pad source =>
    obtain ⟨source⟩ := SortableFamilyPlan.atOriginalSpine spine sourceEq source
    exact ⟨.pad source⟩
termination_by sizeOf plan

theorem SortableFamilyPlan.atOriginalHeader
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    (plan : SortableFamilyPlan env U registry target name levels signature [] demand []) :
    Nonempty (RichFamilyPlan env U registry target header name levels signature .nil
      (nativeCaptureSubst []) [] demand []) := by
  let node := (EndpointState.ref header).cast signature.type_eq rfl
  let location : Located header node := Located.here.castExpression signature.type_eq
  obtain ⟨spine⟩ := originalConstructorSpine (context := .nil) location (by
    rw [Located.castExpression_contextDerivation]; rfl)
  exact SortableFamilyPlan.atOriginalSpine
    (castSpine (show signature.domains = signature.domains.drop ([] : List VExpr).length by simp) spine) rfl plan

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
