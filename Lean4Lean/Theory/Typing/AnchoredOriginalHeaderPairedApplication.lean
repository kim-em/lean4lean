import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain
import Lean4Lean.Theory.Typing.AnchoredSortableApplicationCode
import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterNormalization

/-! Actual paired body reconstruction under captured and fresh header binders.
The application admission at the right realization is derived from the
original function/argument slots. No body semantic clause is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Actual variable-body transfer uses the same retained header slot on
both sides, even when that slot is a newly admitted Pi argument. -/
theorem HeaderBinderFrame.pairedVariableCode
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (node : EndpointState headerEnv U headerSource (.bvar index) (.sort level))
    (profileFormed : profile.HasType (.sort relevant))
    (member : Need.mk n profile ∈ available index)
    (lookup : Lookup headerSource index sourceType) :
    Nonempty (RichCodeTransferResult env U registry target node node locals left right available relevant profile) := by
  obtain ⟨entry⟩ := frame.lookup henv formed member lookup
  exact ⟨{
    footprint := [(index, Need.mk n profile)]
    certificate := .legacy (.seed (.var locals right index profile) profileFormed)
    resources := by intro i need h; cases List.mem_singleton.mp h; exact member
    related := entry.related.code_of_sortable henv hscoped formed profileFormed }⟩

/-- Every finite code wrapper transports a computed paired answer and
constructs its right-hand source certificate. This includes cross-grade
sort/family padding, support transforms and minimal-support focus. -/
theorem RichCodeTransferResult.codeAction
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (result : RichCodeTransferResult env U registry target leftNode rightNode rightLocals
      σ τ available relevant profile)
    (action : SortableCodeAction env U registry target relevant profile next output) :
    Nonempty (RichCodeTransferResult env U registry target leftNode rightNode rightLocals
      σ τ available next output) := by
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := result.certificate.codeAction action result.resources
  exact ⟨⟨footprint, certificate, resources, action.codeMap henv hscoped result.related⟩⟩

theorem HeaderBinderFrame.pairedCapturedApplication
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (node : EndpointState headerEnv U headerSource
      (.app (.bvar functionIndex) (.bvar argumentIndex)) assigned)
    (key : Key n) (output : Atom n)
    (outputFormed : (Profile.singleton output).HasType (.sort relevant))
    (functionNeed : Need.mk (n + 1) (Profile.fn key output) ∈ available functionIndex)
    (functionLookup : Lookup headerSource functionIndex (.forallE A B))
    (rawInput : Profile n)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (argumentNeed : Need.mk n rawInput ∈ available argumentIndex)
    (argumentLookup : Lookup headerSource argumentIndex A)
    (admitted : Admitted env U registry target key (left argumentIndex) (left argumentIndex)) :
    ∃ footprint, Nonempty (RichCert headerEnv env U registry target node locals right relevant
      (.singleton output) footprint) ∧ footprint.Available available ∧
      TypeRelated env U registry target (.app (left functionIndex) (left argumentIndex))
        (.app (right functionIndex) (right argumentIndex)) (.singleton output) := by
  obtain ⟨functionEntry⟩ := frame.lookup henv formed functionNeed functionLookup
  obtain ⟨argumentEntry⟩ := frame.lookup henv formed argumentNeed argumentLookup
  have functionValue : Related env U registry target (left functionIndex) (right functionIndex)
      (.forallE (A.subst left) (B.subst left.lift)) (Profile.fn key output) functionEntry.support := by
    simpa only [subst] using functionEntry.related
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have sourceCode := (bridge.symm henv inputTyped.wf_type).left_diagonal
  have keyCode := bridge.left_diagonal
  have adapted := arguments.termMap henv hscoped formed inputTyped sourceCode argumentEntry.related
  have paired := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have pairedRaw := path.symm.cast (substitutions.lookup argumentLookup)
  obtain ⟨anchorRaw, _, oldSupport, _, _, _, anchor, _⟩ := admitted
  have anchor' := Related.retag henv inputTyped keyCode anchor
  have pairAdmission : Admitted env U registry target key (left argumentIndex) (right argumentIndex) :=
    ⟨anchorRaw, pairedRaw, support, inputTyped, supportFormed, keyCode, anchor', paired⟩
  have rightAnchor := Related.trans henv hscoped anchor' paired
  have rightSelf := (Related.symm henv rightAnchor).left_diagonal
  have rightAdmission : Admitted env U registry target key (right argumentIndex) (right argumentIndex) :=
    ⟨anchorRaw.trans pairedRaw, pairedRaw.hasType.2, support, inputTyped, supportFormed,
      keyCode, rightAnchor, rightSelf⟩
  have result := Related.applicationCode henv hscoped formed outputFormed functionValue pairAdmission
  let footprint : Footprint := [(functionIndex, Need.mk (n + 1) (Profile.fn key output))] ++
    [(argumentIndex, Need.mk n rawInput)]
  let certificate : RichCert headerEnv env U registry target node locals right relevant
      (.singleton output) footprint :=
    .legacy (.observe (.app (.legacy (.var locals right functionIndex _))
      (.legacy (.var locals right argumentIndex _)) arguments rightAdmission) outputFormed)
  refine ⟨footprint, ⟨certificate⟩, ?_, result⟩
  intro index need member
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    exact functionNeed
  · cases List.mem_singleton.mp member
    exact argumentNeed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
