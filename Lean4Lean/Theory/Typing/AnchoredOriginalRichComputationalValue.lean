import Lean4Lean.Theory.Typing.AnchoredOriginalRichValueInduction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain

/-! The paired computational F answer retains both channels: the original
assigned-type support on the left, and a concrete query at the same original
expression on the right. A value-only answer cannot supply the latter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure RichComputationalValue
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {value assigned : VExpr}
    (owner : EndpointState sourceEnv U source value assigned)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (input : Profile n)
    extends RichSupportedValue sourceEnv env U registry target owner locals σ τ available input where
  rightQuery : RichGradedResult sourceEnv env U registry target owner locals τ available input

def HeaderComputationalInductionAt
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    {headerSource : List VExpr} (context : ContextDerivation headerEnv U headerSource)
    (node : EndpointState headerEnv U headerSource expression assigned) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : HeaderBinderFrame header field major env registry target context locals σ τ available,
    (Closure.close (node.dependencyOrigin hf) (frame.dependencyEnvironment hf sf initial)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ headerSource →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs headerEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue headerEnv env U registry target node locals σ τ available profile)

theorem HeaderComputationalInductionAt.value
    (induction : HeaderComputationalInductionAt header field major env registry hf sf initial context node limit) :
    HeaderValueInductionAt header field major env registry hf sf initial context node limit := by
  intro target locals σ τ available frame bound closed formed substitutions n profile footprint query resources
  obtain ⟨answer⟩ := induction target locals σ τ available frame bound closed formed substitutions query resources
  exact ⟨answer.toRichSupportedValue⟩

theorem RichComputationalValue.code
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)
    (sorted : profile.HasType (.sort relevant)) :
    Nonempty (RichCodeTransferResult env U registry target node node locals σ τ available relevant profile) := by
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := answer.rightQuery.code henv sorted
  exact ⟨⟨footprint, certificate, resources, answer.related.code_of_sortable henv hscoped formed sorted⟩⟩

theorem HeaderComputationalInductionAt.code
    {node : EndpointState headerEnv U headerSource expression (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (induction : HeaderComputationalInductionAt header field major env registry hf sf initial context node limit) :
    HeaderCodeInductionAt header field major env registry hf sf initial context node limit := by
  intro target locals σ τ available frame bound closed formed substitutions relevant n profile footprint query resources
  obtain ⟨answer⟩ := induction target locals σ τ available frame bound closed formed substitutions (.code query) resources
  exact answer.code henv hscoped formed query.formed

def RichComputationalValue.empty :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available (.empty : Profile n) :=
  { RichSupportedValue.empty with rightQuery := .empty }

noncomputable def RichComputationalValue.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : RichComputationalValue sourceEnv env U registry target node locals σ τ available p)
    (right : RichComputationalValue sourceEnv env U registry target node locals σ τ available q) :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available (p.union q) :=
  { left.toRichSupportedValue.union henv right.toRichSupportedValue with
    rightQuery := left.rightQuery.union henv hscoped formed right.rightQuery }

theorem RichComputationalValue.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (.singleton original))
    (path : GeneralOutputPath env U registry target original output) :
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available (.singleton output)) := by
  obtain ⟨value⟩ := answer.toRichSupportedValue.outputPath henv hscoped formed path
  obtain ⟨query⟩ := answer.rightQuery.outputPath henv hscoped formed path
  exact ⟨{ value with rightQuery := query }⟩

/-- The right application guard is obtained from the paired argument F
answer and the actual function's domain alignment, not copied from the left. -/
theorem RichBinderValue.applicationAdmissions
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (functionAnswer : RichBinderValue sourceEnv env U registry target function locals σ τ available
      (Profile.fn (key : Key n) output))
    (argumentAnswer : RichBinderValue sourceEnv env U registry target argument locals σ τ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target (a.subst σ) (a.subst τ) (A.subst σ))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Admitted env U registry target key (a.subst σ) (a.subst τ) ∧
      Admitted env U registry target key (a.subst τ) (a.subst τ) := by
  have functionValue : Related env U registry target (f.subst σ) (f.subst τ)
      (.forallE (A.subst σ) (B.subst σ.lift)) (Profile.fn key output) functionAnswer.support := by
    simpa only [subst] using functionAnswer.related
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have sourceCode := (bridge.symm henv inputTyped.wf_type).left_diagonal
  have keyCode := bridge.left_diagonal
  have adapted := arguments.termMap henv hscoped formed inputTyped sourceCode argumentAnswer.related
  have paired := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have pairedRaw := path.symm.cast raw
  obtain ⟨anchorRaw, _, _, _, _, _, anchor, _⟩ := admitted
  have anchor' := Related.retag henv inputTyped keyCode anchor
  have rightAnchor := Related.trans henv hscoped anchor' paired
  have rightSelf := (Related.symm henv rightAnchor).left_diagonal
  exact ⟨⟨anchorRaw, pairedRaw, support, inputTyped, supportFormed, keyCode, anchor', paired⟩,
    ⟨anchorRaw.trans pairedRaw, pairedRaw.hasType.2, support, inputTyped, supportFormed,
      keyCode, rightAnchor, rightSelf⟩⟩

/-- General paired application uses the left original result support and
reconstructs its right observer from the two actual computational children. -/
theorem RichComputationalValue.apply_nativeDepth
    {n : Nat} {output : Atom n} {key : Key n} {rawInput : Profile n}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (left : RichSupportedValue sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ σ available (.singleton output))
    (functionAnswer : RichComputationalValue sourceEnv env U registry target function locals σ τ available
      (Profile.fn (key : Key n) output))
    (argumentAnswer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target (a.subst σ) (a.subst τ) (A.subst σ))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ τ available (.singleton output),
      (∀ current, answer.rightQuery.observation.nativeDepth current =
        max (functionAnswer.rightQuery.observation.nativeDepth current)
          (argumentAnswer.rightQuery.observation.nativeDepth current)) ∧
      (∀ current, answer.certificate.nativeDepth current = left.certificate.nativeDepth current) := by
  obtain ⟨paired, right⟩ := functionAnswer.toRichBinderValue.applicationAdmissions henv hscoped formed
    argumentAnswer.toRichBinderValue arguments raw admitted
  obtain ⟨rightQuery, rightDepth⟩ := RichGradedResult.app_nativeDepth henv hscoped formed closed domain body result hu hv
    functionAnswer.rightQuery argumentAnswer.rightQuery arguments right
  refine ⟨{ left with rightQuery := rightQuery, related := ?_ }, rightDepth, fun _ => rfl⟩
  simpa only [subst, subst_inst, inst_lift_cons] using
    Related.apply (B := B.subst σ.lift) henv hscoped formed left.typed
      (by simpa only [subst_inst, inst_lift_cons] using left.typeCode)
      (by simpa only [subst] using functionAnswer.related) paired

theorem RichComputationalValue.apply
    {n : Nat} {output : Atom n} {key : Key n} {rawInput : Profile n}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (left : RichSupportedValue sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ σ available (.singleton output))
    (functionAnswer : RichComputationalValue sourceEnv env U registry target function locals σ τ available
      (Profile.fn (key : Key n) output))
    (argumentAnswer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target (a.subst σ) (a.subst τ) (A.subst σ))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Nonempty (RichComputationalValue sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ τ available (.singleton output)) := by
  obtain ⟨answer, _, _⟩ := RichComputationalValue.apply_nativeDepth henv hscoped formed closed domain body result hu hv
    left functionAnswer argumentAnswer arguments raw admitted
  exact ⟨answer⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
