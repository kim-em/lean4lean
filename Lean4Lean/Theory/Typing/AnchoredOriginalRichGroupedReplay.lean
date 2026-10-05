import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication

/-! Source variable and application reconstruction from a finite grouped
capture ledger. Semantic liveness is obtained from the selected original
whole-query alignment; resource membership is computed from the actual
finite groups. No query-synthesis callback is stored in the ledger. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem group_live
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : Need.mk n profile ∈ entries.needs) : Profile.Live env U registry target profile := by
  obtain ⟨_, _, _, _, _, _, _, related⟩ := entries.lookup henv formed member
  exact related.live henv hscoped formed

theorem RichGroupedCapture.variable
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (node : EndpointState headerEnv U (A :: headerSource) (.bvar 0) assigned)
    (member : Need.mk n profile ∈ entries.needs) :
    Nonempty (RichGradedResult headerEnv env U registry target node (Locals.push headerLocals)
      (declaredLeft.cons leftValue) (headerAvailable.push entries.needs) profile) := by
  exact ⟨{
    rank := n, bound := Nat.le_refl _, raw := profile,
    footprint := [(0, Need.mk n profile)]
    observation := .legacy (.legacy (.var _ _ 0 profile))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by intro i need hm; cases List.mem_singleton.mp hm; exact member
    live := group_live henv hscoped formed entries member }⟩

/-- The two grouped slots are consumed by an actual original structural
application. Each slot can contain queries from many source occurrences and
binder frames. No canonical source owner is chosen or relabelled. -/
theorem groupedCapture_application
    {domainF : EndpointRef headerEnv U headerSource F (.sort fLevel)}
    {domainA : EndpointRef headerEnv U (F :: headerSource) A (.sort aLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (functions : RichGroupedCapture (field := field) (major := major) domainF env registry target
      locals σ available ownerInitial rawFunction functionValue functionRight)
    (arguments : RichGroupedCapture (field := field) (major := major) domainA env registry target
      (Locals.push locals) (σ.cons functionValue) (available.push functions.needs)
      ownerInitial rawArgument argumentValue argumentRight)
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    (functionMember : Need.mk (n + 1) (Profile.fn key output) ∈ functions.needs)
    (argumentMember : Need.mk n rawInput ∈ arguments.needs)
    (domain : EndpointState headerEnv U (A :: F :: headerSource) D (.sort u))
    (codomain : EndpointState headerEnv U (D :: A :: F :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U (A :: F :: headerSource) (.bvar 1) (.forallE D B))
    (argument : EndpointState headerEnv U (A :: F :: headerSource) (.bvar 0) D)
    (result : EndpointState headerEnv U (A :: F :: headerSource) (B.inst (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key argumentValue argumentValue)
    (closed : ((available.push functions.needs).push arguments.needs).AtomClosed) :
    Nonempty (RichGradedResult headerEnv env U registry target
      (.app hu hv domain codomain function argument result) (Locals.push (Locals.push locals))
      ((σ.cons functionValue).cons argumentValue)
      ((available.push functions.needs).push arguments.needs) (.singleton output)) := by
  let functionResult : RichGradedResult headerEnv env U registry target function
      (Locals.push (Locals.push locals)) ((σ.cons functionValue).cons argumentValue)
      ((available.push functions.needs).push arguments.needs) (Profile.fn key output) := {
    rank := n + 1, bound := Nat.le_refl _, raw := Profile.fn key output
    footprint := [(1, Need.mk (n + 1) (Profile.fn key output))]
    observation := .legacy (.legacy (.var _ _ 1 (Profile.fn key output)))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by intro i need hm; cases List.mem_singleton.mp hm; exact functionMember
    live := group_live henv hscoped formed functions functionMember }
  let argumentResult : RichGradedResult headerEnv env U registry target argument
      (Locals.push (Locals.push locals)) ((σ.cons functionValue).cons argumentValue)
      ((available.push functions.needs).push arguments.needs) rawInput := {
    rank := n, bound := Nat.le_refl _, raw := rawInput
    footprint := [(0, Need.mk n rawInput)]
    observation := .legacy (.legacy (.var _ _ 0 rawInput))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by intro i need hm; cases List.mem_singleton.mp hm; exact argumentMember
    live := group_live henv hscoped formed arguments argumentMember }
  exact RichGradedResult.app henv hscoped formed closed domain codomain result hu hv
    functionResult argumentResult adapter admitted

/-- Reconstruct both the actual semantic frame and the application query from
its finite whole-cut groups. Every group entry retains its own valid original
frame; the returned frame charges their owner/domain bundles. -/
theorem groupedCapture_applicationFrame
    {sourceEnv : VEnv} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domainF : EndpointRef headerEnv U headerSource F (.sort fLevel)}
    {domainA : EndpointRef headerEnv U (F :: headerSource) A (.sort aLevel)}
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (sourceOrdered : sourceEnv.Ordered)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (functions : RichGroupedCapture (field := field) (major := major) domainF env registry target
      locals σ available ownerInitial rawFunction functionValue functionRight)
    (arguments : RichGroupedCapture (field := field) (major := major) domainA env registry target
      (Locals.push locals) (σ.cons functionValue) (available.push functions.needs)
      ownerInitial rawArgument argumentValue argumentRight)
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    (functionMember : Need.mk (n + 1) (Profile.fn key output) ∈ functions.needs)
    (argumentMember : Need.mk n rawInput ∈ arguments.needs)
    (domain : EndpointState headerEnv U (A :: F :: headerSource) D (.sort u))
    (codomain : EndpointState headerEnv U (D :: A :: F :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U (A :: F :: headerSource) (.bvar 1) (.forallE D B))
    (argument : EndpointState headerEnv U (A :: F :: headerSource) (.bvar 0) D)
    (result : EndpointState headerEnv U (A :: F :: headerSource) (B.inst (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key argumentValue argumentValue)
    (closed : ((available.push functions.needs).push arguments.needs).AtomClosed) :
    ∃ frame : OriginalRichFrame headerEnv env U registry target
      (.cons (.cons context domainF) domainA) (Locals.push (Locals.push locals))
      ((σ.cons functionValue).cons argumentValue) ((τ.cons functionRight).cons argumentRight)
      ((available.push functions.needs).push arguments.needs),
    Nonempty (RichGradedResult headerEnv env U registry target
      (.app hu hv domain codomain function argument result) (Locals.push (Locals.push locals))
      ((σ.cons functionValue).cons argumentValue)
      ((available.push functions.needs).push arguments.needs) (.singleton output)) := by
  refine ⟨(tail.group domainF sourceOrdered ownerInitial functions).group
    domainA sourceOrdered ownerInitial arguments, ?_⟩
  exact groupedCapture_application henv hscoped formed functions arguments
    functionMember argumentMember domain codomain function argument result hu hv adapter admitted closed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
