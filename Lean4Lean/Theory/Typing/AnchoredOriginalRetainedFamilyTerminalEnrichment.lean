import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientFamilyDescriptor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySeedConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth

/-! Rebuild a saturated retained family from the actual enlarged capture.
The complete input is selected from the captured ledger, so its original
query and declared-domain certificate are retained even when the old
codomain query did not use the parameter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The selected complete input yields an actual declared-domain certificate
and a concrete frozen request. Even an empty value input keeps the SAME
selected assigned support and its interpretation from the aligned answer. -/
theorem RichGroupedCapture.completeRequest
    {domain : EndpointRef headerEnv U headerSource C (.sort cu)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (present : (⟨n, input⟩ : Need) ∈ entries.needs) :
    ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain)
        headerLocals declaredLeft true (support : Profile n) footprint,
      footprint.Available headerAvailable ∧
      RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨⟨C.subst declaredLeft, leftValue, input⟩, support⟩ : DataRequest (Profile n))
        leftValue leftValue ∧
      ∃ entry ∈ entries, support.sortFlags = entry.answer.value.support.sortFlags := by
  obtain ⟨entry, member, support, footprint, certificate, resources, typed, related, code, flags, _⟩ :=
    RichGroupedCapture.lookup_supportedAllDepth henv formed entries present
  have raw := entry.answer.path.cast
    ((entry.owner.node.sound.defeq.mono below).substDF henv entry.substitutions.wf formed entry.substitutions)
  rw [entry.left_eq, entry.right_eq] at raw
  exact ⟨support, footprint, certificate, resources,
    ⟨raw.hasType.1, raw.hasType.1, typed, certificate.formed, code,
      related.left_diagonal, related.left_diagonal⟩, entry, member, flags⟩

/-- The final captured slot can rebuild both the native family terminal and
its original Pi header code. The descriptor contains the entire enlarged
input, rather than only the needs present in the old codomain footprint. -/
theorem RichGroupedCapture.oneParameterPlan
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {domain : EndpointRef headerEnv U [] C (.sort cu)}
    {body : EndpointState headerEnv U [C] signature.result (.sort dv)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (hcu : cu.WF U) (hdv : dv.WF U)
    (domains : signature.domains = [C])
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = .nil)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      [] realization (fun _ => []) ownerInitial rawCapture leftValue rightValue)
    (present : (⟨n, input⟩ : Need) ∈ entries.needs) :
    ∃ request : DataRequest (Profile n),
      request.input = input ∧ request.anchor = leftValue ∧
      (∃ entry ∈ entries, request.support.sortFlags = entry.answer.value.support.sortFlags) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target request leftValue leftValue ∧
      Nonempty (RichFamilyPlanResult env U registry target header name levels signature
        .nil (.pi hcu hdv (.ref domain) body) realization [] (fun _ => [])
        (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, levels, relevant, [request]⟩))) := by
  obtain ⟨support, footprint, certificate, resources, admission, retainedSupport⟩ :=
    entries.completeRequest henv hscoped below formed present
  let request : DataRequest (Profile n) := ⟨⟨C.subst realization, leftValue, input⟩, support⟩
  have anchor : Admitted env U registry target request.toKeyData leftValue leftValue :=
    ⟨admission.1, admission.2.1, support, admission.2.2.1, admission.2.2.2.1,
      admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.2⟩
  have guard : LambdaGuard env U registry target realization C request.toKeyData support :=
    ⟨admission.2.2.1, admission.2.2.2.1, .refl, admission.2.2.2.2.1, anchor⟩
  let needs : List Need := [⟨n, input⟩]
  let captures : FamilyCaptures env U registry target [C] [0]
      (realization.cons leftValue) [.bvar 0] [request] [(0, ⟨n, input⟩)] :=
    .cons .zero (.var [0] (realization.cons leftValue) 0 input) (.refl _) (by simpa only [lift_subst_cons] using (DomainChain.refl (env := env) (U := U) (registry := registry) (Γ := target) (input := input) (C.subst realization))) admission .nil
  have capturesAvailable : Footprint.Available [(0, ⟨n, input⟩)]
      (Valuation.push needs (fun _ => [])) := by
    intro i need member
    cases List.mem_singleton.mp member
    exact List.mem_singleton_self _
  let terminal := RichFamilyPlanResult.terminal (header := header) (name := name) (levels := levels)
    (context := ContextDerivation.cons .nil domain) (node := body) (arguments := [leftValue])
    (by simp only [List.length_singleton, domains]) resultSort relevance captures capturesAvailable
  have bounded : ∀ need ∈ needs, need.rank ≤ n+1 := by
    intro need member
    cases List.mem_singleton.mp member
    exact Nat.le_succ _
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade (n+1)).atoms,
      atom ∈ (Key.pad request.toKeyData).input.atoms := by
    intro need member atom atomMember
    cases List.mem_singleton.mp member
    simpa only [Need.atGrade, dif_pos (Nat.le_succ n),
      raiseProfile_step (Nat.le_refl n), raiseProfile_self, Key.pad, request] using atomMember
  have raisedGuard := guard.raise henv (Nat.le_succ n)
  simp only [raiseKey_step (Nat.le_refl n), raiseKey_self,
    raiseProfile_step (Nat.le_refl n), raiseProfile_self] at raisedGuard
  obtain ⟨plan⟩ := RichFamilyPlanResult.binder (header := header) (signature := signature) (arguments := []) hcu hdv
    (by simp only [List.length_nil, domains, List.getElem?_cons_zero]) location lineage
    certificate.pad resources raisedGuard needs bounded covered terminal
  exact ⟨request, rfl, rfl, retainedSupport, admission, ⟨plan⟩⟩

private theorem oneDomain_eq
    (signature : ConstantTelescope expression) (domains : signature.domains = [C]) :
    expression = .forallE C signature.result := by
  simpa only [domains, wrapForalls, List.foldr_cons, List.foldr_nil]
    using signature.type_eq

/-- Apply the rebuilt native family to the actual stronger original argument
query. The retained header origin and seed universes are unchanged. This is
an actual source observation, not only a semantic descriptor admission. -/
theorem RetainedRichFamilySeed.oneParameterApplication
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (seed : RetainedRichFamilySeed root env registry target name levels)
    {sourceDomain : EndpointState sourceEnv U source A (.sort u)}
    {sourceBody : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {headerDomain : EndpointRef seed.origin.source U [] C (.sort cu)}
    {headerBody : EndpointState seed.origin.source U [C] seed.signature.result (.sort dv)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (hu : u.WF U) (hv : v.WF U) (hcu : cu.WF U) (hdv : dv.WF U)
    (domains : seed.signature.domains = [C])
    (resultSort : seed.signature.result = .sort level) (relevance : Relevant level relevant)
    (location : Located (seed.origin.familyHeader seed.seedWF).reference (.ref headerDomain))
    (lineage : location.contextDerivation .nil = .nil)
    (route : PrefixRoute seed.origin.source U [] (.forallE C seed.signature.result)
      ((EndpointState.ref (seed.origin.familyHeader seed.seedWF).reference).cast
        (oneDomain_eq seed.signature domains) rfl)
      (.pi hcu hdv (.ref headerDomain) headerBody))
    (entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
      [] realization (fun _ => []) ownerInitial rawCapture leftValue rightValue)
    (present : (⟨n, input⟩ : Need) ∈ entries.needs)
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available input)
    (anchorEq : leftValue = a.subst σ) :
    ∃ request : DataRequest (Profile n),
      request.input = input ∧ request.anchor = a.subst σ ∧
      (∃ entry ∈ entries, request.support.sortFlags = entry.answer.value.support.sortFlags) ∧
      Nonempty (RichGradedResult sourceEnv env U registry target
        (.app hu hv sourceDomain sourceBody function argument result) locals σ available
        (.singleton (n := n+1) (.family ⟨name, seed.seed, relevant, [request]⟩))) := by
  obtain ⟨request, inputEq, requestAnchor, retainedSupport, admission, ⟨plan⟩⟩ :=
    entries.oneParameterPlan (header := (seed.origin.familyHeader seed.seedWF).reference)
      (signature := seed.signature) (name := name) (levels := seed.seed)
      (body := headerBody) henv hscoped below formed hcu hdv domains resultSort relevance
      location lineage present
  let originalPlan := plan.restoreRoute route
  have footprintEmpty : originalPlan.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨i, need⟩ member
    exact nomatch originalPlan.resources i need member
  have typeEmpty : originalPlan.typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨i, need⟩ member
    exact nomatch originalPlan.typeResources i need member
  let observation : RichObs sourceEnv env U registry target function locals σ
      (Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)) [] :=
    .family seed.origin seed.lookup seed.notDefinition seed.notNative seed.notQuotient
      seed.seedWF seed.seedLength seed.levelsWF seed.equivalent seed.signature seed.typeClosed
      (by simpa only [List.length_nil, List.range_zero, typeEmpty] using RichCert.ofCast (oneDomain_eq seed.signature domains) rfl originalPlan.certificate)
      originalPlan.typed (by simpa only [footprintEmpty, Profile.fn] using originalPlan.plan)
  have admitted : Admitted env U registry target request.toKeyData leftValue leftValue :=
    ⟨admission.1, admission.2.1, request.support, admission.2.2.1, admission.2.2.2.1,
      admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.2⟩
  have padded := Admitted.pad henv admitted
  have anchorAdmitted : Admitted env U registry target (Key.pad request.toKeyData)
      (Key.pad request.toKeyData).anchor (Key.pad request.toKeyData).anchor := by
    simpa only [Key.pad, requestAnchor] using padded
  let functionQuery : RichGradedResult sourceEnv env U registry target function locals σ available
      (Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)) := {
    rank := n+2
    bound := Nat.le_refl _
    raw := Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)
    footprint := []
    observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ impossible => nomatch impossible
    live := Profile.Live.singleton_iff.mpr ⟨anchorAdmitted, trivial⟩ }
  obtain ⟨output⟩ := RichGradedResult.app henv hscoped formed closed sourceDomain sourceBody result hu hv
    functionQuery (argumentQuery.pad henv hscoped formed)
    (by change GeneralNormalProfileAdapter env U registry target input.pad request.input.pad
        rw [inputEq]; exact .refl _)
    (by simpa only [anchorEq] using padded)
  exact ⟨request, inputEq, requestAnchor.trans anchorEq, retainedSupport, ⟨output⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
