import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredNativePrefixFits

/-! Variable transfer reads the actual retained context entry and invokes
formation only at its original earlier-domain occurrence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- These calls range only over the finite original source context spine. -/
def OriginalTail.ContextHereditaryFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {tailSource : List VExpr} (tail : ContextDerivation sourceEnv U tailSource)
    {A : VExpr} {level : VLevel} (domain : EndpointRef sourceEnv U tailSource A (.sort level)),
    ContextDerivation.Location context tail domain →
    StateHereditaryFundamental env registry tail (.ref domain)

theorem OriginalTail.contextDomain_variable_schedule
    {context : ContextDerivation sourceEnv U source}
    {tail : ContextDerivation sourceEnv U tailSource}
    {domain : EndpointRef sourceEnv U tailSource A (.sort level)}
    (location : ContextDerivation.Location context tail domain)
    (lookup : Lookup source index sourceType) (levelWF : occurrenceLevel.WF U)
    (formation : EndpointState sourceEnv U source sourceType (.sort occurrenceLevel)) :
    (Closure.close domain.origin tail.closures).cost <
      (Closure.close (EndpointState.bvar lookup levelWF formation).origin context.closures).cost :=
  variable_lookup _ location.captured_member

private theorem variableLeaf
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (demand : Profile n) (member : (⟨n, demand⟩ : Need) ∈ available index) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  obtain ⟨entry⟩ := fits.forward.lookup henv hTarget member lookup
  have actualLocation : ContextDerivation.Location context entry.tailFits.contextDerivation entry.originalDomain :=
    by simpa only [fits.forwardContext] using entry.originalLocation
  have original := domains entry.tailFits.contextDerivation entry.originalDomain actualLocation
  have tailClosed : entry.tailAvailable.AtomClosed := by
    intro i need hm selected hs
    rw [entry.available_eq] at hm ⊢
    exact closed _ _ hm selected hs
  have raw : Ctx.SubstEq env U target entry.tailLeft entry.tailRight entry.tailSource := by
    have h : Ctx.SubstEq env U target σ τ ((entry.front ++ [entry.domain]) ++ entry.tailSource) := by
      simpa only [List.append_assoc, List.singleton_append] using entry.source_eq ▸ substitutions
    have h := Lean4Lean.AnchoredSource.Adapted.Ctx.SubstEq.nativePrefix h
    simpa only [List.length_append, List.length_singleton, ← entry.index_eq,
      entry.left_eq, entry.right_eq] using h
  obtain ⟨typeAnswer⟩ := original.sortable henv hscoped target entry.tailLocals
    entry.tailLeft entry.tailLeft entry.tailAvailable tailClosed hTarget raw.left
    (SortableTailPairedFits.diagonal entry.tailFits.contextDerivation entry.tailFits.left)
    entry.certificate entry.resources
  have typeEq : entry.domain.lift' (.skipN .refl (index + 1)) = A :=
    (lift'_consN_skipN (k := 0)).trans entry.sourceType_eq.symm
  let certificate := entry.certificate.renameSource (.skipN .refl (index + 1)) σ entry.left_eq locals
  have resources : (entry.footprint.sourceLift (.skipN .refl (index + 1))).Available available := by
    intro i need hm
    obtain ⟨⟨j, originalNeed⟩, hm, equal⟩ := List.mem_map.mp hm
    cases equal
    have resource := entry.resources j need hm
    simpa only [entry.available_eq, Lift.liftVar_skipN, Lift.liftVar, Nat.zero_add] using resource
  have typeCode : TypeRelated env U registry target (A.subst σ) (A.subst σ) entry.support := by
    have realized : A.subst σ = entry.domain.subst entry.tailLeft := by
      calc
        _ = (entry.domain.lift' (.skipN .refl (index + 1))).subst σ := congrArg (VExpr.subst · σ) typeEq.symm
        _ = _ := by rw [subst_lift', entry.left_eq]
    simpa only [realized] using typeAnswer.related
  have related : Related env U registry target ((VExpr.bvar index).subst σ)
      ((VExpr.bvar index).subst τ) (A.subst σ) demand entry.support := entry.related
  exact ⟨{
    rank := n, bound := Nat.le_refl _, raw := demand,
    footprint := [(index, ⟨n, demand⟩)], observation := .legacy (.var locals τ index demand),
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resources := fun i need hm => by cases List.mem_singleton.mp hm; exact member,
    live := related.live henv hscoped hTarget,
    support := entry.support, typeFootprint := _,
    typeCertificate := by simpa only [typeEq] using certificate, typeAvailable := resources,
    typed := by simpa only [raiseProfile_self] using entry.typed,
    rawTyped := entry.typed, typeCode := typeCode,
    related := by simpa only [raiseProfile_self] using related,
    rawRelated := (related.symm henv).left_diagonal }⟩

mutual
theorem Obs.variableHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .var _ _ _ demand =>
    exact variableLeaf henv hscoped context domains lookup closed hTarget substitutions fits demand
      (resources index _ List.mem_cons_self)
  | .empty => exact ⟨.empty⟩
  | .union first second =>
    obtain ⟨a⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .pad child =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.unpad⟩
  | .view child view =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.view henv hscoped hTarget view⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    have padded := answer.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem SortableObs.variableHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .legacy child => exact Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
  | .code relevant child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.computational henv⟩
  | .union first second =>
    obtain ⟨a⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .pad child =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.unpad⟩
  | .action child action =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.action henv hscoped hTarget closed action
  | .view child view =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.view henv hscoped hTarget view⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    have padded := answer.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem CodeCert.variableHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A true demand) := by
  match certificate with
  | .seed child formed =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad child =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.pad henv⟩
  | .unpad child =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.unpad henv⟩
  | .familyPad child =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.familyPad henv
  | .down child =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.down henv⟩
  | .map view child =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.map henv hscoped view
  | .select child member =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal child minimal bound =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.variableHereditary
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ (.bvar index) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A relevant demand) := by
  match certificate with
  | .seed child formed =>
    obtain ⟨answer⟩ := Obs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .observe child formed =>
    obtain ⟨answer⟩ := SortableObs.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.sortableResult henv hscoped hTarget closed formed
  | .ofCode child formed =>
    obtain ⟨answer⟩ := CodeCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.retag formed⟩
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.pad henv⟩
  | .unpad child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.unpad henv⟩
  | .familyPad child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.familyPad henv
  | .down child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.down henv⟩
  | .support action child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.supportAction henv hscoped action⟩
  | .map view child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.map henv hscoped view
  | .select child member =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.select henv member⟩
  | .focusMinimal child minimal bound =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact ⟨answer.focusMinimal henv minimal bound⟩
  | .sortPad child =>
    obtain ⟨answer⟩ := SortableCert.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits child resources
    exact answer.sortPad henv
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

theorem OriginalTail.StateHereditaryFundamental.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source A (.sort level)) :
    StateHereditaryFundamental env registry context (.bvar lookup levelWF formation) := by
  intro target locals σ τ available closed hTarget substitutions fits n demand footprint observation resources
  exact observation.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits resources

theorem OriginalTail.DerivationHereditaryFundamental.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ContextHereditaryFundamentals env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : Derivation sourceEnv U source A A (.sort level)) :
    DerivationHereditaryFundamental env registry context (.bvar lookup levelWF formation) := by
  intro target locals σ τ available closed hTarget substitutions fits
  have transfer : SortableComputationalTransfer env U registry target locals σ τ available
      (.bvar index) (.bvar index) A := by
    intro n demand footprint observation resources
    exact observation.variableHereditary henv hscoped context domains lookup closed hTarget substitutions fits resources
  exact ⟨transfer, transfer⟩

end Lean4Lean.AnchoredSource.Adapted
