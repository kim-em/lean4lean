import Lean4Lean.Theory.Typing.AnchoredSortableBudgetResults
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthRenaming
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableVariable

/-! The original variable rule preserves every caller declaration budget.
It reads the actual bounded tail entry; formation is queried only at the
stored original earlier-domain occurrence. All current rich wrappers are
reconstructed with bounded source certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The only semantic calls are at finite original context locations. -/
def HereditaryBudgeted.ContextFundamentalsAt (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {tailSource : List VExpr} (tail : ContextDerivation sourceEnv U tailSource)
    {A : VExpr} {level : VLevel} (domain : EndpointRef sourceEnv U tailSource A (.sort level)),
    ContextDerivation.Location context tail domain →
    HereditaryBudgeted.StateFundamentalAt budgets env registry tail (.ref domain)

def HereditaryBudgeted.ContextFundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {tailSource : List VExpr} (tail : ContextDerivation sourceEnv U tailSource)
    {A : VExpr} {level : VLevel} (domain : EndpointRef sourceEnv U tailSource A (.sort level)),
    ContextDerivation.Location context tail domain →
    HereditaryBudgeted.StateFundamental env registry tail (.ref domain)

theorem HereditaryBudgeted.ContextFundamentals.forget
    (domains : HereditaryBudgeted.ContextFundamentals env registry context) :
    ContextHereditaryFundamentals env registry context := by
  intro tailSource tail A level domain location
  exact (domains tail domain location).forget

private theorem variableLeafBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (demand : Profile n) (member : (⟨n, demand⟩ : Need) ∈ available index) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  obtain ⟨entry, entryBound⟩ := fits.forward.lookup_allDepth henv hTarget member lookup
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
  let domainFrame := SortableTailPairedFits.diagonal entry.tailFits.contextDerivation entry.tailFits.left
  have boundTail : HereditaryBudgeted.Within budgets domainFrame.nativeDepth := by
    intro current fuel member
    simp only [domainFrame, SortableTailPairedFits.nativeDepth, SortableTailPairedFits.diagonal,
      SortableTailFits.nativeDepth_reorigin, SortableTailFits.nativeDepth_left, Nat.max_self]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (entryBound current)
      (Nat.le_trans (Nat.le_max_left _ _) (frameBound current fuel member)))
  have boundCertificate : HereditaryBudgeted.Within budgets entry.certificate.nativeDepth := by
    intro current fuel member
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (entryBound current)
      (Nat.le_trans (Nat.le_max_left _ _) (frameBound current fuel member)))
  obtain ⟨domainAnswer⟩ := original target entry.tailLocals
    entry.tailLeft entry.tailLeft entry.tailAvailable tailClosed hTarget raw.left domainFrame boundTail
    (.code true entry.certificate) (by
      intro current fuel member
      simpa only [SortableObs.nativeDepth] using boundCertificate current fuel member) entry.resources
  obtain ⟨typeAnswer⟩ := domainAnswer.sortable henv hscoped hTarget tailClosed entry.certificate.formed
  have typeEq : entry.domain.lift' (.skipN .refl (index + 1)) = A :=
    (lift'_consN_skipN (k := 0)).trans entry.sourceType_eq.symm
  let certificate := entry.certificate.renameSource (.skipN .refl (index + 1)) σ entry.left_eq locals
  let outputCertificate : SortableCert env U registry target locals σ A true entry.support
      (entry.footprint.sourceLift (.skipN .refl (index + 1))) :=
    Eq.rec (motive := fun expression _ => SortableCert env U registry target locals σ expression true
      entry.support (entry.footprint.sourceLift (.skipN .refl (index + 1)))) certificate typeEq
  have certificateDepth (current : Name → Bool) :
      outputCertificate.nativeDepth current = entry.certificate.nativeDepth current := by
    exact (SortableCert.nativeDepth_rec current typeEq (fun _ => locals) (fun _ => σ)
      id (fun _ => entry.support) (fun _ => entry.footprint.sourceLift (.skipN .refl (index + 1))) certificate).trans
      (entry.certificate.nativeDepth_renameSource current _ _ _ _)
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
    typeCertificate := outputCertificate, typeAvailable := resources,
    typed := by simpa only [raiseProfile_self] using entry.typed,
    rawTyped := entry.typed, typeCode := typeCode,
    related := by simpa only [raiseProfile_self] using related,
    rawRelated := (related.symm henv).left_diagonal
    observationBound := by
      intro current fuel _
      simp only [SortableObs.nativeDepth, Obs.nativeDepth]
      exact Nat.zero_le _
    certificateBound := by
      intro current fuel member
      change outputCertificate.nativeDepth current ≤ fuel
      rw [certificateDepth current]
      exact boundCertificate current fuel member }⟩

mutual
theorem Obs.variableBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .var _ _ _ demand =>
    exact variableLeafBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound demand
      (resources index _ List.mem_cons_self)
  | .empty => exact ⟨.empty⟩
  | .union first second =>
    obtain ⟨a⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .pad child =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.unpad⟩
  | .view child view =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.view henv hscoped hTarget view⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    have padded := answer.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem SortableObs.variableBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .legacy child => exact Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
  | .code relevant child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.computational henv⟩
  | .union first second =>
    obtain ⟨a⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .pad child =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.unpad⟩
  | .action child action =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped hTarget closed action
  | .view child view =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact ⟨answer.view henv hscoped hTarget view⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    have padded := answer.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem CodeCert.variableBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A true demand) := by
  match certificate with
  | .seed child formed =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    obtain ⟨a⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad child =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .pad
  | .unpad child =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .unpad
  | .familyPad child =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .familyPad
  | .down child =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .down
  | .map view child =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.map view)
  | .select child member =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal child minimal bound =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.variableBudgeted
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (lookup : Lookup source index A) (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    {demand : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ (.bvar index) relevant demand footprint)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A relevant demand) := by
  match certificate with
  | .seed child formed =>
    obtain ⟨answer⟩ := Obs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .observe child formed =>
    obtain ⟨answer⟩ := SortableObs.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .ofCode child formed =>
    obtain ⟨answer⟩ := CodeCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.retag formed)
  | .union first second =>
    obtain ⟨a⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound first (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound second (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .pad
  | .unpad child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .unpad
  | .familyPad child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .familyPad
  | .down child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .down
  | .support action child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.support action)
  | .map view child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.map view)
  | .select child member =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal child minimal bound =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
  | .sortPad child =>
    obtain ⟨answer⟩ := SortableCert.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound child resources
    exact answer.action henv hscoped .sortPad
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end


theorem HereditaryBudgeted.StateFundamentalAt.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source A (.sort level)) :
    HereditaryBudgeted.StateFundamentalAt budgets env registry context (.bvar lookup levelWF formation) := by
  intro target locals σ τ available closed hTarget substitutions fits frameBound n demand footprint observation _ resources
  exact observation.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound resources


/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.StateFundamental.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentals env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source A (.sort level)) :
    HereditaryBudgeted.StateFundamental env registry context (.bvar lookup levelWF formation) := by
  intro budgets
  exact HereditaryBudgeted.StateFundamentalAt.bvar henv hscoped context
    (fun {_} tail {_} {_} domain location => domains tail domain location budgets) lookup levelWF formation

theorem HereditaryBudgeted.FundamentalAt.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentalsAt budgets env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : Derivation sourceEnv U source A A (.sort level)) :
    HereditaryBudgeted.FundamentalAt budgets env registry context (.bvar lookup levelWF formation) := by
  intro target locals σ τ available closed hTarget substitutions fits frameBound
  have transfer : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.bvar index) (.bvar index) A := by
    intro n demand footprint observation _ resources
    exact observation.variableBudgeted henv hscoped context domains lookup closed hTarget substitutions fits frameBound resources
  exact ⟨transfer, transfer⟩

/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.DerivationFundamental.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : HereditaryBudgeted.ContextFundamentals env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : Derivation sourceEnv U source A A (.sort level)) :
    HereditaryBudgeted.DerivationFundamental env registry context (.bvar lookup levelWF formation) := by
  intro budgets
  exact HereditaryBudgeted.FundamentalAt.bvar henv hscoped context
    (fun {_} tail {_} {_} domain location => domains tail domain location budgets) lookup levelWF formation

end Lean4Lean.AnchoredSource.Adapted
