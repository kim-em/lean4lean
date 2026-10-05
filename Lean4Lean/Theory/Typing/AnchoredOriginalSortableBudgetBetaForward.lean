import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetBetaApplication
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetComposition

/-! Complete hereditary forward beta transfer. Every wrapper preserves the
actual assigned-type certificate; the only replay is the instantiated-term
child already stored in the original beta rule. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
mutual
theorem Obs.betaBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app function argumentObservation arguments admitted =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.betaAppBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound (.legacy function) (.legacy argumentObservation) arguments.toGeneral admitted
      (by intro current fuel member; simp only [SortableObs.nativeDepth]; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (by intro current fuel member; simp only [SortableObs.nativeDepth]; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.betaBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .legacy source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
  | .code relevant certificate =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound certificate bounded resources
    exact ⟨answer.computational henv⟩
  | .app function argumentObservation arguments admitted =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.betaAppBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound function argumentObservation arguments admitted
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.betaBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : CodeCert env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) true demand) := by
  match certificate with
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.betaBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : SortableCert env U registry target locals σ (.app (.lam A body) argument) relevant
      demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.retag formed)
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .observe observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .support action source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.support action)
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
  | .sortPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .sortPad
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

theorem HereditaryBudgeted.Transfer.betaForwardOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) := by
  apply HereditaryBudgeted.Transfer.trans henv hscoped hTarget
  · intro n demand footprint observation bounded resources
    exact SortableObs.betaBudgeted henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound) observation bounded resources
  · exact (originalInstantiated target locals σ τ available closed hTarget substitutions fits frameBound)


end Lean4Lean.AnchoredSource.Adapted
