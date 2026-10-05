import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetEtaContraction
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferConversion

/-! The complete original lambda equality for hereditary observations. The
mutual traversal covers both legacy and rich computational/certificate
wrappers; reverse typing is transported through the actual Pi equality. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
mutual
theorem Obs.etaContractBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : Obs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.etaLamBudgetedOriginal henv hscoped hle (.ofCode domain domain.formed)
      (by simpa only [SortableCert.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))) guard (.legacy body)
      (by simpa only [SortableObs.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))) pack covered
      context originalDomain originalBody domainIH bodyIH functionChild formedA formedB functionTyped
      closed hTarget substitutions fits frameBound
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.etaContractBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : SortableObs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .legacy source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
  | .code relevant certificate =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound certificate bounded resources
    exact ⟨answer.computational henv⟩
  | .lam domain guard body pack covered =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.etaLamBudgetedOriginal henv hscoped hle domain (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)) guard body (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member)) pack covered
      context originalDomain originalBody domainIH bodyIH functionChild formedA formedB functionTyped
      closed hTarget substitutions fits frameBound
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.etaContractBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : CodeCert env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) true demand) := by
  match certificate with
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.etaContractBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : SortableCert env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) relevant demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.retag formed)
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .observe observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableObs.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .support action source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.support action)
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
  | .sortPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.etaContractBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .sortPad
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted
