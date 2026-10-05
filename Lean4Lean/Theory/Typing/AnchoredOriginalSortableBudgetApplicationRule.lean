import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetApplicationTransfer
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetConversion
import Lean4Lean.Theory.Typing.AnchoredOriginalTailApplication

/-! Complete hereditary application F traverses every old and rich query
wrapper, then assembles the five original appDF children at exact source tails. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

mutual
theorem Obs.appBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available a b A)
    (resultChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : Obs env U registry target locals σ (.app f a) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app fn arg arguments admitted =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.appTransferBudgetedOriginal henv hscoped hle context originalDomain originalBody
      domainIH bodyIH functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound
      (.legacy fn) (by simpa only [SortableObs.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)))
      (.legacy arg) (by simpa only [SortableObs.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))) arguments.toGeneral admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.appBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available a b A)
    (resultChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : SortableObs env U registry target locals σ (.app f a) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .legacy source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
  | .code relevant certificate =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound certificate bounded resources
    exact ⟨answer.computational henv⟩
  | .app fn arg arguments admitted =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.appTransferBudgetedOriginal henv hscoped hle context originalDomain originalBody
      domainIH bodyIH functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound
      fn (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)) arg (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member)) arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.appBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available a b A)
    (resultChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : CodeCert env U registry target locals σ (.app f a) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) true demand) := by
  match certificate with
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.appBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available a b A)
    (resultChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : SortableCert env U registry target locals σ (.app f a) relevant demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.retag formed)
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .observe observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .support action source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.support action)
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
  | .sortPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
      functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .sortPad
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end


/-- Hereditary transfer of an actual source application. -/
theorem HereditaryBudgeted.Transfer.appOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available a b A)
    (resultChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth) :
    HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) :=
  SortableObs.appBudgeted henv hscoped hle context originalDomain originalBody domainIH bodyIH
    functionChild argumentChild resultChild rawArgument closed hTarget substitutions fits frameBound

/-- The five original appDF children are queried at their exact retained
tails; the reverse result conversion is the original result equality. The
strict schedules are `OriginalTail.appDF_schedule` for this same derivation. -/
theorem HereditaryBudgeted.FundamentalAt.appDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (function : Derivation sourceEnv U source f g (.forallE A B))
    (argument : Derivation sourceEnv U source a b A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst b) (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.FundamentalAt budgets env registry context domain)
    (bodyIH : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.FundamentalAt budgets env registry context function)
    (argumentIH : HereditaryBudgeted.FundamentalAt budgets env registry context argument)
    (resultIH : HereditaryBudgeted.FundamentalAt budgets env registry context result) :
    HereditaryBudgeted.FundamentalAt budgets env registry context (.appDF domainWF bodyWF domain body function argument result) := by
  have domainF : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref (.left domain)) := by
    intro target locals σ τ available closed hTarget substitutions fits frameBound
    exact (domainIH target locals σ τ available closed hTarget substitutions fits frameBound).1
  have bodyF : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context (.left domain)) (.ref (.left body)) := by
    intro target locals σ τ available closed hTarget substitutions fits frameBound
    exact (bodyIH target locals σ τ available closed hTarget substitutions fits frameBound).1
  intro target locals σ τ available closed hTarget substitutions fits frameBound
  have functionAnswer := functionIH target locals σ τ available closed hTarget substitutions fits frameBound
  have argumentAnswer := argumentIH target locals σ τ available closed hTarget substitutions fits frameBound
  have resultAnswer := resultIH target locals σ σ available closed hTarget substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound)
  have resultJoint : HereditaryBudgeted.TailJointAt budgets env registry context (B.inst a) (B.inst b) (.sort bodyLevel) := resultIH
  have resultLeft : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel) :=
    (resultJoint.left henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound)).1
  have resultRight : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (B.inst b) (B.inst b) (.sort bodyLevel) :=
    (resultJoint.symm.left henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound)).1
  have forward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) :=
    HereditaryBudgeted.Transfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainF bodyF functionAnswer.1 argumentAnswer.1 resultLeft
      (argument.forget.defeq.mono hle) closed hTarget substitutions fits frameBound
  have backwardNatural : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst b) :=
    HereditaryBudgeted.Transfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainF bodyF functionAnswer.2 argumentAnswer.2 resultRight
      (argument.forget.defeq.mono hle).symm closed hTarget substitutions fits frameBound
  have backward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst a) :=
    HereditaryBudgeted.Transfer.convertAnswer henv hscoped closed hTarget resultAnswer.2 backwardNatural
  exact ⟨forward, backward⟩

/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.DerivationFundamental.appDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (function : Derivation sourceEnv U source f g (.forallE A B))
    (argument : Derivation sourceEnv U source a b A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst b) (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.DerivationFundamental env registry context domain)
    (bodyIH : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.DerivationFundamental env registry context function)
    (argumentIH : HereditaryBudgeted.DerivationFundamental env registry context argument)
    (resultIH : HereditaryBudgeted.DerivationFundamental env registry context result) :
    HereditaryBudgeted.DerivationFundamental env registry context (.appDF domainWF bodyWF domain body function argument result) := by
  intro budgets
  exact HereditaryBudgeted.FundamentalAt.appDF henv hscoped hle context domainWF bodyWF domain body function argument result
    (domainIH budgets) (bodyIH budgets) (functionIH budgets) (argumentIH budgets) (resultIH budgets)

end Lean4Lean.AnchoredSource.Adapted
