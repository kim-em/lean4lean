import Lean4Lean.Theory.Typing.AnchoredSortableTransferAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetLambda
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetPiRule
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetConversion

/-! The complete original lambda equality for hereditary observations. The
mutual traversal covers both legacy and rich computational/certificate
wrappers; reverse typing is transported through the actual Pi equality. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
mutual
theorem Obs.lamBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : Obs env U registry target locals σ (.lam A body) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.graded_lam_transferBudgetedOriginal henv hscoped (.ofCode domain domain.formed)
      (by simpa only [SortableCert.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))) guard (.legacy body)
      (by simpa only [SortableObs.nativeDepth] using (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))) pack covered
      context domainRef originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits frameBound
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.lamBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : SortableObs env U registry target locals σ (.lam A body) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .legacy source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
  | .code relevant certificate =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound certificate bounded resources
    exact ⟨answer.computational henv⟩
  | .lam domain guard body pack covered =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    exact SortableObs.graded_lam_transferBudgetedOriginal henv hscoped domain (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)) guard body (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member)) pack covered
      context domainRef originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits frameBound
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound left
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound right
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.lamBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : CodeCert env U registry target locals σ (.lam A body) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) true demand) := by
  match certificate with
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableCert.lamBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (certificate : SortableCert env U registry target locals σ (.lam A body) relevant demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.CodeResult budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) relevant demand) := by
  match certificate with
  | .ofCode source formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := CodeCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.retag formed)
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := Obs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .observe observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact answer.sortable henv hscoped hTarget closed formed
  | .union first second =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound first
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound second
      (by intro current fuel member; exact Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv b⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .pad
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .down
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .unpad
  | .support action source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.support action)
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.map view)
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .familyPad
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.select member)
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped (.focusMinimal minimal bound)
  | .sortPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth] at bounded
    obtain ⟨answer⟩ := SortableCert.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact answer.action henv hscoped .sortPad
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

end

theorem HereditaryBudgeted.Transfer.lamDFOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) body other B)
    (originalCodomain : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth) :
    HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
  SortableObs.lamBudgeted henv hscoped context domainRef originalDomain originalBody originalCodomain
    domains codomain bodies rightBody closed hTarget substitutions fits frameBound

/-- The two lambda annotations use their own actual formation references.
The reverse Pi conversion is constructed from the original formation
children, not supplied as a recursive call on a synthesized derivation. -/
theorem HereditaryBudgeted.FundamentalAt.lamDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B)
    (domainIH : HereditaryBudgeted.FundamentalAt budgets env registry context domain)
    (codomainIH : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.left domain)) codomain)
    (codomainIH' : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.right domain)) codomain')
    (bodyIH : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.left domain)) bodies)
    (bodyIH' : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.right domain)) bodies') :
    HereditaryBudgeted.FundamentalAt budgets env registry context
      (.lamDF domainWF bodyWF domain codomain codomain' bodies bodies') := by
  intro target locals σ τ available closed hTarget substitutions fits frameBound
  have domainJoint : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel) := domainIH
  have bodyJoint : HereditaryBudgeted.TailJointAt budgets env registry (.cons context (.left domain)) body other B := bodyIH
  have otherJoint : HereditaryBudgeted.TailJointAt budgets env registry (.cons context (.right domain)) body other B := bodyIH'
  have forward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
    HereditaryBudgeted.Transfer.lamDFOriginal henv hscoped context (.left domain) domainJoint bodyJoint codomainIH
      (domain.forget.defeq.mono hle) (codomain.forget.defeq.mono hle)
      (bodies.forget.defeq.mono hle) (bodies'.forget.defeq.mono hle).hasType.2
      closed hTarget substitutions fits frameBound
  have backwardNatural : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A' B) :=
    HereditaryBudgeted.Transfer.lamDFOriginal henv hscoped context (.right domain) domainJoint.symm otherJoint.symm codomainIH'
      (domain.forget.defeq.mono hle).symm (codomain'.forget.defeq.mono hle)
      (bodies'.forget.defeq.mono hle).symm (bodies.forget.defeq.mono hle).hasType.1
      closed hTarget substitutions fits frameBound
  have pi := HereditaryBudgeted.FundamentalAt.forallEDF henv hscoped hle context domainWF bodyWF
    domain codomain codomain' domainIH codomainIH codomainIH'
  have code : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available
      (.forallE A' B) (.forallE A B) (.sort (.imax domainLevel bodyLevel)) :=
    (pi target locals σ σ available closed hTarget substitutions.left fits.left (HereditaryBudgeted.frame_left frameBound)).2
  have backward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A B) :=
    HereditaryBudgeted.Transfer.convertAnswer henv hscoped closed hTarget code backwardNatural
  exact ⟨forward, backward⟩

/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.DerivationFundamental.lamDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B)
    (domainIH : HereditaryBudgeted.DerivationFundamental env registry context domain)
    (codomainIH : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.left domain)) codomain)
    (codomainIH' : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.right domain)) codomain')
    (bodyIH : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.left domain)) bodies)
    (bodyIH' : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.right domain)) bodies') :
    HereditaryBudgeted.DerivationFundamental env registry context
      (.lamDF domainWF bodyWF domain codomain codomain' bodies bodies') := by
  intro budgets
  exact HereditaryBudgeted.FundamentalAt.lamDF henv hscoped hle context domainWF bodyWF domain codomain codomain' bodies bodies'
    (domainIH budgets) (codomainIH budgets) (codomainIH' budgets) (bodyIH budgets) (bodyIH' budgets)

end Lean4Lean.AnchoredSource.Adapted
