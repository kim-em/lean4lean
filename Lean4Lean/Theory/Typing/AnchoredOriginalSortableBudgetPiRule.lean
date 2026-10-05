import Lean4Lean.Theory.Typing.AnchoredOriginalSortablePiRule
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetPi
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetSortResult

/-! The actual original Pi rule for the complete hereditary observer syntax.
Native formation flags, code wrappers, and all computational closures are
interpreted through the same fixed original domain/body calls. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

@[simp] theorem PiRows.nativeDepth_toSortable (current : Name → Bool)
    (rows : PiRows env U registry target locals σ A B ambient entries footprint) :
    rows.toSortable.nativeDepth current = rows.nativeDepth current := by
  match rows with
  | .nil => simp only [PiRows.toSortable, SortableRows.nativeDepth, PiRows.nativeDepth]
  | .cons guard body pack covered tail =>
    simp only [PiRows.toSortable, SortableRows.nativeDepth, SortableCert.nativeDepth, PiRows.nativeDepth, tail.nativeDepth_toSortable current]
termination_by sizeOf rows

mutual
theorem Obs.piBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : Obs env U registry target locals σ (.forallE A B) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .pi domain guard body =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    exact SortableCert.piTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalBody domains bodies rightBody
      closed hTarget substitutions fits frameBound (.ofCode domain domain.formed)
      (by intro current fuel member; simp only [SortableCert.nativeDepth]; exact Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      guard body.toSortable
      (by intro current fuel member; simpa only [PiRows.nativeDepth_toSortable] using Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound left (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound right (fun current fuel member => Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.piBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (observation : SortableObs env U registry target locals σ (.forallE A B) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .legacy source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    exact Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
  | .code requestedFlag certificate =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨actualFlag, flag⟩ : ∃ actualFlag, Relevant (.imax domainLevel bodyLevel) actualFlag := by
      by_cases h : VLevel.imax domainLevel bodyLevel ≈ .zero
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound flag certificate bounded resources
    have sourceA : OnCtx (A :: source) (env.IsType U) := ⟨substitutions.wf, _, domains.hasType.1⟩
    exact ⟨result.computational henv
      ⟨domains.sort_r henv substitutions.wf,
        bodies.sort_r henv sourceA⟩ flag⟩
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound left (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound right (fun current fuel member => Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .action source action =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact a.action henv hscoped hTarget closed action
  | .view source change =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    exact ⟨a.unpad⟩
  | @SortableObs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨a⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits frameBound source bounded resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

theorem CodeCert.piBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (flag : Relevant (.imax domainLevel bodyLevel) actualFlag)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.SortResult budgets env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') true actualFlag demand) := by
  match certificate with
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨hl⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag left (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag right (fun current fuel member => Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨{
      footprint := hl.footprint ++ hr.footprint, certificate := .union hl.certificate hr.certificate
      available := fun i need hm => (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
      related := ?_, sorted := hl.sorted.union hr.sorted
      bounded := by intro current fuel member; simp only [SortableCert.nativeDepth]
                    exact Nat.max_le.mpr ⟨hl.bounded current fuel member, hr.bounded current fuel member⟩ }⟩
    apply TypeRelated.of_singletons
    intro atom hm
    exact (List.mem_append.mp hm).elim
      (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .pad result.certificate,
      available := result.available, related := result.related.pad henv, sorted := result.sorted.pad_sort
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .familyPad result.certificate,
      available := result.available, related := result.related.familyPad henv, sorted := result.sorted.familyPad
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .unpad result.certificate,
      available := result.available, related := (TypeRelated.pad_iff henv).mp result.related, sorted := by simpa only [Profile.down_sort] using result.sorted.pad_inv
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .down result.certificate,
      available := result.available, related := result.related.down henv, sorted := by simpa only [Profile.down_sort] using result.sorted.down
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .map view result.certificate,
      available := result.available, related := view.codeMap henv hscoped result.related, sorted := view.mapType_sort result.sorted
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth] using result.bounded current fuel member }⟩
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .select result.certificate member,
      available := result.available, related := result.related.singleton member, sorted := result.sorted.singleton_of_mem member
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .focusMinimal result.certificate minimal bound,
      available := result.available, related := result.related.focusMinimal henv minimal bound, sorted := result.sorted.restrict bound minimal.formation.wf_value
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableCert.piBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {A : VExpr} {domainLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A' B B' : VExpr}
    {bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort domainLevel))
    (originalBody : HereditaryBudgeted.TailJointAt budgets env registry (.cons context domainRef) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (flag : Relevant (.imax domainLevel bodyLevel) actualFlag)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) requestedFlag demand footprint)
    (bounded : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (resources : footprint.Available available) :
    Nonempty (HereditaryBudgeted.SortResult budgets env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') requestedFlag actualFlag demand) := by
  match certificate with
  | .ofCode source requested =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := CodeCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .observe (.code true result.certificate) requested,
      available := result.available, related := result.related, sorted := result.sorted
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .pi domain guard rowBodies =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piTransferBudgetedOriginal henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound domain
      (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member)) guard rowBodies
      (fun current fuel member => Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact result.atSort henv hscoped closed hTarget (SortableCert.pi domain guard rowBodies).formed flag
  | .observe observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableObs.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .seed observation formed =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := Obs.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound observation bounded resources
    exact result.atSort henv hscoped closed hTarget formed flag
  | .union left right =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨hl⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag left (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag right (fun current fuel member => Nat.le_trans (Nat.le_max_right _ _) (bounded current fuel member))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨{
      footprint := hl.footprint ++ hr.footprint, certificate := .union hl.certificate hr.certificate
      available := fun i need hm => (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
      related := ?_, sorted := hl.sorted.union hr.sorted
      bounded := by intro current fuel member; simp only [SortableCert.nativeDepth]
                    exact Nat.max_le.mpr ⟨hl.bounded current fuel member, hr.bounded current fuel member⟩ }⟩
    apply TypeRelated.of_singletons
    intro atom hm
    exact (List.mem_append.mp hm).elim
      (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .pad result.certificate,
      available := result.available, related := result.related.pad henv, sorted := result.sorted.pad_sort
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .sortPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .sortPad result.certificate,
      available := result.available, related := result.related.sortPad, sorted := result.sorted.sortPad
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .familyPad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .familyPad result.certificate,
      available := result.available, related := result.related.familyPad henv, sorted := result.sorted.familyPad
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .unpad source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .unpad result.certificate,
      available := result.available, related := (TypeRelated.pad_iff henv).mp result.related, sorted := by simpa only [Profile.down_sort] using result.sorted.pad_inv
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .down source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .down result.certificate,
      available := result.available, related := result.related.down henv, sorted := by simpa only [Profile.down_sort] using result.sorted.down
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .support action source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .support action result.certificate,
      available := result.available, related := action.codeMap henv hscoped result.related, sorted := action.preservesSort result.sorted
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth] using result.bounded current fuel member }⟩
  | .map view source =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .map view result.certificate,
      available := result.available, related := view.codeMap henv hscoped result.related, sorted := view.mapType_sort result.sorted
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth] using result.bounded current fuel member }⟩
  | .select source member =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .select result.certificate member,
      available := result.available, related := result.related.singleton member, sorted := result.sorted.singleton_of_mem member
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
  | .focusMinimal source minimal bound =>
    simp only [SortableObs.nativeDepth, SortableCert.nativeDepth, Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at bounded
    obtain ⟨result⟩ := SortableCert.piBudgeted henv hscoped context domainRef originalDomain originalBody domains bodies rightBody closed hTarget substitutions fits frameBound flag source bounded resources
    exact ⟨{
      footprint := result.footprint, certificate := .focusMinimal result.certificate minimal bound,
      available := result.available, related := result.related.focusMinimal henv minimal bound, sorted := result.sorted.restrict bound minimal.formation.wf_value
      bounded := by intro current fuel member; simpa only [SortableCert.nativeDepth, SortableObs.nativeDepth] using result.bounded current fuel member }⟩
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

end

/-- The actual original Pi equality, with each body interpreted in its
own retained original domain context. -/
theorem HereditaryBudgeted.FundamentalAt.forallEDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort u))
    (body : Derivation sourceEnv U (A :: source) B B' (.sort v))
    (body' : Derivation sourceEnv U (A' :: source) B B' (.sort v))
    (domainIH : HereditaryBudgeted.FundamentalAt budgets env registry context domain)
    (bodyIH : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.left domain)) body)
    (bodyIH' : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.right domain)) body') :
    HereditaryBudgeted.FundamentalAt budgets env registry context (.forallEDF hu hv domain body body') := by
  intro target locals σ τ available closed hTarget substitutions fits frameBound
  have domains := domain.forget.defeq.mono below
  have bodies := body.forget.defeq.mono below
  have bodies' := body'.forget.defeq.mono below
  have domainJoint : HereditaryBudgeted.TailJointAt budgets env registry context A A' (.sort u) := domainIH
  have bodyJoint : HereditaryBudgeted.TailJointAt budgets env registry (.cons context (.left domain)) B B' (.sort v) := bodyIH
  have bodyJoint' : HereditaryBudgeted.TailJointAt budgets env registry (.cons context (.right domain)) B B' (.sort v) := bodyIH'
  have forward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax u v)) :=
    SortableObs.piBudgeted henv hscoped context (.left domain) domainJoint bodyJoint
      domains bodies bodies'.hasType.2 closed hTarget substitutions fits frameBound
  have backward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.forallE A' B') (.forallE A B) (.sort (.imax u v)) :=
    SortableObs.piBudgeted henv hscoped context (.right domain) domainJoint.symm bodyJoint'.symm
      domains.symm bodies'.symm bodies.hasType.1 closed hTarget substitutions fits frameBound
  exact ⟨forward, backward⟩

/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.DerivationFundamental.forallEDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort u))
    (body : Derivation sourceEnv U (A :: source) B B' (.sort v))
    (body' : Derivation sourceEnv U (A' :: source) B B' (.sort v))
    (domainIH : HereditaryBudgeted.DerivationFundamental env registry context domain)
    (bodyIH : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.left domain)) body)
    (bodyIH' : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.right domain)) body') :
    HereditaryBudgeted.DerivationFundamental env registry context (.forallEDF hu hv domain body body') := by
  intro budgets
  exact HereditaryBudgeted.FundamentalAt.forallEDF henv hscoped below context hu hv domain body body'
    (domainIH budgets) (bodyIH budgets) (bodyIH' budgets)

end Lean4Lean.AnchoredSource.Adapted
