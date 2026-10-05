import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetEtaData
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthRenaming

/-! Actual reverse function eta from a finite returned function query.
All domains and Pi rows retain the original source formation endpoints. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim (fun h => left.singleton h) (fun h => right.singleton h)

private theorem eta_subst (A f : VExpr) (σ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst σ =
      .lam (A.subst σ) (.app (f.subst σ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst σ) (.app (f.lift.subst σ.lift) ((VExpr.bvar 0).subst σ.lift)) = _
  rw [lift_subst_lift]
  rfl

private theorem etaPack (input : Profile n) (outside : Footprint) :
    BinderPack n input (outside.sourceLift (.skip .refl) ++ [(0, ⟨n, input⟩)]) outside := by
  induction outside with
  | nil =>
    have h := BinderPack.local (n := n) ⟨n, input⟩ (Nat.le_refl n) BinderPack.nil
    simpa [Need.atGrade, Profile.union, Profile.empty, Profile.atoms, Profile.mk, Footprint.sourceLift] using h
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    exact .external i need ih

theorem SortableObs.expandEtaAtomBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {atom : Atom n} {support : Profile n} {footprint typeFootprint : Footprint}
    (observation : SortableObs env U registry target locals τ f (.singleton atom) footprint)
    (observationBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) true support typeFootprint)
    (certificateBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (typeAvailable : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) (.singleton atom) support)
    (rawEta : env.IsDefEq U target ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ)
      (f.subst τ) ((VExpr.forallE A B).subst σ))
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (_formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth) :
    Nonempty (BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f (.singleton atom)) := by
  have origins := certificate.piOriginsBudgetedOriginal henv hscoped hle hTarget closed context originalDomain originalBody
    substitutions.left fits.left.forward
    (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (HereditaryBudgeted.frame_left frameBound current fuel member))
    domainIH bodyIH certificateBound typeAvailable
  have shape := origins.forget.value_shape typed (List.mem_singleton_self _)
  cases n with
  | zero => exact shape.elim
  | succ n =>
    obtain ⟨key, output, normalEq⟩ := shape
    let normal : AtomView env U registry target atom (n := n + 1) (.fn key output) :=
      normalEq ▸ AdapterNormal.view henv atom
    let normalizedObs := SortableObs.view observation normal
    let normalizedCert := SortableCert.map normal certificate
    have normalizedTyped := normal.mapType_typed typed
    have normalizedRelated := normal.termMap henv hscoped hTarget related
    obtain ⟨resultSupport, ⟨row⟩, _⟩ := normalizedCert.piRowBudgetedOriginal henv hscoped hle hTarget closed
      context originalDomain originalBody substitutions.left fits.left.forward
      (fun current fuel member => Nat.le_trans (Nat.le_max_left _ _) (HereditaryBudgeted.frame_left frameBound current fuel member))
      domainIH bodyIH (by simpa only [normalizedCert, SortableCert.nativeDepth] using certificateBound) typeAvailable normalizedTyped
    have child : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available A A (.sort domainLevel) :=
      domainIH target locals σ τ available closed hTarget substitutions fits frameBound
    obtain ⟨domain⟩ := child.sortable henv hscoped hTarget closed row.domain row.domainBound row.domainAvailable
    have path : TypeConversion env U target (A.subst σ) (A.subst τ) :=
      .single (formedA.substDF henv substitutions.wf hTarget substitutions)
    have admittedA := row.alignment.admission henv row.anchor
    have seed := Admitted.rekey (key := ⟨A.subst σ, key.anchor, key.input⟩) henv path row.inputTyped row.domain.formed domain.related admittedA
    let newKey : Key n := ⟨A.subst τ, key.anchor, key.input⟩
    have guard : LambdaGuard env U registry target τ A newKey row.domainSupport := {
      inputTyped := row.inputTyped
      formed := row.domain.formed
      path := .refl
      domains := (domain.related.symm henv row.inputTyped.wf_type).left_diagonal
      anchor := seed }
    let lifted := normalizedObs.renameSource (.skip .refl) (τ.cons key.anchor) rfl (Locals.push locals)
    have liftedPacket : ∃ functionObs : SortableObs env U registry target (Locals.push locals)
        (τ.cons key.anchor) (f.lift' (.skip .refl)) (Profile.fn key output)
        (footprint.sourceLift (.skip .refl)),
        ∀ current, functionObs.nativeDepth current = observation.nativeDepth current := by
      refine ⟨lifted, ?_⟩
      intro current
      simp only [lifted, normalizedObs, SortableObs.nativeDepth_renameSource, SortableObs.nativeDepth]
    rw [← lift_eq_lift'] at liftedPacket
    obtain ⟨functionObs, functionDepth⟩ := liftedPacket
    let application : SortableObs env U registry target (Locals.push locals) (τ.cons key.anchor)
        (.app f.lift (.bvar 0)) (.singleton output)
        (footprint.sourceLift (.skip .refl) ++ [(0, ⟨n, key.input⟩)]) := by
      exact .app functionObs
        (.legacy (.var _ _ 0 key.input)) (.refl _) row.anchor
    let expanded := SortableObs.lam domain.certificate guard application (etaPack key.input footprint)
      (fun _ h => h)
    have changing : AtomView env U registry target (n := n + 1)
        (.fn key output) (.fn newKey output) :=
      .trans (row.alignment.view key.anchor output)
        (.domainRekey path row.inputTyped row.domain.formed domain.related)
    have whole : AtomView env U registry target atom (n := n + 1) (.fn newKey output) :=
      .trans normal changing
    have mappedTyped := whole.mapType_typed typed
    have mappedCode := whole.codeMap henv hscoped code
    have mappedRelated := whole.termMap henv hscoped hTarget related
    have rawEta' := rawEta
    rw [eta_subst] at rawEta'
    have etaLeft := Related.etaExpandAt henv rawEta' rawEta'.hasType.2 mappedRelated
    have etaRight := Related.symm henv etaLeft
    have etaSelf := Related.etaExpandAt henv rawEta' rawEta'.hasType.1 etaRight
    have oldRelated := (whole.inverse henv).termMap henv hscoped hTarget etaRight
    have oldTyped := (whole.inverse henv).mapType_typed mappedTyped
    have oldCode := (whole.inverse henv).codeMap henv hscoped mappedCode
    have back := Related.retag henv typed code oldRelated
    have allCode := code_union code mappedCode
    have wf := typed.wf_type.union mappedTyped.wf_type
    have requestedTyped := typed.enlarge (Profile.le_union_left _ _) wf
    have rawTyped := mappedTyped.enlarge (Profile.le_union_right _ _) wf
    exact ⟨{
      rawDemand := Profile.fn newKey output
      footprint := domain.footprint ++ footprint
      observation := expanded
      resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
        (domain.available i need) (resources i need)
      adapter := .cons (List.mem_singleton_self _) ((whole.inverse henv).toGeneralAdapter henv hscoped hTarget) (.nil _)
      support := _
      typeFootprint := typeFootprint ++ typeFootprint
      certificate := .union certificate (.map whole certificate)
      typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
        (typeAvailable i need) (typeAvailable i need)
      typed := requestedTyped
      rawTyped := rawTyped
      code := allCode
      related := by simpa only [eta_subst] using Related.retag henv requestedTyped allCode back
      rawRelated := by simpa only [eta_subst, Profile.fn] using Related.retag henv rawTyped allCode etaSelf
      observationBound := by
        intro current fuel member
        simp only [expanded, SortableObs.nativeDepth]
        change max (domain.certificate.nativeDepth current) (application.nativeDepth current) ≤ fuel
        simp only [application, SortableObs.nativeDepth, Obs.nativeDepth, functionDepth, Nat.max_zero]
        exact Nat.max_le.mpr ⟨domain.valueBound current fuel member, observationBound current fuel member⟩
      certificateBound := by
        intro current fuel member
        simpa only [SortableCert.nativeDepth, Nat.max_self] using certificateBound current fuel member }⟩

theorem SortableObs.expandEtaProfileBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile support : Profile n} {footprint typeFootprint : Footprint}
    (observation : SortableObs env U registry target locals τ f profile footprint)
    (observationBound : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available)
    (certificate : SortableCert env U registry target locals σ (.forallE A B) true support typeFootprint)
    (certificateBound : HereditaryBudgeted.Within budgets certificate.nativeDepth)
    (typeAvailable : typeFootprint.Available available)
    (typed : profile.HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) profile support)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth) :
    Nonempty (BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f profile) := by
  have rawEta := IsDefEq.eta_subst_right henv hTarget substitutions formedA formedB functionTyped
  have go : ∀ selected : Profile n, List.Subset selected profile →
      Nonempty (BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f selected) := by
    intro selected included
    induction selected with
    | nil => exact ⟨.empty⟩
    | cons atom rest ih =>
      have member := included List.mem_cons_self
      obtain ⟨selected, selectedDepth⟩ := observation.atom_allDepth member
      have localResources := selected.atomizes.available_closed resources closed
      obtain ⟨head⟩ := selected.observation.expandEtaAtomBudgetedOriginal henv hscoped hle
        (fun current fuel member => Nat.le_trans (selectedDepth current) (observationBound current fuel member)) localResources certificate
        certificateBound typeAvailable (typed.singleton_of_mem member) code
        (related.singleton_of_mem member) rawEta context originalDomain originalBody domainIH bodyIH
        formedA formedB closed hTarget substitutions fits frameBound
      obtain ⟨tail⟩ := ih (fun _ h => included (List.mem_cons_of_mem _ h))
      exact ⟨head.union henv tail⟩
  exact go profile (fun _ h => h)

theorem HereditaryBudgeted.Result.etaExpandBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile : Profile n}
    (result : HereditaryBudgeted.Result budgets env U registry target locals σ τ available f f (.forallE A B) profile)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyIH : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) profile) := by
  obtain ⟨expanded⟩ := result.observation.expandEtaProfileBudgetedOriginal henv hscoped hle
    result.observationBound result.resources result.typeCertificate result.certificateBound result.typeAvailable result.rawTyped result.typeCode
    result.rawRelated context originalDomain originalBody domainIH bodyIH formedA formedB functionTyped
    closed hTarget substitutions fits frameBound
  have requested := result.adapter.termMap henv hscoped hTarget result.typed result.typeCode expanded.related
  have cross := Related.trans henv hscoped result.related requested
  have code := code_union result.typeCode expanded.code
  have wf := result.typed.wf_type.union expanded.rawTyped.wf_type
  have typed := result.typed.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := expanded.rawTyped.enlarge (Profile.le_union_right _ _) wf
  exact ⟨{
    rank := result.rank
    bound := result.bound
    raw := expanded.rawDemand
    footprint := expanded.footprint
    observation := expanded.observation
    adapter := expanded.adapter.comp result.adapter
    resources := expanded.resultAvailable
    support := result.support.union expanded.support
    typeFootprint := result.typeFootprint ++ expanded.typeFootprint
    typeCertificate := .union result.typeCertificate expanded.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (result.typeAvailable i need) (expanded.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code cross
    rawRelated := Related.retag henv rawTyped code expanded.rawRelated
    live := (Related.retag henv rawTyped code expanded.rawRelated).live henv hscoped hTarget
    observationBound := expanded.observationBound
    certificateBound := by
      intro current fuel member
      simp only [SortableCert.nativeDepth]
      exact Nat.max_le.mpr ⟨result.certificateBound current fuel member, expanded.certificateBound current fuel member⟩ }⟩

end Lean4Lean.AnchoredSource.Adapted
