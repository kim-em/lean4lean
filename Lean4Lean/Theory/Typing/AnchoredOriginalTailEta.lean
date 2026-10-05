import Lean4Lean.Theory.Typing.AnchoredOriginalTailApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaDiagonal
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaJoint

/-! Function eta uses only fixed original domain, codomain, and function
calls. Source head frames retain the actual original domain occurrence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem EtaFactor.certificateOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : EtaFactor env U registry target locals σ f key output outside)
    {resultSupport : Profile factor.rank}
    (row : PiRowCertificate env U registry target locals σ available A B factor.key resultSupport)
    (outputTyped : (Profile.singleton factor.rawOutput).HasType resultSupport)
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailPairedFits env registry target context locals σ σ available)
    (domainAvailable : domainFootprint.Available available) :
    ∃ support footprint,
      Nonempty (CodeCert env U registry target locals σ (.forallE A B) support footprint) ∧
      footprint.Available available ∧
      (raiseProfile (factor.rank + 1) (Nat.succ_le_succ factor.bound)
        (Profile.fn key output)).HasType support ∧
      TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
        ((VExpr.forallE A B).subst σ) support := by
  obtain ⟨anchored⟩ := row.reanchorOriginal henv hscoped hle hTarget closed context originalDomain originalBody
    substitutions fits.forward domainIH bodyIH factor.admitted
  have scope := formedB.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  have externalLive := (fits.forward.toFits henv hTarget).leavesLive henv hscoped hTarget anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped scope))
  have highDomain := domain.raise factor.bound
  have highGuard := guard.raise henv factor.bound
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := highGuard.anchor
  have newLive := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨bodyFootprint, external, packed, ⟨body⟩, pack, covered, resources⟩ :=
    anchored.body.replayInput henv hscoped hTarget factor.arguments newLive
      anchored.pack anchored.covered anchored.outsideAvailable externalLive closed
  have changedBody := CodeCert.map factor.resultView body
  have certificate := highDomain.piLiteral
    (PiRows.cons highGuard changedBody pack covered PiRows.nil)
  have typed : (Profile.fn (raiseKey factor.rank factor.bound key)
      (raiseAtom factor.rank factor.bound output)).HasType
      (Profile.pi (A.subst σ) (B.subst σ.lift)
        (raiseProfile factor.rank factor.bound domainSupport)
        [(raiseKey factor.rank factor.bound key, factor.resultView.mapType resultSupport)]) :=
    Profile.HasType.fn certificate.formed.wf_value (List.mem_singleton_self _)
      (factor.resultView.mapType_typed outputTyped)
  have code := OriginalEndpointFactor.CodeCert.piDiagonalOriginal henv hscoped hle context
    originalDomain originalBody domainIH bodyIH closed hTarget substitutions fits.forward
    highDomain PiGuard.literal (.cons highGuard changedBody pack covered .nil)
    domainAvailable (fun i need member => resources i need (by simpa using member))
  let view := (functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) factor.bound key output).inverse henv
  refine ⟨_, _, ⟨CodeCert.map view certificate⟩, ?_, ?_, view.codeMap henv hscoped code⟩
  · intro i need hm
    exact (List.mem_append.mp hm).elim (domainAvailable i need)
      (fun h => resources i need (by simpa using h))
  · simpa only [Profile.fn, raiseProfile_singleton] using view.mapType_typed typed

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

theorem EtaFactor.completeOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport : Profile n}
    {domainFootprint outside : Footprint}
    (factor : EtaFactor env U registry target locals σ f key output outside)
    (functionResult : GradedTransferResult env U registry target locals σ τ available
      f f (.forallE A B) (Profile.fn factor.key factor.rawOutput))
    {resultSupport : Profile factor.rank}
    (row : PiRowCertificate env U registry target locals σ available A B factor.key resultSupport)
    (outputTyped : (Profile.singleton factor.rawOutput).HasType resultSupport)
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (domainAvailable : domainFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  have functionRelated := functionResult.requestedRelated henv hTarget
  obtain ⟨adapt⟩ := factor.adapter henv hscoped hTarget guard functionRelated
  obtain ⟨support, footprint, ⟨certificate⟩, resources, typed, code⟩ :=
    factor.certificateOriginal henv hscoped hle row outputTyped domain guard context originalDomain originalBody domainIH bodyIH
      formedA formedB closed hTarget substitutions.left fits.left domainAvailable
  have raw := functionTyped.substDF henv substitutions.wf hTarget substitutions
  have expanded := Related.etaExpand henv raw functionRelated
  have requested := adapt.termMap henv hscoped hTarget typed code expanded
  have highCertificate := certificate.raise functionResult.bound
  have highCode := TypeRelated.raise henv functionResult.bound code
  have highTyped := Profile.HasType.raise functionResult.bound typed
  have highRelated := Related.raise henv functionResult.bound requested
  have allCode := code_union highCode functionResult.typeCode
  have wf := highTyped.wf_type.union functionResult.rawTyped.wf_type
  have requestedTyped := highTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := functionResult.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have adapter := functionResult.adapter.comp
    (NormalProfileAdapter.raise henv hscoped hTarget functionResult.bound adapt)
  refine ⟨{
    rank := functionResult.rank
    bound := Nat.le_trans (Nat.succ_le_succ factor.bound) functionResult.bound
    rawDemand := functionResult.rawDemand
    resultFootprint := functionResult.resultFootprint
    observation := functionResult.observation
    adapter := by simpa only [raiseProfile_trans] using adapter
    resultAvailable := functionResult.resultAvailable
    support := _
    typeFootprint := _
    certificate := .union highCertificate functionResult.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (resources i need) (functionResult.typeAvailable i need)
    typed := by simpa only [raiseProfile_trans] using requestedTyped
    rawTyped := rawTyped
    typeCode := allCode
    related := ?_
    rawRelated := Related.retag henv rawTyped allCode functionResult.rawRelated }⟩
  simpa only [eta_subst, raiseProfile_trans] using
    Related.retag henv requestedTyped allCode highRelated


theorem Obs.etaLamOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals σ A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (body : Obs env U registry target (Locals.push locals) (σ.cons key.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : GradedTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) (Profile.fn key output)) := by
  obtain ⟨factor⟩ := body.eta_factor henv hscoped hTarget pack covered
  obtain ⟨returned⟩ := functionChild factor.function outsideAvailable
  obtain ⟨resultSupport, ⟨row⟩, outputTyped⟩ := returned.requestedCertificate.piRowOriginal
    henv hscoped hle hTarget closed context originalDomain originalBody substitutions.left fits.left.forward
    domainIH bodyIH returned.typeAvailable returned.requestedTyped
  exact factor.completeOriginal henv hscoped hle returned row outputTyped domain guard
    context originalDomain originalBody domainIH bodyIH formedA formedB functionTyped closed hTarget
    substitutions fits domainAvailable

/-- Full forward eta transfer for the replacement source grammar, including
all enclosing demand views, finite conjunctions, and grade changes. -/
theorem Obs.etaContractOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : GradedTransfer env U registry target locals σ τ available f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    exact body.etaLamOriginal henv hscoped hle domain guard pack covered
      context originalDomain originalBody domainIH bodyIH functionChild formedA formedB functionTyped
      closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨hl⟩ := left.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := right.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨hl.union henv hscoped hTarget hr⟩
  | .view source change =>
    obtain ⟨result⟩ := source.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits resources
    exact ⟨result.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨result⟩ := source.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits resources
    exact ⟨result.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨result⟩ := source.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits resources
    exact ⟨result.unpad⟩
  | .rowShift source =>
    obtain ⟨result⟩ := source.etaContractOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      formedA formedB functionTyped closed hTarget substitutions fits resources
    exact ⟨(result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

private theorem etaPack (input : Profile n) (outside : Footprint) :
    BinderPack n input (outside.sourceLift (.skip .refl) ++ [(0, ⟨n, input⟩)]) outside := by
  induction outside with
  | nil =>
    have h := BinderPack.local (n := n) ⟨n, input⟩ (Nat.le_refl n) BinderPack.nil
    simpa [Need.atGrade, Profile.union, Profile.empty, Profile.atoms, Profile.mk, Footprint.sourceLift] using h
  | cons entry rest ih =>
    obtain ⟨i, need⟩ := entry
    exact .external i need ih

theorem Obs.expandEtaAtomOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {atom : Atom n} {support : Profile n} {footprint typeFootprint : Footprint}
    (observation : Obs env U registry target locals τ f (.singleton atom) footprint)
    (resources : footprint.Available available)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) support typeFootprint)
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
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (_formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available) :
    Nonempty (EtaExpansionResult env U registry target locals σ τ available A B f (.singleton atom)) := by
  have origins := certificate.piOriginsOriginal henv hscoped hle hTarget closed context originalDomain originalBody
    substitutions.left fits.left.forward domainIH bodyIH typeAvailable
  have shape := origins.value_shape typed (List.mem_singleton_self _)
  cases n with
  | zero => exact shape.elim
  | succ n =>
    obtain ⟨key, output, normalEq⟩ := shape
    let normal : AtomView env U registry target atom (n := n + 1) (.fn key output) :=
      normalEq ▸ AdapterNormal.view henv atom
    have normalizedObs := Obs.view observation normal
    have normalizedCert := CodeCert.map normal certificate
    have normalizedTyped := normal.mapType_typed typed
    have normalizedRelated := normal.termMap henv hscoped hTarget related
    obtain ⟨resultSupport, ⟨row⟩, _⟩ := normalizedCert.piRowOriginal henv hscoped hle hTarget closed
      context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH
      typeAvailable normalizedTyped
    have child : GradedTransfer env U registry target locals σ τ available A A (.sort domainLevel) :=
      (domainIH target locals σ τ available closed hTarget substitutions fits).1
    obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed child row.domainAvailable
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
    have lifted := normalizedObs.renameSource (.skip .refl) (τ.cons key.anchor) rfl (Locals.push locals)
    have application : Obs env U registry target (Locals.push locals) (τ.cons key.anchor)
        (.app f.lift (.bvar 0)) (.singleton output)
        (footprint.sourceLift (.skip .refl) ++ [(0, ⟨n, key.input⟩)]) := by
      exact .app (by simpa only [← lift_eq_lift', Profile.fn] using lifted)
        (.var _ _ 0 key.input) (.refl _) row.anchor
    have expanded := Obs.lam domain.certificate guard application (etaPack key.input footprint)
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
      adapter := .cons (List.mem_singleton_self _) ((whole.inverse henv).toAdapter henv hscoped hTarget) (.nil _)
      support := _
      typeFootprint := typeFootprint ++ typeFootprint
      certificate := .union certificate (.map whole certificate)
      typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
        (typeAvailable i need) (typeAvailable i need)
      typed := requestedTyped
      rawTyped := rawTyped
      code := allCode
      related := by simpa only [eta_subst] using Related.retag henv requestedTyped allCode back
      rawRelated := by simpa only [eta_subst, Profile.fn] using Related.retag henv rawTyped allCode etaSelf }⟩

theorem Obs.expandEtaProfileOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile support : Profile n} {footprint typeFootprint : Footprint}
    (observation : Obs env U registry target locals τ f profile footprint)
    (resources : footprint.Available available)
    (certificate : CodeCert env U registry target locals σ (.forallE A B) support typeFootprint)
    (typeAvailable : typeFootprint.Available available)
    (typed : profile.HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) profile support)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available) :
    Nonempty (EtaExpansionResult env U registry target locals σ τ available A B f profile) := by
  have rawEta := IsDefEq.eta_subst_right henv hTarget substitutions formedA formedB functionTyped
  have go : ∀ selected : Profile n, List.Subset selected profile →
      Nonempty (EtaExpansionResult env U registry target locals σ τ available A B f selected) := by
    intro selected included
    induction selected with
    | nil => exact ⟨.empty⟩
    | cons atom rest ih =>
      have member := included List.mem_cons_self
      obtain ⟨selected⟩ := observation.atom member
      have localResources := selected.atomizes.available_closed resources closed
      obtain ⟨head⟩ := selected.observation.expandEtaAtomOriginal henv hscoped hle localResources certificate
        typeAvailable (typed.singleton_of_mem member) code
        (related.singleton_of_mem member) rawEta context originalDomain originalBody domainIH bodyIH
        formedA formedB closed hTarget substitutions fits
      obtain ⟨tail⟩ := ih (fun _ h => included (List.mem_cons_of_mem _ h))
      exact ⟨head.union henv tail⟩
  exact go profile (fun _ h => h)

theorem GradedTransferResult.etaExpandOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A B f : VExpr} {profile : Profile n}
    (result : GradedTransferResult env U registry target locals σ τ available f f (.forallE A B) profile)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) profile) := by
  obtain ⟨expanded⟩ := result.observation.expandEtaProfileOriginal henv hscoped hle
    result.resultAvailable result.certificate result.typeAvailable result.rawTyped result.typeCode
    result.rawRelated context originalDomain originalBody domainIH bodyIH formedA formedB functionTyped
    closed hTarget substitutions fits
  have requested := result.adapter.termMap henv hscoped hTarget result.typed result.typeCode expanded.related
  have cross := Related.trans henv hscoped result.related requested
  have code := code_union result.typeCode expanded.code
  have wf := result.typed.wf_type.union expanded.rawTyped.wf_type
  have typed := result.typed.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := expanded.rawTyped.enlarge (Profile.le_union_right _ _) wf
  exact ⟨{
    rank := result.rank
    bound := result.bound
    rawDemand := expanded.rawDemand
    resultFootprint := expanded.footprint
    observation := expanded.observation
    adapter := expanded.adapter.comp result.adapter
    resultAvailable := expanded.resultAvailable
    support := result.support.union expanded.support
    typeFootprint := result.typeFootprint ++ expanded.typeFootprint
    certificate := .union result.certificate expanded.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (result.typeAvailable i need) (expanded.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code cross
    rawRelated := Related.retag henv rawTyped code expanded.rawRelated }⟩

/-- Eta's two directions use the original function and its original type
formations; the generated lambda body is never an induction premise. -/
theorem OriginalTail.DerivationFundamental.eta
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (liftedBody : Derivation sourceEnv U (A.lift :: A :: source)
      (B.liftN 1 1) (B.liftN 1 1) (.sort bodyLevel))
    (function : Derivation sourceEnv U source f f (.forallE A B))
    (liftedFunction : Derivation sourceEnv U (A :: source) f.lift f.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation sourceEnv U (A :: source) A.lift A.lift (.sort domainLevel))
    (domainIH : DerivationFundamental env registry context domain)
    (bodyIH : DerivationFundamental env registry (.cons context (.left domain)) body)
    (functionIH : DerivationFundamental env registry context function) :
    DerivationFundamental env registry context
      (.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain) := by
  intro target locals σ τ available closed hTarget substitutions fits
  have functionChild : GradedTransfer env U registry target locals σ τ available f f (.forallE A B) :=
    (functionIH target locals σ τ available closed hTarget substitutions fits).1
  have forward : GradedTransfer env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) := by
    intro n demand footprint observation resources
    exact observation.etaContractOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      (domainIH.left henv hscoped) (bodyIH.left henv hscoped) functionChild
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits resources
  have backward : GradedTransfer env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) := by
    intro n demand footprint observation resources
    obtain ⟨result⟩ := functionChild observation resources
    exact result.etaExpandOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      (domainIH.left henv hscoped) (bodyIH.left henv hscoped)
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

/-- The only three semantic calls in eta are strict original children, with
the codomain charged under the original domain formation. -/
theorem OriginalTail.eta_schedule
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (liftedBody : Derivation sourceEnv U (A.lift :: A :: source)
      (B.liftN 1 1) (B.liftN 1 1) (.sort bodyLevel))
    (function : Derivation sourceEnv U source f f (.forallE A B))
    (liftedFunction : Derivation sourceEnv U (A :: source) f.lift f.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation sourceEnv U (A :: source) A.lift A.lift (.sort domainLevel)) :
    let parent := schedule .fundamental (Closure.close
      (Derivation.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain).origin
      context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close body.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close function.origin context.closures).cost < parent := by
  have parentBound : (Closure.close
      (etaLeftOrigin domain.origin body.origin liftedBody.origin liftedFunction.origin liftedDomain.origin)
      context.closures).cost < (Closure.close
      (Derivation.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain).origin
      context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have domainBound := binder_domain_cost domain.origin
    [body.origin, etaBodyOrigin body.origin liftedBody.origin liftedFunction.origin liftedDomain.origin]
    [] context.closures
  have bodyBound := binder_body_cost (domain := domain.origin)
    (bodies := [body.origin, etaBodyOrigin body.origin liftedBody.origin liftedFunction.origin liftedDomain.origin])
    (children := []) (body := body.origin) (by simp) context.closures
  exact ⟨schedule_strict (Nat.lt_trans domainBound parentBound) _ _,
    schedule_strict (Nat.lt_trans bodyBound parentBound) _ _,
    schedule_strict (original_child_same_environment (Origin.rule_child (by simp)) context.closures) _ _⟩

end Lean4Lean.AnchoredSource.Adapted
