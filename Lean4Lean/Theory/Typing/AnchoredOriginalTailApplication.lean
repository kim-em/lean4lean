import Lean4Lean.Theory.Typing.AnchoredOriginalPiReanchor
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedAppJoint

/-! Application transfer with fixed original formation calls and exact
captured source tails. Existing unrestricted application APIs are unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem CodeCert.piRowOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available)
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    {profile : Profile (n + 1)}
    (certificate : CodeCert env U registry target locals σ (.forallE A B) profile footprint)
    (resources : footprint.Available available)
    (typed : (Profile.fn (key : Key n) output).HasType profile) :
    ∃ result, Nonempty (PiRowCertificate env U registry target locals σ available A B key result) ∧
      (Profile.singleton output).HasType result := by
  obtain ⟨protoDomain, protoBody, domain, rows, result, member, _, _, _, row, resultTyped⟩ :=
    typed.fn_inv (List.mem_singleton_self _)
  have origins := certificate.piOriginsOriginal henv hscoped hle hTarget closed context
    originalDomain originalBody substitutions tail domainIH bodyIH resources
  exact ⟨result, origins _ member key result row, resultTyped⟩

private theorem DomainChain.backward
    (henv : env.Ordered)
    (chain : DomainChain env U registry Γ (input : Profile n) left right)
    (typed : input.HasType support) (formed : support.HasType (.sort true))
    (code : TypeRelated env U registry Γ right right support)
    (related : Related env U registry Γ x y right input support) :
    ∃ support, input.HasType support ∧ support.HasType (.sort true) ∧
      TypeRelated env U registry Γ left left support ∧
      Related env U registry Γ x y left input support := by
  induction chain with
  | refl => exact ⟨support, typed, formed, code, related⟩
  | step path ht hf bridge tail ih =>
    obtain ⟨_, _, _, _, pair⟩ := ih code related
    exact ⟨_, ht, hf, bridge.left_diagonal,
      Related.convert henv ht (bridge.symm henv ht.wf_type) pair⟩

private theorem admission_left
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key x x := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
  exact ⟨anchor, pair.hasType.1, support, typed, formed, code, first, Related.left_diagonal second⟩

private theorem admission_right
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, Related.left_diagonal (Related.symm henv second)⟩

private theorem PiRowCertificate.argumentPair
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (row : PiRowCertificate env U registry target locals σ available A B (key : Key n) result)
    (domainCode : TypeRelated env U registry target (A.subst σ) (A.subst σ) row.domainSupport)
    (argument : Related env U registry target x y (A.subst σ) rawInput support)
    (adapter : NormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target x y (A.subst σ))
    (admitted : Admitted env U registry target key x x) :
    Admitted env U registry target key x y := by
  have changed := adapter.termMap henv hscoped hTarget row.inputTyped domainCode argument
  obtain ⟨support, typed, formed, code, pair⟩ := DomainChain.backward henv row.alignment row.inputTyped
    row.domain.formed domainCode changed
  obtain ⟨anchor, _, _, _, _, _, first, _⟩ := admitted
  exact ⟨anchor, row.alignment.path.symm.cast raw, support, typed, formed, code,
    Related.retag henv typed code first, pair⟩

private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => left.singleton h) (fun h => right.singleton h)

theorem Obs.appTransferOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : EndpointFundamental env registry context originalDomain)
    (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : GradedTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : GradedTransfer env U registry target locals σ τ available a b A)
    (resultChild : GradedTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    (functionObservation : Obs env U registry target locals σ f (Profile.fn key output) functionFootprint)
    (argumentObservation : Obs env U registry target locals σ a rawInput argumentFootprint)
    (arguments : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) (.singleton output)) := by
  obtain ⟨fn⟩ := functionChild functionObservation functionAvailable
  obtain ⟨arg⟩ := argumentChild argumentObservation argumentAvailable
  have domainChild : GradedTransfer env U registry target locals σ σ available A A (.sort domainLevel) :=
    (domainIH target locals σ σ available closed hTarget substitutions.left fits.left).1
  obtain ⟨result, ⟨row⟩, outputTyped⟩ := fn.requestedCertificate.piRowOriginal henv hscoped hle hTarget
    closed context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH
    fn.typeAvailable fn.requestedTyped
  obtain ⟨domainCode⟩ := row.domain.transfer_graded henv hscoped hTarget closed domainChild row.domainAvailable
  have argumentRelated := arg.requestedRelated henv hTarget
  have paired := row.argumentPair henv hscoped hTarget domainCode.related argumentRelated arguments
    (rawArgument.substDF henv substitutions.wf hTarget substitutions) admitted
  have sourceLive := Related.live henv hscoped hTarget argumentRelated
  let sourceArgument : GradedResult env U registry target locals σ available a key.input :=
    { rank := n, bound := Nat.le_refl n, raw := rawInput, footprint := argumentFootprint,
      observation := argumentObservation, adapter := by simpa only [raiseProfile_self] using arguments,
      resources := argumentAvailable, live := sourceLive }
  obtain ⟨requestedCert⟩ := OriginalFactorCut.rowInstantiateOriginal henv hscoped hle hTarget closed
    context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH row admitted sourceArgument
  obtain ⟨requestedCode⟩ := requestedCert.certificate.transfer_graded henv hscoped hTarget closed
    resultChild requestedCert.resources
  have requestedRelated : Related env U registry target ((VExpr.app f a).subst σ)
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton output) result := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget outputTyped
      (by simpa only [subst_inst] using requestedCode.related)
      (by simpa only [subst] using fn.requestedRelated henv hTarget) paired
  let M := max fn.rank (arg.rank + 1) - 1
  have hfn : fn.rank ≤ M + 1 := by dsimp [M]; omega
  have harg : arg.rank ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by have := fn.bound; dsimp [M]; omega
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  have raisedFn := fn.observation.raise hfn
  have raisedArg := arg.observation.raise harg
  have raisedFnAdapter := NormalProfileAdapter.raise henv hscoped hTarget hfn fn.adapter
  simp only [raiseProfile_trans] at raisedFnAdapter
  have gradeView := functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) hn key output
  have functionAdapter : NormalProfileAdapter env U registry target
      (raiseProfile (M + 1) hfn fn.rawDemand) (Profile.fn highKey highOutput) := by
    change NormalProfileAdapter env U registry target _
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at raisedFnAdapter
    rw [raiseProfile_singleton] at raisedFnAdapter
    exact raisedFnAdapter.comp (.cons (List.mem_singleton_self _)
      (gradeView.toAdapter henv hscoped hTarget) (.nil _))
  have argumentAdapter : NormalProfileAdapter env U registry target
      (raiseProfile M harg arg.rawDemand) highKey.input := by
    have raised := NormalProfileAdapter.raise henv hscoped hTarget harg arg.adapter
    simp only [raiseProfile_trans] at raised
    exact raised.comp (NormalProfileAdapter.raise henv hscoped hTarget hn arguments)
  obtain ⟨factor⟩ := Obs.factor_application henv raisedFn functionAdapter raisedArg argumentAdapter
  let selectedView := AdapterNormal.view (U := U) (registry := registry) (Γ := target) henv factor.rawOrigin
  have selectedCertificate := CodeCert.map selectedView (fn.certificate.raise hfn)
  have selectedTyped := selectedView.mapType_typed
    ((Profile.HasType.raise hfn fn.rawTyped).singleton_of_mem factor.origin)
  have selectedRelated := selectedView.termMap henv hscoped hTarget
    ((Related.raise henv hfn fn.rawRelated).singleton_of_mem factor.origin)
  generalize selectedSupportEq : selectedView.mapType (raiseProfile (M + 1) hfn fn.support) =
    selectedSupport at selectedCertificate selectedTyped selectedRelated
  rw [factor.normalOrigin] at selectedTyped selectedRelated
  obtain ⟨rawResult, ⟨rawRow⟩, rawOutputTyped⟩ := selectedCertificate.piRowOriginal henv hscoped hle hTarget
    closed context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH
    fn.typeAvailable selectedTyped
  have highAdmission := Admitted.raise henv hn paired
  have actualAdmission := factor.keys.pull henv hscoped hTarget rawRow.anchor
    (AdapterNormal.normalizeAdmission henv hscoped hTarget highAdmission)
  have fixed : AdapterNormal.atom (n := M + 1) (.fn factor.key factor.output) =
      .fn factor.key factor.output := by
    rw [← factor.normalOrigin, AdapterNormal.atom_idem]
  have keyFixed := (AtomData.fn.inj fixed).1
  have inputFixed : AdapterNormal.profile factor.key.input = factor.key.input := congrArg KeyData.input keyFixed
  have sourceAdapter : NormalProfileAdapter env U registry target
      (raiseProfile M hn rawInput) factor.key.input := by
    change ProfileAdapter env U registry target _ (AdapterNormal.profile factor.key.input)
    rw [inputFixed]
    exact ProfileAdapter.comp (NormalProfileAdapter.raise henv hscoped hTarget hn arguments) factor.keys.arguments
  let rawSourceArgument : GradedResult env U registry target locals σ available a factor.key.input :=
    { rank := M, bound := Nat.le_refl M, raw := raiseProfile M hn rawInput,
      footprint := argumentFootprint, observation := argumentObservation.raise hn,
      adapter := by simpa only [raiseProfile_self] using sourceAdapter,
      resources := argumentAvailable, live := (raiseProfile_live_iff hn rawInput).mpr sourceLive }
  obtain ⟨rawCert⟩ := OriginalFactorCut.rowInstantiateOriginal henv hscoped hle hTarget closed
    context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH rawRow (admission_left actualAdmission) rawSourceArgument
  obtain ⟨rawCode⟩ := rawCert.certificate.transfer_graded henv hscoped hTarget closed
    resultChild rawCert.resources
  have rawPair : Related env U registry target (.app (g.subst τ) (a.subst σ))
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton factor.output) rawResult := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget rawOutputTyped
      (by simpa only [subst_inst] using rawCode.related)
      (by simpa only [subst, Profile.fn] using selectedRelated) actualAdmission
  have rawSelf := (rawPair.symm henv).left_diagonal
  have produced := Obs.app factor.functionObservation factor.argumentObservation factor.argumentAdapter
    (admission_right henv hscoped actualAdmission)
  have resultAdapter : NormalProfileAdapter env U registry target (.singleton factor.output)
      (raiseProfile M hn (.singleton output)) := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  have raisedTyped := Profile.HasType.raise hn outputTyped
  have raisedCode := TypeRelated.raise henv hn requestedCode.related
  have combinedCode := code_union raisedCode rawCode.related
  have wf := raisedTyped.wf_type.union rawOutputTyped.wf_type
  have finalTyped := raisedTyped.enlarge (Profile.le_union_left _ _) wf
  have finalRawTyped := rawOutputTyped.enlarge (Profile.le_union_right _ _) wf
  exact ⟨{
    rank := M, bound := hn, rawDemand := .singleton factor.output,
    resultFootprint := _, observation := produced, adapter := resultAdapter,
    resultAvailable := fun i need hm => (List.mem_append.mp hm).elim
      ((factor.selected.available_closed fn.resultAvailable closed) i need) (arg.resultAvailable i need),
    support := (raiseProfile M hn result).union rawResult,
    typeFootprint := requestedCert.footprint ++ rawCert.footprint,
    certificate := .union (requestedCert.certificate.raise hn) rawCert.certificate,
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (requestedCert.resources i need) (rawCert.resources i need),
    typed := finalTyped, rawTyped := finalRawTyped, typeCode := combinedCode,
    related := Related.retag henv finalTyped combinedCode (Related.raise henv hn requestedRelated),
    rawRelated := Related.retag henv finalRawTyped combinedCode rawSelf }⟩

section
variable {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
  (context : ContextDerivation sourceEnv U source)
  (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
  (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
  (domainIH : EndpointFundamental env registry context originalDomain)
  (bodyIH : StateFundamental env registry (.cons context originalDomain) originalBody)
  (functionChild : GradedTransfer env U registry target locals σ τ available f g (.forallE A B))
  (argumentChild : GradedTransfer env U registry target locals σ τ available a b A)
  (resultChild : GradedTransfer env U registry target locals σ σ available
    (B.inst a) (B.inst a) (.sort bodyLevel))
  (rawArgument : env.IsDefEq U source a b A)
  (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (fits : TailPairedFits env registry target context locals σ τ available)

include henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild argumentChild resultChild
  rawArgument closed hTarget substitutions fits in
 theorem Obs.applicationOriginal
    (observation : Obs env U registry target locals σ (.app f a) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app fn arg arguments admitted =>
    exact Obs.appTransferOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
      argumentChild resultChild rawArgument closed hTarget substitutions fits
      fn arg arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := left.applicationOriginal
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.applicationOriginal
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨value⟩ := source.applicationOriginal resources
    exact ⟨value.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨value⟩ := source.applicationOriginal resources
    exact ⟨value.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨value⟩ := source.applicationOriginal resources
    exact ⟨value.unpad⟩
  | .rowShift source =>
    obtain ⟨value⟩ := source.applicationOriginal resources
    exact ⟨(value.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

include henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild argumentChild resultChild
  rawArgument closed hTarget substitutions fits in
 theorem GradedTransfer.appOriginal :
    GradedTransfer env U registry target locals σ τ available (.app f a) (.app g b) (B.inst a) := by
  intro n demand footprint observation resources
  exact observation.applicationOriginal henv hscoped hle context originalDomain originalBody domainIH bodyIH functionChild
    argumentChild resultChild rawArgument closed hTarget substitutions fits resources

end


theorem GradedTransfer.convertAnswer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right A B : VExpr}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (producer : GradedTransfer env U registry target locals σ σ available A B (.sort level))
    (originalTerm : GradedTransfer env U registry target locals σ τ available left right A) :
    GradedTransfer env U registry target locals σ τ available left right B := by
  intro n demand footprint observation resources
  obtain ⟨value⟩ := originalTerm observation resources
  obtain ⟨type⟩ := value.certificate.transfer_graded henv hscoped hTarget closed producer value.typeAvailable
  exact ⟨{
    rank := value.rank
    bound := value.bound
    rawDemand := value.rawDemand
    adapter := value.adapter
    resultFootprint := value.resultFootprint
    observation := value.observation
    resultAvailable := value.resultAvailable
    support := value.support
    typeFootprint := type.footprint
    certificate := type.certificate
    typeAvailable := type.available
    typed := value.typed
    rawTyped := value.rawTyped
    typeCode := TypeRelated.left_diagonal (TypeRelated.symm henv value.typed.wf_type type.related)
    rawRelated := Related.convert henv value.rawTyped type.related value.rawRelated
    related := Related.convert henv value.typed type.related value.related }⟩

/-- Every fundamental call in application transfer is smaller at its exact
original captured source context, including the codomain binder. -/
theorem OriginalTail.appDF_schedule
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (function : Derivation sourceEnv U source f g (.forallE A B))
    (argument : Derivation sourceEnv U source a b A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst b) (.sort bodyLevel)) :
    let parent := schedule .fundamental (Closure.close
      (Derivation.appDF domainWF bodyWF domain body function argument result).origin context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close body.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close function.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close argument.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close result.origin context.closures).cost < parent := by
  have parentBound : (Closure.close
      (applicationOrigin domain.origin body.origin function.origin argument.origin result.origin)
      context.closures).cost < (Closure.close
      (Derivation.appDF domainWF bodyWF domain body function argument result).origin context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have domainBound := binder_domain_cost domain.origin [body.origin]
    [function.origin, argument.origin, result.origin] context.closures
  have bodyBound := binder_body_cost (domain := domain.origin) (bodies := [body.origin])
    (children := [function.origin, argument.origin, result.origin]) (body := body.origin)
    (by simp) context.closures
  have functionBound := binder_other_cost (domain := domain.origin) (bodies := [body.origin])
    (children := [function.origin, argument.origin, result.origin]) (child := function.origin)
    (by simp) context.closures
  have argumentBound := binder_other_cost (domain := domain.origin) (bodies := [body.origin])
    (children := [function.origin, argument.origin, result.origin]) (child := argument.origin)
    (by simp) context.closures
  have resultBound := binder_other_cost (domain := domain.origin) (bodies := [body.origin])
    (children := [function.origin, argument.origin, result.origin]) (child := result.origin)
    (by simp) context.closures
  exact ⟨schedule_strict (Nat.lt_trans domainBound parentBound) _ _,
    schedule_strict (Nat.lt_trans bodyBound parentBound) _ _,
    schedule_strict (Nat.lt_trans functionBound parentBound) _ _,
    schedule_strict (Nat.lt_trans argumentBound parentBound) _ _,
    schedule_strict (Nat.lt_trans resultBound parentBound) _ _⟩

/-- The original five appDF children suffice at their exact captured source
contexts. No child is strengthened to arbitrary untracked fitted contexts. -/
theorem OriginalTail.DerivationFundamental.appDF
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
    (domainIH : DerivationFundamental env registry context domain)
    (bodyIH : DerivationFundamental env registry (.cons context (.left domain)) body)
    (functionIH : DerivationFundamental env registry context function)
    (argumentIH : DerivationFundamental env registry context argument)
    (resultIH : DerivationFundamental env registry context result) :
    DerivationFundamental env registry context (.appDF domainWF bodyWF domain body function argument result) := by
  intro target locals σ τ available closed hTarget substitutions fits
  have functionAnswer := functionIH target locals σ τ available closed hTarget substitutions fits
  have argumentAnswer := argumentIH target locals σ τ available closed hTarget substitutions fits
  have resultAnswer := resultIH target locals σ σ available closed hTarget substitutions.left fits.left
  have resultLeft : GradedTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel) :=
    (resultIH.left henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left).1
  have resultRight : GradedTransfer env U registry target locals σ σ available
      (B.inst b) (B.inst b) (.sort bodyLevel) :=
    (resultIH.right henv hscoped target locals σ σ available closed hTarget substitutions.left fits.left).1
  have forward : GradedTransfer env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) :=
    GradedTransfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      (domainIH.left henv hscoped) (bodyIH.left henv hscoped) functionAnswer.1 argumentAnswer.1 resultLeft
      (argument.forget.defeq.mono hle) closed hTarget substitutions fits
  have backwardNatural : GradedTransfer env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst b) :=
    GradedTransfer.appOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      (domainIH.left henv hscoped) (bodyIH.left henv hscoped) functionAnswer.2.1 argumentAnswer.2.1 resultRight
      (argument.forget.defeq.mono hle).symm closed hTarget substitutions fits
  have backward : GradedTransfer env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst a) :=
    GradedTransfer.convertAnswer henv hscoped closed hTarget resultAnswer.2.1 backwardNatural
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

end Lean4Lean.AnchoredSource.Adapted
