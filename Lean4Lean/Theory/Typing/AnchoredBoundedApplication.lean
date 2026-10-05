import Lean4Lean.Theory.Typing.AnchoredBoundedPiExtraction
import Lean4Lean.Theory.Typing.AnchoredBoundedInstantiation
import Lean4Lean.Theory.Typing.AnchoredBoundedConversion
import Lean4Lean.Theory.Typing.AnchoredApplication

/-! Dependent application consumes actual source Pi rows and the original
argument and codomain children. Both computational children may change grade
and demand; their finite adapters are cut at the selected returned row. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

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
    (row : PiRowCertificate current fuel env U registry target locals σ available A B (key : Key n) result)
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

private theorem PiRowCertificate.instantiate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation} {A B argument : VExpr}
    (closed : available.AtomClosed)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (row : PiRowCertificate current fuel env U registry target locals σ available A B (key : Key n) result)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (argumentResult : Substitution.GradedResult current fuel env U registry target locals σ available argument key.input) :
    Nonempty (Substitution.CertificateResult current fuel env U registry target locals σ available (B.inst argument) result) := by
  obtain ⟨anchored⟩ := row.reanchor henv hscoped hTarget closed formedA substitutions fits
    originalDomain originalBody admitted
  have bodyScope := formedB.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, formedA⟩)
  have outsideLive := fits.forward.forget.leavesLive henv hscoped hTarget anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped bodyScope))
  exact Substitution.CodeCert.instantiate henv hscoped hTarget closed anchored.body anchored.bodyBound argumentResult
    anchored.pack anchored.covered anchored.outsideAvailable outsideLive

private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => left.singleton h) (fun h => right.singleton h)

/-- The dependent application rule uses only its original formation, term,
and instantiated-result children. The returned raw application is rebuilt
from the actual normalized function row and the actual returned argument. -/
theorem Obs.app_transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : Joint current fuel env U registry source f g (.forallE A B))
    (originalArgument : Joint current fuel env U registry source a b A)
    (originalResult : Joint current fuel env U registry source (B.inst a) (B.inst b) (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (functionObservation : Obs env U registry target locals σ f (Profile.fn key output) functionFootprint)
    (argumentObservation : Obs env U registry target locals σ a rawInput argumentFootprint)
    (functionBound : functionObservation.nativeDepth current ≤ fuel)
    (argumentBound : argumentObservation.nativeDepth current ≤ fuel)
    (arguments : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) (.singleton output)) := by
  obtain ⟨fn⟩ := (originalFunction target locals σ τ available closed hTarget substitutions fits).1
    functionObservation functionBound functionAvailable
  obtain ⟨arg⟩ := (originalArgument target locals σ τ available closed hTarget substitutions fits).1
    argumentObservation argumentBound argumentAvailable
  have domainChild : Transfer current fuel env U registry target locals σ σ available A A (.sort domainLevel) :=
    (originalDomain target locals σ σ available closed hTarget substitutions.left fits.left).1
  have resultChild : Transfer current fuel env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel) :=
    ((originalResult.left henv hscoped) target locals σ σ available closed hTarget substitutions.left fits.left).1
  obtain ⟨result, ⟨row⟩, outputTyped⟩ := CodeCert.piRow henv hscoped hTarget
    closed formedA formedB substitutions.left fits.left originalDomain originalBody
    fn.toGradedTransferResult.requestedCertificate
    (by simpa only [GradedTransferResult.requestedCertificate, CodeCert.nativeDepth_lower] using fn.certificateBound)
    fn.typeAvailable fn.toGradedTransferResult.requestedTyped
  obtain ⟨domainCode⟩ := domainChild.codeCertificate henv hscoped hTarget closed row.domain row.domainBound row.domainAvailable
  have argumentRelated := arg.toGradedTransferResult.requestedRelated henv hTarget
  have paired := row.argumentPair henv hscoped hTarget domainCode.related argumentRelated arguments
    (rawArgument.substDF henv substitutions.wf hTarget substitutions) admitted
  have sourceLive := Related.live henv hscoped hTarget argumentRelated
  let sourceArgument : Substitution.GradedResult current fuel env U registry target locals σ available a key.input :=
    { rank := n, bound := Nat.le_refl n, raw := rawInput, footprint := argumentFootprint,
      observation := argumentObservation, adapter := by simpa only [raiseProfile_self] using arguments,
      resources := argumentAvailable, live := sourceLive, observationBound := argumentBound }
  obtain ⟨requestedCert⟩ := row.instantiate henv hscoped hTarget closed formedA formedB
    substitutions.left fits.left originalDomain originalBody admitted sourceArgument
  obtain ⟨requestedCode⟩ := resultChild.codeCertificate henv hscoped hTarget closed
    requestedCert.certificate requestedCert.certificateBound requestedCert.resources
  have requestedRelated : Related env U registry target ((VExpr.app f a).subst σ)
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton output) result := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget outputTyped
      (by simpa only [subst_inst] using requestedCode.related)
      (by simpa only [subst] using fn.toGradedTransferResult.requestedRelated henv hTarget) paired
  let M := max fn.rank (arg.rank + 1) - 1
  have hfn : fn.rank ≤ M + 1 := by dsimp [M]; omega
  have harg : arg.rank ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by have := fn.bound; dsimp [M]; omega
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  let raisedFn := fn.observation.raise hfn
  let raisedArg := arg.observation.raise harg
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
  obtain ⟨factor⟩ := Substitution.Obs.factor_application (current := current) henv raisedFn functionAdapter raisedArg argumentAdapter
  let selectedView := AdapterNormal.view (U := U) (registry := registry) (Γ := target) henv factor.rawOrigin
  let selectedCertificate := CodeCert.map selectedView (fn.certificate.raise hfn)
  have selectedBound : selectedCertificate.nativeDepth current ≤ fuel := by
    simpa only [selectedCertificate, CodeCert.nativeDepth, CodeCert.nativeDepth_raise] using fn.certificateBound
  have selectedTyped := selectedView.mapType_typed
    ((Profile.HasType.raise hfn fn.rawTyped).singleton_of_mem factor.origin)
  have selectedRelated := selectedView.termMap henv hscoped hTarget
    ((Related.raise henv hfn fn.rawRelated).singleton_of_mem factor.origin)
  clear_value selectedCertificate
  generalize selectedSupportEq : selectedView.mapType (raiseProfile (M + 1) hfn fn.support) =
    selectedSupport at selectedCertificate selectedTyped selectedRelated selectedBound
  rw [factor.normalOrigin] at selectedTyped selectedRelated
  obtain ⟨rawResult, ⟨rawRow⟩, rawOutputTyped⟩ := CodeCert.piRow henv hscoped hTarget
    closed formedA formedB substitutions.left fits.left originalDomain originalBody
    selectedCertificate selectedBound fn.typeAvailable selectedTyped
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
  let rawSourceArgument : Substitution.GradedResult current fuel env U registry target locals σ available a factor.key.input :=
    { rank := M, bound := Nat.le_refl M, raw := raiseProfile M hn rawInput,
      footprint := argumentFootprint, observation := argumentObservation.raise hn,
      adapter := by simpa only [raiseProfile_self] using sourceAdapter,
      resources := argumentAvailable, live := (raiseProfile_live_iff hn rawInput).mpr sourceLive,
      observationBound := by simpa only [Obs.nativeDepth_raise] using argumentBound }
  obtain ⟨rawCert⟩ := rawRow.instantiate henv hscoped hTarget closed formedA formedB
    substitutions.left fits.left originalDomain originalBody (admission_left actualAdmission) rawSourceArgument
  obtain ⟨rawCode⟩ := resultChild.codeCertificate henv hscoped hTarget closed
    rawCert.certificate rawCert.certificateBound rawCert.resources
  have rawPair : Related env U registry target (.app (g.subst τ) (a.subst σ))
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton factor.output) rawResult := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget rawOutputTyped
      (by simpa only [subst_inst] using rawCode.related)
      (by simpa only [subst, Profile.fn] using selectedRelated) actualAdmission
  have rawSelf := (rawPair.symm henv).left_diagonal
  let produced := Obs.app factor.functionObservation raisedArg factor.argumentAdapter
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
    rawRelated := Related.retag henv finalRawTyped combinedCode rawSelf
    observationBound := by
      simp only [produced, Obs.nativeDepth]
      exact Nat.max_le.mpr ⟨Nat.le_trans factor.selectionBound
        (by simpa only [raisedFn, Obs.nativeDepth_raise] using fn.observationBound),
        by simpa only [raisedArg, Obs.nativeDepth_raise] using arg.observationBound⟩
    certificateBound := by
      simpa only [CodeCert.nativeDepth, CodeCert.nativeDepth_raise] using
        Nat.max_le.mpr ⟨requestedCert.certificateBound, rawCert.certificateBound⟩ }⟩

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  (henv : env.Ordered) (hscoped : registry.Scoped)
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
  (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
  (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
  (originalFunction : Joint current fuel env U registry source f g (.forallE A B))
  (originalArgument : Joint current fuel env U registry source a b A)
  (originalResult : Joint current fuel env U registry source (B.inst a) (B.inst b) (.sort bodyLevel))
  (formedA : env.HasType U source A (.sort domainLevel))
  (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
  (rawArgument : env.IsDefEq U source a b A)
  (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (fits : PairedFits current fuel env U registry source target locals σ τ available)

include henv hscoped originalDomain originalBody originalFunction originalArgument originalResult
  formedA formedB rawArgument closed hTarget substitutions fits in
 theorem Obs.application
    (observation : Obs env U registry target locals σ (.app f a) demand footprint)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app fn arg arguments admitted =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using observationBound)
    exact Obs.app_transfer henv hscoped originalDomain originalBody originalFunction
      originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits
      fn arg bounds.1 bounds.2 arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using observationBound)
    obtain ⟨a⟩ := Obs.application left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := Obs.application right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨value⟩ := Obs.application source (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨Result.view henv hscoped hTarget change value⟩
  | .pad source =>
    obtain ⟨value⟩ := Obs.application source (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨value.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨value⟩ := Obs.application source (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨value.unpad⟩
  | .rowShift source =>
    obtain ⟨value⟩ := Obs.application source (by simpa only [Obs.nativeDepth] using observationBound) resources
    exact ⟨Result.view henv hscoped hTarget (.commutePadFn _ _) (value.pad henv hscoped hTarget)⟩
termination_by sizeOf observation

include henv hscoped originalDomain originalBody originalFunction originalArgument originalResult
  formedA formedB rawArgument closed hTarget substitutions fits in
 theorem Transfer.appDF :
    Transfer current fuel env U registry target locals σ τ available (.app f a) (.app g b) (B.inst a) := by
  intro n demand footprint observation observationBound resources
  exact Obs.application henv hscoped originalDomain originalBody originalFunction originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits observation observationBound resources

end

/-- Both endpoint transfers and sort correctness are consequences of the
original five semantic children of appDF, with no added typing premise. -/
theorem Joint.appDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : Joint current fuel env U registry source f g (.forallE A B))
    (originalArgument : Joint current fuel env U registry source a b A)
    (originalResult : Joint current fuel env U registry source (B.inst a) (B.inst b) (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A) :
    Joint current fuel env U registry source (.app f a) (.app g b) (B.inst a) := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : Transfer current fuel env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) := Transfer.appDF henv hscoped originalDomain originalBody originalFunction
    originalArgument originalResult formedA formedB rawArgument closed hTarget substitutions fits
  have backward : Transfer current fuel env U registry target locals σ τ available
      (.app g b) (.app f a) (B.inst b) :=
    Transfer.appDF henv hscoped originalDomain originalBody originalFunction.symm
      originalArgument.symm originalResult.symm formedA formedB rawArgument.symm
      closed hTarget substitutions fits
  exact ⟨forward, Transfer.convert henv hscoped originalResult.symm closed hTarget
    substitutions fits backward⟩


end Lean4Lean.AnchoredSource.Adapted.Staged
