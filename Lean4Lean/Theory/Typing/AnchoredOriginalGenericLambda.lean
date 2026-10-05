import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPi
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda
import Lean4Lean.Theory.Typing.AnchoredNativeBinderInterpretation

/-! Native lambda interpretation uses the actual original body and codomain
occurrences. The body's returned assigned-type query crosses their strictly
smaller same-expression comparison before it becomes a literal Pi row. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private extended_environment_bound from Lean4Lean.Theory.Typing.AnchoredOriginalClosureMeasure
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false

private theorem binder_two_bodies (domain first second : Origin) (captured : List Closure) :
    (Closure.close first (.close domain captured :: captured)).cost +
      (Closure.close second (.close domain captured :: captured)).cost <
        (Closure.close (.binder domain [first, second] []) captured).cost := by
  have bounded := Nat.mul_le_mul_left (first.weight + second.weight)
    (extended_environment_bound domain captured)
  have strict : (first.weight + second.weight) * (1 + domain.weight) <
      (Origin.binder domain [first, second] []).weight := by
    simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  rw [← Nat.mul_assoc] at bounded
  have result := Nat.lt_of_le_of_lt bounded
    (Nat.mul_lt_mul_of_pos_right strict (show 0 < 1 + environmentCost captured by omega))
  simpa only [Closure.cost, Nat.add_mul, Nat.mul_assoc] using result

/-- Both sides of the same-expression comparison are actual original
formation occurrences in the same computed binder frame. -/
theorem lambda_formation_pair_schedule
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U) (captured : List Closure) :
    (Closure.close (body.typeFormation.node.dependencyOrigin ordered)
      (.close (domain.dependencyOrigin ordered) captured :: captured)).cost +
    (Closure.close (codomain.dependencyOrigin ordered)
      (.close (domain.dependencyOrigin ordered) captured :: captured)).cost <
    (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered) captured).cost := by
  have bounded := body.typeFormation_dependency_cost_le ordered
    (.close (domain.dependencyOrigin ordered) captured :: captured)
  have strict := binder_two_bodies (domain.dependencyOrigin ordered)
    (codomain.dependencyOrigin ordered) (body.dependencyOrigin ordered) captured
  change _ < (Closure.close (.binder (domain.dependencyOrigin ordered)
    [codomain.dependencyOrigin ordered, body.dependencyOrigin ordered] []) captured).cost
  omega

variable {root : EndpointRef sourceEnv U rootSource rootExpression rootType}

/-- The fixed body F call uses a concrete frame assembled from the retained
binder query. It can run at any actual admitted right argument. -/
theorem OriginalRichFrame.lambdaBodyStep
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered) (initialContext : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv (.ref domain) codomain body))
    (lineage : location.contextDerivation initialContext = context)
    (bodyF : OriginalComputationalInductionAt env registry ordered initialContext (.lamBody location) limit)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (bound : (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    {output : Atom n}
    (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (.singleton output) footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : outside.Available available)
    (admitted : Admitted env U registry target key key.anchor z) :
    Nonempty (RichComputationalValue sourceEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (τ.cons z)
      (available.push (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons)) (.singleton output)) := by
  unfold OriginalComputationalInductionAt at bodyF
  have selected : Classical.choose location.originalDomains.1 = domain := by
    exact (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1)).symm
  have bodyLineage : (Located.lamBody location).contextDerivation initialContext = .cons context domain := by
    change ContextDerivation.cons (location.contextDerivation initialContext)
      (Classical.choose location.originalDomains.1) = _
    rw [selected, lineage]
  rw [bodyLineage] at bodyF
  let needs := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  obtain ⟨_, raw, _, _, _, _, _, pair⟩ := admitted
  let child := OriginalRichFrame.bind frame domain domainCode domainAvailable guard.inputTyped
    (Related.convert henv guard.inputTyped guard.domains pair) needs
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
  have smaller : (Closure.close (body.dependencyOrigin ordered)
      (child.dependencyEnvironment ordered)).cost < limit :=
    Nat.lt_of_lt_of_le (binder_body_cost (by simp) _) bound
  exact bodyF target (Locals.push locals) (σ.cons key.anchor) (τ.cons z) (available.push needs)
    child smaller (Valuation.push_atomized_closed closed _) formed
    (.cons substitutions (domain.sound.defeq.mono sourceBelow) (guard.path.cast raw))
    observation (pack.available_atomized_localNeeds resources)

/-- Only this fixed pair of actual formation occurrences is requested by
lambda type reconstruction; the frame and pair budget are explicit. -/
def LambdaCodomainInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    (context : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B) (limit : Nat) : Prop :=
  ∀ target locals σ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain) locals σ σ available,
    richSchedule .expressionReindex
      ((Closure.close (body.typeFormation.node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
        (Closure.close (codomain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ σ (A :: source) →
    RichCodeTransfer env U registry target body.typeFormation.node codomain locals locals σ σ available available

structure RichLambdaAnchor
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A B : VExpr} {v : VLevel}
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (locals : List Nat) (σ : Subst) (available : Valuation) (needs : List Need)
    (key : Key n) (output : Atom n) where
  support : Profile n
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target codomain (Locals.push locals)
    (σ.cons key.anchor) true support footprint
  resources : footprint.Available (available.push needs)
  typed : (Profile.singleton output).HasType support
  typeCode : TypeRelated env U registry target (B.subst (σ.cons key.anchor))
    (B.subst (σ.cons key.anchor)) support

/-- Produce the actual declared codomain row from the body child's returned
assigned-type certificate. No source certificate is relabelled. -/
theorem OriginalRichFrame.lambdaAnchorStep
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered) (initialContext : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv (.ref domain) codomain body))
    (lineage : location.contextDerivation initialContext = context)
    (bodyF : OriginalComputationalInductionAt env registry ordered initialContext (.lamBody location) limit)
    (codomainR : LambdaCodomainInductionAt env registry ordered context domain codomain body limit)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (bound : (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost ≤ limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    {output : Atom n}
    (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (.singleton output) footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : outside.Available available) :
    Nonempty (RichLambdaAnchor sourceEnv env U registry target codomain locals σ available
      (footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons) key output) := by
  obtain ⟨answer⟩ := frame.lambdaBodyStep henv sourceBelow ordered initialContext domain codomain body hu hv
    location lineage bodyF bound closed formed substitutions domainCode domainAvailable guard observation pack covered resources guard.anchor
  let needs := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  obtain ⟨raw, _, _, _, _, _, _, pair⟩ := guard.anchor
  let child := OriginalRichFrame.bind frame domain domainCode domainAvailable guard.inputTyped
    (Related.convert henv guard.inputTyped guard.domains pair) needs
    (fun need member => (pack.atomized_localNeeds need member).1)
    (fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present))
  have smaller : (Closure.close (body.typeFormation.node.dependencyOrigin ordered)
      (child.dependencyEnvironment ordered)).cost +
      (Closure.close (codomain.dependencyOrigin ordered) (child.dependencyEnvironment ordered)).cost < limit :=
    Nat.lt_of_lt_of_le (lambda_formation_pair_schedule ordered domain codomain body hu hv
      (frame.dependencyEnvironment ordered)) bound
  have sourcePair : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) :=
    .cons substitutions (domain.sound.defeq.mono sourceBelow) (guard.path.cast raw)
  obtain ⟨changed⟩ := codomainR target (Locals.push locals) (σ.cons key.anchor) (available.push needs)
    child (richSchedule_strict smaller _ _) (Valuation.push_atomized_closed closed _) formed sourcePair
    answer.certificate answer.resources
  exact ⟨⟨answer.support, changed.footprint, changed.certificate, changed.resources, answer.typed, changed.related⟩⟩

private theorem codeInduction_mono
    {location : Located root node}
    (induction : OriginalCodeInductionAt env registry ordered initialContext location larger)
    (bound : smaller ≤ larger) :
    OriginalCodeInductionAt env registry ordered initialContext location smaller := by
  intro target locals σ τ available frame cost closed formed substitutions
  exact induction target locals σ τ available frame (Nat.lt_of_lt_of_le cost bound) closed formed substitutions

private theorem pi_lambda_cost_le
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U) (captured : List Closure) :
    (Closure.close ((EndpointState.pi hu hv (.ref domain) codomain).dependencyOrigin ordered) captured).cost ≤
    (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered) captured).cost := by
  apply Nat.mul_le_mul_right
  simp only [EndpointState.dependencyOrigin, Origin.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_mul]
  omega

private theorem lambda_anchor_beta
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domain : env.HasType U source A (.sort u))
    (codomain : env.HasType U (A :: source) B (.sort v))
    (body : env.HasType U (A :: source) b B)
    (arguments : env.IsDefEq U target x y (A.subst σ))
    (related : Related env U registry target (b.subst (σ.cons x)) (b.subst (τ.cons y))
      (B.subst (σ.cons x)) input support) :
    Related env U registry target (.app ((VExpr.lam A b).subst σ) x)
      (.app ((VExpr.lam A b).subst τ) y) (B.subst (σ.cons x)) input support := by
  have rightSubst := substitutions.right henv formed
  have sourceWF : OnCtx (A :: source) (env.IsType U) := ⟨substitutions.wf, _, domain⟩
  have leftContext : OnCtx (A.subst σ :: target) (env.IsType U) :=
    ⟨formed, _, domain.subst henv substitutions.left formed⟩
  have rightContext : OnCtx (A.subst τ :: target) (env.IsType U) :=
    ⟨formed, _, domain.subst henv rightSubst formed⟩
  have leftBody := body.subst henv (substitutions.left.lift henv domain) leftContext
  have rightBody := body.subst henv (rightSubst.lift henv domain) rightContext
  have domains := domain.substDF henv substitutions.wf formed substitutions
  have rightArgument := IsDefEq.defeqDF domains arguments.hasType.2
  have paired : Ctx.SubstEq env U target (σ.cons x) (τ.cons y) (A :: source) :=
    .cons substitutions domain arguments
  have bodies := codomain.substDF henv sourceWF formed paired
  simp only [subst_sort] at domains bodies
  have leftBeta := IsDefEq.beta leftBody arguments.hasType.1
  have rightBeta := IsDefEq.beta rightBody rightArgument
  simp only [inst_lift_cons] at leftBeta rightBeta
  have rightBeta := IsDefEq.defeqDF bodies.symm rightBeta
  have leftHead : HeadBeta (.app ((VExpr.lam A b).subst σ) x) (b.subst (σ.cons x)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A.subst σ) (body := b.subst σ.lift) (argument := x) (trailing := []))
  have rightHead : HeadBeta (.app ((VExpr.lam A b).subst τ) y) (b.subst (τ.cons y)) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, inst_lift_cons] using
      (HeadBeta.contract (A := A.subst τ) (body := b.subst τ.lift) (argument := y) (trailing := []))
  exact Related.headBeta henv leftHead rightHead leftBeta rightBeta related

/-- Paired native lambda F reconstructs its actual assigned Pi certificate
and its right source observation from the fixed original children. -/
theorem OriginalRichFrame.nativeLambdaComputationalStep
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (ordered : sourceEnv.Ordered) (initialContext : ContextDerivation sourceEnv U rootSource)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) b B)
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.lam hu hv (.ref domain) codomain body))
    (lineage : location.contextDerivation initialContext = context)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (domainF : OriginalCodeInductionAt env registry ordered initialContext (.lamDomain location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (codomainF : OriginalCodeInductionAt env registry ordered initialContext (.lamCodomain location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (bodyF : OriginalComputationalInductionAt env registry ordered initialContext (.lamBody location)
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (codomainR : LambdaCodomainInductionAt env registry ordered context domain codomain body
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true (ambient : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A (key : Key n) ambient)
    {output : Atom n}
    (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
      (σ.cons key.anchor) (.singleton output) footprint)
    (pack : BinderPack n packed footprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (resources : outside.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target
      (.lam hu hv (.ref domain) codomain body) locals σ τ available (Profile.fn key output)) := by
  have selected : Classical.choose location.originalDomains.1 = domain :=
    (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1)).symm
  have domainLineage : (Located.lamDomain location).contextDerivation initialContext = context := by
    change location.contextDerivation initialContext = context
    exact lineage
  have codomainLineage : (Located.lamCodomain location).contextDerivation initialContext = .cons context domain := by
    change ContextDerivation.cons (location.contextDerivation initialContext)
      (Classical.choose location.originalDomains.1) = _
    rw [selected, lineage]
  have diagonalBound : (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
      (frame.leftDiagonal.dependencyEnvironment ordered)).cost ≤
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    exact Nat.le_refl _
  obtain ⟨anchor⟩ := frame.leftDiagonal.lambdaAnchorStep henv sourceBelow ordered initialContext domain codomain body
    hu hv location lineage bodyF codomainR diagonalBound closed formed substitutions.left
    domainCode domainAvailable guard observation pack covered resources
  let needs := footprint.localNeeds ++ footprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n := fun need member => (pack.atomized_localNeeds need member).1
  have coverage : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
  obtain ⟨newPacked, newOutside, newPack, newCovered, newResources⟩ :=
    Footprint.pack_available anchor.resources bounded coverage
  let rows : RichRows sourceEnv env U registry target (.ref domain) codomain locals σ true ambient
      [(key, anchor.support)] (newOutside ++ []) :=
    .cons guard anchor.certificate newPack newCovered .nil
  have rowResources : (newOutside ++ []).Available available := by simpa only [List.append_nil] using newResources
  let typeCertificate := RichCert.pi hu hv domainCode PiGuard.literal rows
  have typeResources : (domainFootprint ++ (newOutside ++ [])).Available available :=
    fun index need member => (List.mem_append.mp member).elim (domainAvailable index need) (rowResources index need)
  have piBound := pi_lambda_cost_le ordered domain codomain body hu hv (frame.dependencyEnvironment ordered)
  have piBoundDiagonal : (Closure.close ((EndpointState.pi hu hv (.ref domain) codomain).dependencyOrigin ordered)
      (frame.leftDiagonal.dependencyEnvironment ordered)).cost ≤
      (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    simpa only [OriginalRichFrame.dependencyEnvironment_leftDiagonal] using piBound
  obtain ⟨typeAnswer⟩ := frame.leftDiagonal.nativePiStep henv hscoped sourceBelow ordered initialContext
    domain (.lamDomain location) domainLineage codomain (.lamCodomain location) codomainLineage hu hv
    (codeInduction_mono domainF piBoundDiagonal) (codeInduction_mono codomainF piBoundDiagonal)
    closed formed substitutions.left domainCode domainAvailable PiGuard.literal rows rowResources
  have typed : (Profile.fn key output).HasType
      (Profile.pi (A.subst σ) (B.subst σ.lift) ambient [(key, anchor.support)]) :=
    Profile.HasType.fn typeCertificate.formed.wf_value (List.mem_singleton_self _) anchor.typed
  have rawDomain := domain.sound.defeq.mono sourceBelow
  have rawCodomain := codomain.sound.defeq.mono sourceBelow
  have rawBody := body.sound.defeq.mono sourceBelow
  have rawA : env.IsType U target (A.subst σ) := ⟨_, rawDomain.subst henv substitutions.left formed⟩
  have rawB : env.IsType U (A.subst σ :: target) (B.subst σ.lift) :=
    ⟨_, rawCodomain.subst henv (substitutions.left.lift henv rawDomain) ⟨formed, rawA⟩⟩
  have related : Related env U registry target ((VExpr.lam A b).subst σ) ((VExpr.lam A b).subst τ)
      ((VExpr.forallE A B).subst σ) (Profile.fn key output)
      (Profile.pi (A.subst σ) (B.subst σ.lift) ambient [(key, anchor.support)]) := by
    apply Related.nativeBinder henv hscoped formed rawA rawB typeAnswer.related
      (List.mem_singleton_self _) anchor.typed anchor.typed.wf_type
      guard.inputTyped guard.formed guard.path guard.domains guard.anchor
      (origin := .app ((VExpr.lam A b).subst σ) key.anchor)
    intro next ρ future z admitted
    let query' := observation.future henv future
    have guard' := guard.future henv future
    have domain' := domainCode.future henv future
    have queryTyped : (Profile.singleton (output.rename ρ)).HasType (anchor.support.rename ρ) :=
      Profile.rename_hasType_iff.mpr anchor.typed
    have fixedCode := anchor.typeCode.future henv future
    have covered' : ∀ atom ∈ (packed.rename ρ).atoms, atom ∈ (key.rename ρ).input.atoms := by
      intro atom member
      obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map_of_mem (covered old present)
    have invoke {other : Subst}
        (nextFrame : OriginalRichFrame sourceEnv env U registry next context locals (σ.lift_r ρ) other (available.rename ρ))
        (nextEnv : nextFrame.dependencyEnvironment ordered = frame.dependencyEnvironment ordered)
        (nextSubst : Ctx.SubstEq env U next (σ.lift_r ρ) other source) :
        Related env U registry next
          (.app ((VExpr.lam A b).subst (σ.lift_r ρ)) (key.anchor.lift' ρ))
          (.app ((VExpr.lam A b).subst other) z)
          (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
          (.singleton (output.rename ρ)) (anchor.support.rename ρ) := by
      obtain ⟨raw, _, support, inputTyped, supportFormed, inputCode, anchorToZ, pair⟩ := admitted
      change Related env U registry next (key.rename ρ).anchor z (key.rename ρ).domain
        (key.rename ρ).input support at anchorToZ
      have anchorAdmission : Admitted env U registry next (key.rename ρ) (key.anchor.lift' ρ) z :=
        ⟨raw.hasType.1, raw, support, inputTyped, supportFormed, inputCode, anchorToZ.left_diagonal, anchorToZ⟩
      have nextBound : (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
          (nextFrame.dependencyEnvironment ordered)).cost ≤
          (Closure.close ((EndpointState.lam hu hv (.ref domain) codomain body).dependencyOrigin ordered)
            (frame.dependencyEnvironment ordered)).cost := by
        rw [nextEnv]
        exact Nat.le_refl _
      obtain ⟨answer⟩ := nextFrame.lambdaBodyStep henv sourceBelow ordered initialContext domain codomain body hu hv
        location lineage bodyF nextBound (closed.rename ρ) (future.targetWF henv) nextSubst domain'
        (domainAvailable.rename ρ) guard' (by simpa only [subst_cons_future, Profile.rename_singleton, Key.rename] using query')
        (pack.rename ρ) covered' (resources.rename ρ) anchorAdmission
      have bridge : TypeRelated env U registry next
          (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ)))
          (B.subst ((σ.lift_r ρ).cons (key.anchor.lift' ρ))) (anchor.support.rename ρ) := by
        simpa only [lift'_subst, subst_cons_future] using fixedCode
      exact lambda_anchor_beta henv (future.targetWF henv) nextSubst rawDomain rawCodomain rawBody
        (guard'.path.cast raw) (Related.retag henv queryTyped bridge answer.related)
    have left := invoke (frame.leftDiagonal.future henv future)
      (by rw [OriginalRichFrame.dependencyEnvironment_future, OriginalRichFrame.dependencyEnvironment_leftDiagonal])
      (substitutions.left.future henv future)
    have right := invoke (frame.future henv future)
      (by rw [OriginalRichFrame.dependencyEnvironment_future]) (substitutions.future henv future)
    simpa only [lift', lift'_subst, subst_cons_future, inst_lift_cons] using And.intro left right
  have actualDomainF := domainF
  unfold OriginalCodeInductionAt at actualDomainF
  rw [domainLineage] at actualDomainF
  obtain ⟨domainAnswer⟩ := actualDomainF target locals σ τ available frame
    (binder_domain_cost _ _ _ _) closed formed substitutions domainCode domainAvailable
  have domains := rawDomain.substDF henv substitutions.wf formed substitutions
  have newGuard : LambdaGuard env U registry target τ A key ambient :=
    ⟨guard.inputTyped, guard.formed, guard.path.trans (.single domains),
      guard.domains.trans henv domainAnswer.related, guard.anchor⟩
  obtain ⟨bodyAnswer⟩ := frame.lambdaBodyStep henv sourceBelow ordered initialContext domain codomain body hu hv
    location lineage bodyF (Nat.le_refl _) closed formed substitutions domainCode domainAvailable guard
    observation pack covered resources guard.anchor
  obtain ⟨rightQuery⟩ := RichGradedResult.lam henv hscoped formed closed codomain hu hv
    domainAnswer.certificate domainAnswer.resources newGuard needs bounded coverage bodyAnswer.rightQuery
    (Valuation.push_atomized_closed closed _)
  exact ⟨{
    support := _
    footprint := _
    certificate := typeCertificate
    resources := typeResources
    typed := typed
    related := related
    typeCode := typeAnswer.related
    rightQuery := rightQuery }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
