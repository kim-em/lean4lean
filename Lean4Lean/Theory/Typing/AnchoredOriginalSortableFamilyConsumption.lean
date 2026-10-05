import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterFamilyOrigins
import Lean4Lean.Theory.Typing.AnchoredAtomActionGeneralAdapter
import Lean4Lean.Theory.Typing.AnchoredAtomActionGrades
import Lean4Lean.Theory.Typing.AnchoredSortableFamilyPlan
import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredSortableInstantiation
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyRequests

/-! Family applications retain hereditary argument queries while replaying
only the original declaration's finite domain occurrences. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
set_option backward.isDefEq.respectTransparency false

/-- Finite valuation entries are backed by genuine source argument results. -/
def SortableGradedValuation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (arguments : List VExpr) (prior : Valuation) : Prop :=
  ∀ index need, need ∈ prior index → ∃ bound : index < arguments.length,
    Nonempty (SortableGradedResult env U registry target locals σ available
      arguments[arguments.length - 1 - index] need.profile)

theorem SortableGradedValuation.empty :
    SortableGradedValuation env U registry target locals σ available [] (fun _ => []) := by
  intro _ _ h
  cases h

theorem SortableGradedValuation.push
    (observed : SortableGradedValuation env U registry target locals σ available arguments prior)
    (argument : SortableGradedResult env U registry target locals σ available expression (input : Profile n))
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    SortableGradedValuation env U registry target locals σ available (arguments ++ [expression])
      (Valuation.push needs prior) := by
  intro index need member
  cases index with
  | zero =>
    refine ⟨by simp, ⟨?_⟩⟩
    simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel, Nat.sub_zero,
      List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] using
      argument.localDemand need (bounded need member) (covered need member)
  | succ index =>
    obtain ⟨bound, ⟨value⟩⟩ := observed index need member
    have position : (arguments ++ [expression]).length - 1 - (index + 1) =
        arguments.length - 1 - index := by simp only [List.length_append, List.length_singleton]; omega
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ⟨?_⟩⟩
    have same : (arguments ++ [expression])[(arguments ++ [expression]).length - 1 - (index + 1)] =
        arguments[arguments.length - 1 - index] := by
      simp only [position]
      exact List.getElem_append_left (by omega)
    exact same.symm ▸ value

/-- All hereditary header calls select concrete occurrences in the actual
closed earlier header, with the source context computed by that location. -/
def OriginalFamilyHeader.SortableFundamentals
    (header : OriginalFamilyHeader sourceEnv U expression)
    (env : VEnv) (registry : CanonicalHead.Registry) : Prop :=
  ∀ {source selected assigned} {node : EndpointState sourceEnv U source selected assigned}
    (location : Located header.reference node),
    StateSortableFundamental env registry (location.contextDerivation .nil) node

theorem OriginalTail.SortableTailPairedFits.pushSortableOriginal
    (henv : env.Ordered)
    {context : ContextDerivation sourceEnv U source}
    {input support : Profile N}
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (domainChild : SortableTransfer env U registry target locals σ τ available A A (.sort level))
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (domain : SortableCert env U registry target locals σ A true support footprint)
    (resources : footprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ N)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Nonempty (SortableTailPairedFits env registry target (.cons context originalDomain)
      (Locals.push locals) (σ.cons x) (τ.cons y) (Valuation.push needs available)) := by
  obtain ⟨rightDomain⟩ := domainChild domain resources
  exact ⟨fits.pushCertificates originalDomain domain rightDomain.certificate
    resources rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv)) needs bounded covered⟩

structure SortableFamilyPlanConsumption (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (info : VConstant) (name : Name) (levels : List VLevel) (arguments : List VExpr)
    (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  seedLevels : List VLevel
  seedWF : ∀ level ∈ seedLevels, level.WF U
  seedLength : seedLevels.length = info.uvars
  equivalent : List.Forall₂ (· ≈ ·) seedLevels levels
  signature : ConstantTelescope (info.type.instL seedLevels)
  typeClosed : info.type.Closed
  anchors : List VExpr
  length : anchors.length = arguments.length
  output : Atom rank
  footprint : Footprint
  plan : SortableFamilyPlan env U registry target name seedLevels signature anchors (.singleton output) footprint
  adapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom rank bound requested)
  valuation : Valuation
  closed : valuation.AtomClosed
  raw : Ctx.SubstEq env U target (nativeCaptureSubst anchors)
    (nativeCaptureSubst (arguments.map (·.subst σ))) (signature.domains.take arguments.length).reverse
  resources : footprint.Available valuation
  observed : SortableGradedValuation env U registry target locals σ available arguments valuation

private theorem raiseAtom_twice {n k N : Nat} (hn : n ≤ k) (hk : k ≤ N) (a : Atom n) :
    raiseAtom N hk (raiseAtom k hn a) = raiseAtom N (Nat.le_trans hn hk) a := by
  have h := raiseProfile_trans hn hk (.singleton a)
  rw [raiseProfile_singleton, raiseProfile_singleton, raiseProfile_singleton] at h
  exact List.singleton_inj.mp (congrArg Profile.atoms h)

noncomputable def SortableFamilyPlanConsumption.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments requested)
    (N : Nat) (bound : result.rank ≤ N) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments requested := by
  refine { result with
    rank := N
    bound := Nat.le_trans result.bound bound
    output := raiseAtom N bound result.output
    plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
    adapter := ?_ }
  simpa only [raiseAtom_twice] using result.adapter.raise henv hscoped hTarget bound

noncomputable def SortableFamilyPlanConsumption.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments a)
    (change : AtomView env U registry target a b) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments b :=
  { result with adapter := result.adapter.comp ((change.toGeneralAdapter henv hscoped hTarget).raise
      henv hscoped hTarget result.bound) }

noncomputable def SortableFamilyPlanConsumption.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments a)
    (change : AtomAction env U registry target a b) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments b :=
  { result with adapter := result.adapter.comp ((change.raise result.bound).toGeneralAdapter henv hscoped hTarget) }

noncomputable def SortableFamilyPlanConsumption.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments (a : Atom n)) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments (n := n + 1) (AtomData.pad a) := by
  let raised := result.raiseTo henv hscoped hTarget (result.rank + 1) (Nat.le_succ _)
  have bound : n + 1 ≤ raised.rank := Nat.succ_le_succ result.bound
  exact { raised with
    bound := bound
    adapter := by simpa only [raiseAtom_pad] using raised.adapter }

noncomputable def SortableFamilyPlanConsumption.unpad
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments (n := n + 1) (AtomData.pad (a : Atom n))) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments a :=
  { result with
    bound := Nat.le_trans (Nat.le_succ _) result.bound
    adapter := by simpa only [raiseAtom_pad] using result.adapter }

/-- A consumed plan retains the exact original header prefix and both fitted
source tails reconstructed while following its actual application binders. -/
structure SortableFamilyPlanConsumption.Original
    (sourceEnv : VEnv)
    (consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested) where
  header : OriginalFamilyHeader sourceEnv U (info.type.instL consumed.seedLevels)
  calls : header.SortableFundamentals env registry
  cursor : OriginalFamilyPrefix header consumed.signature arguments.length
  fitted : SortableTailPairedFits env registry target (cursor.location.contextDerivation .nil)
    (List.range arguments.length) (nativeCaptureSubst consumed.anchors)
    (nativeCaptureSubst (arguments.map (·.subst σ))) consumed.valuation

noncomputable def SortableFamilyPlanConsumption.Original.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (original : consumed.Original sourceEnv) (N : Nat) (bound : consumed.rank ≤ N) :
    (consumed.raiseTo henv hscoped hTarget N bound).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def SortableFamilyPlanConsumption.Original.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments a}
    (original : consumed.Original sourceEnv)
    (change : AtomView env U registry target a b) :
    (consumed.view henv hscoped hTarget change).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def SortableFamilyPlanConsumption.Original.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments a}
    (original : consumed.Original sourceEnv)
    (change : AtomAction env U registry target a b) :
    (consumed.action henv hscoped hTarget change).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def SortableFamilyPlanConsumption.Original.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (a : Atom n)}
    (original : consumed.Original sourceEnv) :
    (consumed.pad henv hscoped hTarget).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def SortableFamilyPlanConsumption.Original.unpad
    {consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.pad a)}
    (original : consumed.Original sourceEnv) : consumed.unpad.Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

private def castSource (same : source = source')
    (node : EndpointState sourceEnv U source expression assigned) :
    EndpointState sourceEnv U source' expression assigned := same ▸ node

private def locatedCastSource (same : source = source')
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) : Located root (castSource same node) := by
  cases same
  exact location

theorem SortableFamilyPlanConsumption.appOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {key : Key n} {output : Atom n}
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 1) (.fn key output))
    (original : result.Original sourceEnv)
    {argument : VExpr} {input : Profile n} {argumentFootprint : Footprint}
    (observation : SortableObs env U registry target locals σ argument input argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : GeneralNormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ)) :
    ∃ next : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      (arguments ++ [argument]) output, Nonempty (next.Original sourceEnv) := by
  rcases result with ⟨rank, bound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, atom, footprint, plan, adapter, valuation, closed, raw, planResources, observed⟩
  rcases original with ⟨header, calls, cursor, originalFits⟩
  cases rank with
  | zero => omega
  | succ rank =>
    have hn : n ≤ rank := Nat.le_of_succ_le_succ bound
    obtain ⟨front⟩ := plan.front henv hscoped hTarget atom rfl
    cases front with
    | terminal saturated shape relevant captures terminalBound frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toGeneralAdapter henv hscoped hTarget
      exact (GeneralNormalAtomAdapter.family_not_fn terminalBound (frontAdapter.toGeneral.comp (adapter.comp expose))).elim
    | @binder r domainFoot bodyFoot outside requested domain oldKey oldOutput support packed
        origin domainCode guard body pack covered frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toGeneralAdapter henv hscoped hTarget
      have normalized := frontAdapter.toGeneral.comp (adapter.comp expose)
      obtain ⟨actualKey, actualOutput, equal, ⟨keys⟩, ⟨outputs⟩⟩ := normalized.fn_inv
      obtain ⟨rfl, rfl⟩ := AtomData.fn.inj equal
      have incoming := AdapterNormal.normalizeAdmission henv hscoped hTarget
        (Admitted.raise henv hn admitted)
      have seed := AdapterNormal.normalizeAdmission henv hscoped hTarget guard.anchor
      have pulled := unnormalize_admission henv hscoped hTarget
        (keys.pull henv hscoped hTarget seed incoming)
      let highInput := raiseProfile rank hn input
      let highObservation := observation.raise hn
      have highInputs : GeneralNormalProfileAdapter env U registry target highInput oldKey.input :=
        (GeneralNormalProfileAdapter.raise henv hscoped hTarget hn inputs).comp keys.arguments
      let argumentResult : SortableGradedResult env U registry target locals σ available argument oldKey.input := {
        rank := rank
        bound := Nat.le_refl rank
        raw := highInput
        footprint := argumentFootprint
        observation := highObservation
        adapter := by simpa only [raiseProfile_self] using highInputs
        resources := resources
        live := (raiseProfile_live_iff hn input).mpr live }
      have domainAt : signature.domains[arguments.length]? = some domain := by
        simpa only [length] using origin
      have literal := signature.prefixResidual_cons domainAt
      let current := cursor.location.castExpression literal
      let head := OriginalEndpointFactor.piPrefix current
      let domainRef := Classical.choose head.view.location.originalDomains.1
      have domainEq : head.view.domain = .ref domainRef :=
        Classical.choose_spec head.view.location.originalDomains.1
      have contextEq : head.view.location.contextDerivation .nil =
          cursor.location.contextDerivation .nil := by
        rw [← head.location_eq, PrefixRoute.locate_contextDerivation,
          Located.castExpression_contextDerivation]
      let fitted : SortableTailPairedFits env registry target
          (head.view.location.contextDerivation .nil) (List.range arguments.length)
          (nativeCaptureSubst anchors) (nativeCaptureSubst (arguments.map (·.subst σ))) valuation := by
        rw [contextEq]
        exact originalFits
      let domainContext := (Located.piDomain head.view.location).contextDerivation .nil
      let domainFitted : SortableTailPairedFits env registry target domainContext
          (List.range arguments.length) (nativeCaptureSubst anchors)
          (nativeCaptureSubst (arguments.map (·.subst σ))) valuation :=
        ⟨fitted.forward.reorigin domainContext, fitted.backward.reorigin domainContext,
          fitted.forward.reorigin_contextDerivation domainContext,
          fitted.backward.reorigin_contextDerivation domainContext⟩
      have domainRaw : Ctx.SubstEq env U target (nativeCaptureSubst anchors)
          (nativeCaptureSubst (arguments.map (·.subst σ)))
          (signature.domains.take arguments.length).reverse := raw
      have domainChild : SortableTransfer env U registry target (List.range arguments.length)
          (nativeCaptureSubst anchors) (nativeCaptureSubst (arguments.map (·.subst σ)))
          valuation domain domain (.sort head.view.domainLevel) :=
        calls (.piDomain head.view.location) target
        (List.range arguments.length) (nativeCaptureSubst anchors)
        (nativeCaptureSubst (arguments.map (·.subst σ))) valuation closed hTarget domainRaw domainFitted
      have domainCode' := domainCode
      rw [length] at domainCode'
      have domainResources : domainFoot.Available valuation :=
        fun i need hm => planResources i need (List.mem_append_left _ hm)
      have outsideResources : outside.Available valuation :=
        fun i need hm => planResources i need (List.mem_append_right _ hm)
      obtain ⟨rawArgument, _, oldSupport, _, _, _, anchorPair, _⟩ := pulled
      have semanticArgument := Related.convert henv guard.inputTyped guard.domains anchorPair
      have rawPair := guard.path.cast rawArgument
      have childRaw : Ctx.SubstEq env U target
          ((nativeCaptureSubst anchors).cons oldKey.anchor)
          ((nativeCaptureSubst (arguments.map (·.subst σ))).cons (argument.subst σ))
          (domain :: (signature.domains.take arguments.length).reverse) :=
        .cons domainRaw (head.view.domain.sound.defeq.mono hle) rawPair
      obtain ⟨childFits⟩ := fitted.pushSortableOriginal henv domainRef
        domainChild domainCode' domainResources guard.inputTyped semanticArgument
        (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons)
        (fun need hm => (pack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
      have childResources := pack.available_atomized_localNeeds outsideResources
      have childContext : (signature.domains.take (arguments ++ [argument]).length).reverse =
          domain :: (signature.domains.take arguments.length).reverse := by
        simpa only [List.length_append, List.length_singleton, length] using
          signature.prefixContext_cons origin
      have childLocals : List.range (arguments ++ [argument]).length =
          Locals.push (List.range arguments.length) := by
        simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
      let next : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
          (arguments ++ [argument]) output := {
        rank := rank
        bound := hn
        seedLevels := seedLevels
        seedWF := seedWF
        seedLength := seedLength
        equivalent := equivalent
        signature := signature
        typeClosed := typeClosed
        anchors := anchors ++ [oldKey.anchor]
        length := by simp only [List.length_append, List.length_singleton, length]
        output := oldOutput
        footprint := bodyFoot
        plan := body
        adapter := outputs
        valuation := Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation
        closed := Valuation.push_atomized_closed closed _
        raw := by
          simpa only [childContext, nativeCaptureSubst_append, List.map_append, List.map_cons,
            List.map_nil] using childRaw
        resources := childResources
        observed := observed.push argumentResult
          (fun need hm => (pack.atomized_localNeeds need hm).1)
          (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha)) }
      have nextCursor : Nonempty (OriginalFamilyPrefix header signature (arguments ++ [argument]).length) := by
        have step : wrapForalls (signature.domains.drop (arguments ++ [argument]).length) signature.result =
            wrapForalls (signature.domains.drop (arguments.length + 1)) signature.result := by simp
        exact ⟨⟨_, castSource childContext.symm (head.view.body.cast step.symm rfl),
          locatedCastSource childContext.symm
            ((Located.piBody head.view.location).castExpression step.symm)⟩⟩
      let selected := Classical.choice nextCursor
      have nextFits : SortableTailPairedFits env registry target
          (selected.location.contextDerivation .nil) (List.range (arguments ++ [argument]).length)
          (nativeCaptureSubst (anchors ++ [oldKey.anchor]))
          (nativeCaptureSubst ((arguments ++ [argument]).map (·.subst σ)))
          (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := by
        have sourceFits : SortableTailPairedFits env registry target
            (.cons (head.view.location.contextDerivation .nil) domainRef) (Locals.push (List.range arguments.length))
            ((nativeCaptureSubst anchors).cons oldKey.anchor)
            ((nativeCaptureSubst (arguments.map (·.subst σ))).cons (argument.subst σ))
            (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := childFits
        let desired := selected.location.contextDerivation .nil
        have forward : SortableTailFits sourceEnv env U registry target
            (signature.domains.take (arguments ++ [argument]).length).reverse
            (List.range (arguments ++ [argument]).length)
            (nativeCaptureSubst (anchors ++ [oldKey.anchor]))
            (nativeCaptureSubst ((arguments ++ [argument]).map (·.subst σ)))
            (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := by
          simpa only [childContext, childLocals, nativeCaptureSubst_append, List.map_append,
            List.map_cons, List.map_nil] using sourceFits.forward
        have backward : SortableTailFits sourceEnv env U registry target
            (signature.domains.take (arguments ++ [argument]).length).reverse
            (List.range (arguments ++ [argument]).length)
            (nativeCaptureSubst ((arguments ++ [argument]).map (·.subst σ)))
            (nativeCaptureSubst (anchors ++ [oldKey.anchor]))
            (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := by
          simpa only [childContext, childLocals, nativeCaptureSubst_append, List.map_append,
            List.map_cons, List.map_nil] using sourceFits.backward
        exact ⟨forward.reorigin desired, backward.reorigin desired,
          forward.reorigin_contextDerivation desired, backward.reorigin_contextDerivation desired⟩
      exact ⟨next, ⟨⟨header, calls, selected, nextFits⟩⟩⟩


noncomputable def SortableFamilyPlanConsumption.rowShift
    {n : Nat} {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (result : SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 1) (.fn key output)) :
    SortableFamilyPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 2) (.fn key.pad (.pad output)) :=
  (result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn key output)

theorem Obs.consumeFamilySortable
    {callerEnv env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).SortableFundamentals env registry)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : SortableTailFits callerEnv env U registry target source locals σ σ available)
    {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {atom : Atom n} (member : atom ∈ demand.atoms) :
    ∃ consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      expression.getAppFnArgs.2 atom, Nonempty (consumed.Original origin.source) := by
  match n, atom, demand, expression, observation with
  | _, _, _, _, .delta found nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, _⟩ := VExpr.const.inj head
    rw [sameName, notDefinition] at found
    cases found
  | _, _, _, _, .native found noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, _⟩ := VExpr.const.inj head
    rw [sameName, notNative] at found
    cases found
  | _, _, _, _, .constructor found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    exact (tree.not_familyHeader shape).elim
  | _, _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    cases packet
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree
    let consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
        [] _ := {
      rank := _
      bound := Nat.le_refl _
      seedLevels := _
      seedWF := seedWF
      seedLength := seedLength
      equivalent := equivalent
      signature := signature
      typeClosed := typeClosed
      anchors := []
      length := rfl
      output := _
      footprint := []
      plan := tree.toSortable
      adapter := by rw [raiseAtom_self]; exact .refl _
      valuation := fun _ => []
      closed := fun _ _ hm => nomatch hm
      raw := .nil
      resources := fun _ _ hm => nomatch hm
      observed := SortableGradedValuation.empty }
    let header := origin.familyHeader seedWF
    let cursor := OriginalFamilyPrefix.initial header signature
    let context := cursor.location.contextDerivation .nil
    let emptyFits : SortableTailFits origin.source env U registry target [] []
        (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) := .nil
    exact ⟨consumed, ⟨⟨header, headers seedWF, cursor,
      ⟨emptyFits.reorigin context, emptyFits.reorigin context,
        emptyFits.reorigin_contextDerivation context, emptyFits.reorigin_contextDerivation context⟩⟩⟩⟩
  | _, _, _, _, .var .. => simp only [getAppFnArgs_bvar] at head; cases head
  | _, _, _, _, .empty => cases member
  | _, _, _, _, .sort .. => simp only [getAppFnArgs_sort] at head; cases head
  | _, _, _, _, .lam .. => simp only [getAppFnArgs_lam] at head; cases head
  | _, _, _, _, .pi .. => simp only [getAppFnArgs_forallE] at head; cases head
  | _, _, _, _, .app fn arg inputs admitted =>
    have atomEq := List.mem_singleton.mp member
    simp only [getAppFnArgs_app] at head ⊢
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨prior, ⟨original⟩⟩ := fn.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope.1 first (List.mem_singleton_self _)
    cases atomEq
    rw [getAppFnArgs_app]
    exact prior.appOriginal henv hscoped origin.sourceBelow hTarget original
      (.legacy arg) second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs.toGeneral admitted
  | _, _, _, _, .union left right =>
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    rcases List.mem_append.mp member with hm | hm
    · exact left.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope first hm
    · exact right.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope second hm
  | _, _, _, _, .view original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.view henv hscoped hTarget change, ⟨original.view henv hscoped hTarget change⟩⟩
  | _, _, _, _, .pad original =>
    obtain ⟨a, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources hm
    exact ⟨prior.pad henv hscoped hTarget, ⟨original.pad henv hscoped hTarget⟩⟩
  | _, _, _, _, .unpad original =>
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_map_of_mem member)
    exact ⟨prior.unpad, ⟨original.unpad⟩⟩
  | _, _, _, _, .rowShift original =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.rowShift henv hscoped hTarget,
      ⟨(original.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

/-- Only function demands, possibly under outer padding, need a suspended
family telescope. Formation-certificate observers cannot introduce this shape. -/
def FamilyFunctionDemand : {n : Nat} → Atom n → Prop
  | _ + 1, .fn _ _ => True
  | _ + 1, .pad atom => FamilyFunctionDemand atom
  | _, _ => False

private theorem FamilyFunctionDemand.not_sort
    {atom : Atom n} (function : FamilyFunctionDemand atom)
    (formed : (Profile.singleton atom).HasType (.sort relevant)) : False := by
  induction n with
  | zero => exact function
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | record => exact function
    | fn key output =>
      obtain ⟨other, hm, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp hm
      contradiction
    | pad atom =>
      have padded : (Profile.singleton atom).pad.HasType (.sort relevant) := by
        simpa only [Profile.pad_singleton] using formed
      exact ih function (by simpa only [Profile.down_sort] using padded.pad_inv)

private theorem FamilyFunctionDemand.view
    {a b : Atom n} (change : AtomView env U registry target a b)
    (function : FamilyFunctionDemand b) : FamilyFunctionDemand a := by
  match n, a, b, change with
  | _, _, _, .refl _ => exact function
  | _ + 1, _, _, .reanchor _ => trivial
  | _ + 1, _, _, .domainRekey _ _ _ _ => trivial
  | _ + 1, _, _, .input _ _ => trivial
  | _ + 2, _, _, .commutePadFn _ _ => trivial
  | _ + 2, _, _, .uncommutePadFn _ _ => trivial
  | _ + 1, _, _, .fn _ _ => trivial
  | k + 1, _, _, .pad child => exact FamilyFunctionDemand.view (n := k) child function
  | _, _, _, .trans first second => exact (function.view second).view first
termination_by sizeOf change
decreasing_by all_goals simp_wf; omega

private theorem FamilyFunctionDemand.action
    {a b : Atom n} (change : AtomAction env U registry target a b)
    (function : FamilyFunctionDemand b) : FamilyFunctionDemand a := by
  induction change with
  | view view => exact function.view view
  | code action formed => exact (function.not_sort (action.preservesSort formed)).elim
  | fn => trivial
  | pad child ih => exact ih function
  | comp first second firstIH secondIH => exact firstIH (secondIH function)

theorem SortableObs.consumeFamilyFunction
    {callerEnv env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).SortableFundamentals env registry)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : SortableTailFits callerEnv env U registry target source locals σ σ available)
    {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry target locals σ expression demand footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {atom : Atom n} (member : atom ∈ demand.atoms)
    (function : FamilyFunctionDemand atom) :
    ∃ consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
      expression.getAppFnArgs.2 atom, Nonempty (consumed.Original origin.source) := by
  match n, atom, demand, expression, observation with
  | _, _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [getAppFnArgs_const] at head
    obtain ⟨sameName, packet⟩ := VExpr.const.inj head
    cases sameName
    rw [origin.constant] at found
    cases Option.some.inj found
    cases packet
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree
    let consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels
        [] _ := {
      rank := _
      bound := Nat.le_refl _
      seedLevels := _
      seedWF := seedWF
      seedLength := seedLength
      equivalent := equivalent
      signature := signature
      typeClosed := typeClosed
      anchors := []
      length := rfl
      output := _
      footprint := []
      plan := tree
      adapter := by rw [raiseAtom_self]; exact .refl _
      valuation := fun _ => []
      closed := fun _ _ hm => nomatch hm
      raw := .nil
      resources := fun _ _ hm => nomatch hm
      observed := SortableGradedValuation.empty }
    let header := origin.familyHeader seedWF
    let cursor := OriginalFamilyPrefix.initial header signature
    let context := cursor.location.contextDerivation .nil
    let emptyFits : SortableTailFits origin.source env U registry target [] []
        (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) := .nil
    exact ⟨consumed, ⟨⟨header, headers seedWF, cursor,
      ⟨emptyFits.reorigin context, emptyFits.reorigin context,
        emptyFits.reorigin_contextDerivation context, emptyFits.reorigin_contextDerivation context⟩⟩⟩⟩
  | _, _, _, _, .legacy observation =>
    exact observation.consumeFamilySortable origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources member
  | _, _, _, _, .code relevant certificate =>
    exact (function.not_sort (certificate.formed.singleton_of_mem member)).elim
  | _, _, _, _, .lam .. => simp only [getAppFnArgs_lam] at head; cases head
  | _, _, _, _, .app fn arg inputs admitted =>
    have atomEq := List.mem_singleton.mp member
    simp only [getAppFnArgs_app] at head ⊢
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    obtain ⟨prior, ⟨original⟩⟩ := fn.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope.1 first (List.mem_singleton_self _) True.intro
    cases atomEq
    rw [getAppFnArgs_app]
    exact prior.appOriginal henv hscoped origin.sourceBelow hTarget original
      arg second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs admitted
  | _, _, _, _, .union left right =>
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    rcases List.mem_append.mp member with hm | hm
    · exact left.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope first hm function
    · exact right.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope second hm function
  | _, _, _, _, .view original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _) (function.view change)
    exact ⟨prior.view henv hscoped hTarget change, ⟨original.view henv hscoped hTarget change⟩⟩
  | _, _, _, _, .action original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _) (function.action change)
    exact ⟨prior.action henv hscoped hTarget change, ⟨original.action henv hscoped hTarget change⟩⟩
  | _, _, _, _, .pad original =>
    obtain ⟨a, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources hm function
    exact ⟨prior.pad henv hscoped hTarget, ⟨original.pad henv hscoped hTarget⟩⟩
  | _, _, _, _, .unpad original =>
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_map_of_mem member) function
    exact ⟨prior.unpad, ⟨original.unpad⟩⟩
  | _, _, _, _, .rowShift original =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyFunction origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _) True.intro
    exact ⟨prior.rowShift henv hscoped hTarget,
      ⟨(original.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

theorem SortableFamilyPlan.initialConsumption
    {env : VEnv} {info : VConstant} {name : Name} {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).SortableFundamentals env registry)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {seedLevels levels : List VLevel}
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = info.uvars)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels)) (typeClosed : info.type.Closed)
    {n : Nat} {demand : Profile n}
    (tree : SortableFamilyPlan env U registry target name seedLevels signature [] demand [])
    {atom : Atom n} (member : atom ∈ demand.atoms) :
    ∃ consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels [] atom,
      Nonempty (consumed.Original origin.source) := by
  have singleton := tree.singleton_of_mem member
  rw [singleton] at tree
  let consumed : SortableFamilyPlanConsumption env U registry target locals σ available info name levels [] atom := {
    rank := n, bound := Nat.le_refl _, seedLevels := seedLevels, seedWF := seedWF,
    seedLength := seedLength, equivalent := equivalent, signature := signature,
    typeClosed := typeClosed, anchors := [], length := rfl, output := atom, footprint := [],
    plan := tree, adapter := (by rw [raiseAtom_self]; exact .refl _),
    valuation := fun _ => []
    closed := fun _ _ hm => nomatch hm
    raw := .nil
    resources := fun _ _ hm => nomatch hm
    observed := SortableGradedValuation.empty }
  let header := origin.familyHeader seedWF
  let cursor := OriginalFamilyPrefix.initial header signature
  let context := cursor.location.contextDerivation .nil
  let emptyFits : SortableTailFits origin.source env U registry target [] []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) := .nil
  exact ⟨consumed, ⟨⟨header, headers seedWF, cursor,
    ⟨emptyFits.reorigin context, emptyFits.reorigin context,
      emptyFits.reorigin_contextDerivation context, emptyFits.reorigin_contextDerivation context⟩⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted
