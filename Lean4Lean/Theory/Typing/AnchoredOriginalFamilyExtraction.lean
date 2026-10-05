import Lean4Lean.Theory.Typing.AnchoredFamilyCodeOrigins
import Lean4Lean.Theory.Typing.AnchoredFamilyConsumeObservation
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

/-! Family extraction follows a closed original header and reconstructs the
exact finite source tails at its binders. Header callbacks range only over
locations in that retained original tree, in their computed source contexts.
They do not strengthen the completed earlier theorem to arbitrary Fits.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private normal_fn_parts unnormalize_admission from Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
set_option backward.isDefEq.respectTransparency false

/-- The actual closed header formation, specialized in its original earlier
environment. Its source stage, rather than its potentially growing query,
justifies the declaration-induction call. -/
structure OriginalFamilyHeader (sourceEnv : VEnv) (U : Nat) (expression : VExpr) where
  level : VLevel
  reference : EndpointRef sourceEnv U [] expression (.sort level)

noncomputable def _root_.Lean4Lean.VEnv.ConstantHeaderOrigin.familyHeader
    (origin : ConstantHeaderOrigin env name info)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    OriginalFamilyHeader origin.source U (info.type.instL levels) := by
  let formed := origin.typeInstance levelsWF
  exact ⟨Classical.choose formed,
    .left (Classical.choice (Derivation.reify (Classical.choose_spec formed)))⟩

/-- Every permitted semantic call points into this one original header.
The exact binder context is computed from that location. -/
def OriginalFamilyHeader.Fundamentals
    (header : OriginalFamilyHeader sourceEnv U expression)
    (env : VEnv) (registry : CanonicalHead.Registry) : Prop :=
  ∀ {source selected assigned} {node : EndpointState sourceEnv U source selected assigned}
    (location : Located header.reference node),
    StateFundamental env registry (location.contextDerivation .nil) node

structure OriginalFamilyPrefix
    (header : OriginalFamilyHeader sourceEnv U expression)
    (signature : ConstantTelescope expression) (count : Nat) where
  assigned : VExpr
  node : EndpointState sourceEnv U (signature.domains.take count).reverse
    (wrapForalls (signature.domains.drop count) signature.result) assigned
  location : Located header.reference node

noncomputable def OriginalFamilyPrefix.initial
    (header : OriginalFamilyHeader sourceEnv U expression)
    (signature : ConstantTelescope expression) : OriginalFamilyPrefix header signature 0 := by
  have equal : expression = wrapForalls (signature.domains.drop 0) signature.result := by
    simpa only [List.drop_zero] using signature.type_eq
  exact ⟨_, (EndpointState.ref header.reference).cast equal rfl,
    (Located.here).castExpression equal⟩

/-- A consumed plan retains the exact original header prefix and both fitted
source tails reconstructed while following its actual application binders. -/
structure FamilyPlanConsumption.Original
    (sourceEnv : VEnv)
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested) where
  header : OriginalFamilyHeader sourceEnv U (info.type.instL consumed.seedLevels)
  calls : header.Fundamentals env registry
  cursor : OriginalFamilyPrefix header consumed.signature arguments.length
  fitted : TailPairedFits env registry target (cursor.location.contextDerivation .nil)
    (List.range arguments.length) (nativeCaptureSubst consumed.anchors)
    (nativeCaptureSubst (arguments.map (·.subst σ))) consumed.valuation

noncomputable def FamilyPlanConsumption.Original.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (original : consumed.Original sourceEnv) (N : Nat) (bound : consumed.rank ≤ N) :
    (consumed.raiseTo henv hscoped hTarget N bound).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def FamilyPlanConsumption.Original.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments a}
    (original : consumed.Original sourceEnv)
    (change : AtomView env U registry target a b) :
    (consumed.view henv hscoped hTarget change).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def FamilyPlanConsumption.Original.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (a : Atom n)}
    (original : consumed.Original sourceEnv) :
    (consumed.pad henv hscoped hTarget).Original sourceEnv :=
  ⟨original.header, original.calls, original.cursor, original.fitted⟩

noncomputable def FamilyPlanConsumption.Original.unpad
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
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

theorem FamilyPlanConsumption.appOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {key : Key n} {output : Atom n}
    (result : FamilyPlanConsumption env U registry target locals σ available info name levels arguments
      (n := n + 1) (.fn key output))
    (original : result.Original sourceEnv)
    {argument : VExpr} {input : Profile n} {argumentFootprint : Footprint}
    (observation : Obs env U registry target locals σ argument input argumentFootprint)
    (resources : argumentFootprint.Available available)
    (live : Profile.Live env U registry target input)
    (inputs : NormalProfileAdapter env U registry target input key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ)) :
    ∃ next : FamilyPlanConsumption env U registry target locals σ available info name levels
      (arguments ++ [argument]) output, Nonempty (next.Original sourceEnv) := by
  rcases result with ⟨rank, bound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, atom, footprint, plan, adapter, valuation, closed, raw, fits, planResources, observed⟩
  rcases original with ⟨header, calls, cursor, originalFits⟩
  cases rank with
  | zero => omega
  | succ rank =>
    have hn : n ≤ rank := Nat.le_of_succ_le_succ bound
    obtain ⟨front⟩ := plan.front henv hscoped hTarget atom rfl
    cases front with
    | terminal saturated shape relevant captures terminalBound frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toAdapter henv hscoped hTarget
      exact (familyAdapter_not_fn terminalBound (frontAdapter.comp (adapter.comp expose))).elim
    | @binder r domainFoot bodyFoot outside requested domain oldKey oldOutput support packed
        origin domainCode guard body pack covered frontAdapter =>
      have expose := (functionGradeView (env := env) (U := U) (registry := registry)
        (Γ := target) hn key output).toAdapter henv hscoped hTarget
      have normalized := frontAdapter.comp (adapter.comp expose)
      obtain ⟨⟨keys⟩, ⟨outputs⟩⟩ := normal_fn_parts normalized
      have incoming := AdapterNormal.normalizeAdmission henv hscoped hTarget
        (Admitted.raise henv hn admitted)
      have seed := AdapterNormal.normalizeAdmission henv hscoped hTarget guard.anchor
      have pulled := unnormalize_admission henv hscoped hTarget
        (keys.pull henv hscoped hTarget seed incoming)
      let highInput := raiseProfile rank hn input
      let highObservation := observation.raise hn
      have highInputs : NormalProfileAdapter env U registry target highInput oldKey.input :=
        (NormalProfileAdapter.raise henv hscoped hTarget hn inputs).comp keys.arguments
      let argumentResult : GradedResult env U registry target locals σ available argument oldKey.input := {
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
      let fitted : TailPairedFits env registry target
          (head.view.location.contextDerivation .nil) (List.range arguments.length)
          (nativeCaptureSubst anchors) (nativeCaptureSubst (arguments.map (·.subst σ))) valuation := by
        rw [contextEq]
        exact originalFits
      let domainContext := (Located.piDomain head.view.location).contextDerivation .nil
      let domainFitted : TailPairedFits env registry target domainContext
          (List.range arguments.length) (nativeCaptureSubst anchors)
          (nativeCaptureSubst (arguments.map (·.subst σ))) valuation :=
        ⟨fitted.forward.reorigin domainContext, fitted.backward.reorigin domainContext,
          fitted.forward.reorigin_contextDerivation domainContext,
          fitted.backward.reorigin_contextDerivation domainContext⟩
      have domainRaw : Ctx.SubstEq env U target (nativeCaptureSubst anchors)
          (nativeCaptureSubst (arguments.map (·.subst σ)))
          (signature.domains.take arguments.length).reverse := raw
      have domainChild := calls (.piDomain head.view.location) target
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
      obtain ⟨childFits⟩ := fitted.pushGradedOriginal henv hscoped hTarget domainRef closed
        domainChild.1 domainCode' domainResources guard.inputTyped semanticArgument
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
      let next : FamilyPlanConsumption env U registry target locals σ available info name levels
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
        fits := by
          simpa only [childContext, childLocals, nativeCaptureSubst_append, List.map_append,
            List.map_cons, List.map_nil] using childFits.toPairedFits henv hTarget
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
      have nextFits : TailPairedFits env registry target
          (selected.location.contextDerivation .nil) (List.range (arguments ++ [argument]).length)
          (nativeCaptureSubst (anchors ++ [oldKey.anchor]))
          (nativeCaptureSubst ((arguments ++ [argument]).map (·.subst σ)))
          (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := by
        have sourceFits : TailPairedFits env registry target
            (.cons (head.view.location.contextDerivation .nil) domainRef) (Locals.push (List.range arguments.length))
            ((nativeCaptureSubst anchors).cons oldKey.anchor)
            ((nativeCaptureSubst (arguments.map (·.subst σ))).cons (argument.subst σ))
            (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := childFits
        let desired := selected.location.contextDerivation .nil
        have forward : TailFits sourceEnv env U registry target
            (signature.domains.take (arguments ++ [argument]).length).reverse
            (List.range (arguments ++ [argument]).length)
            (nativeCaptureSubst (anchors ++ [oldKey.anchor]))
            (nativeCaptureSubst ((arguments ++ [argument]).map (·.subst σ)))
            (Valuation.push (bodyFoot.localNeeds ++ bodyFoot.localNeeds.flatMap Need.singletons) valuation) := by
          simpa only [childContext, childLocals, nativeCaptureSubst_append, List.map_append,
            List.map_cons, List.map_nil] using sourceFits.forward
        have backward : TailFits sourceEnv env U registry target
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

/-- Source-only variable observers retain no realization-sensitive term
node. Rebuilding them changes neither target adapters nor their footprint. -/
noncomputable def Obs.realizeVariable
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (τ : Subst) : Obs env U registry target locals τ (.bvar index) demand footprint := by
  match observation with
  | .var .. => exact .var locals τ index demand
  | .empty => exact .empty
  | .union left right => exact .union (left.realizeVariable τ) (right.realizeVariable τ)
  | .view source change => exact .view (source.realizeVariable τ) change
  | .pad source => exact .pad (source.realizeVariable τ)
  | .unpad source => exact .unpad (source.realizeVariable τ)
  | .rowShift source => exact .rowShift (source.realizeVariable τ)
termination_by sizeOf observation

/-- Terminal capture extraction uses its actual finite argument observers.
No variable formation theorem is needed: target anchor equality comes from
the paired declaration substitution and the stored domain alignment. -/
theorem FamilyCaptures.sourceCapturesOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {captureLocals callerLocals : List Nat}
    {seed actual replacement realization : Subst}
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))} {footprint : Footprint}
    {captureAvailable callerAvailable : Valuation}
    (captures : FamilyCaptures env U registry target source captureLocals seed expressions requests footprint)
    (hTarget : OnCtx target (env.IsType U)) (callerClosed : callerAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target seed actual source)
    (resources : footprint.Available captureAvailable)
    (observed : NativeGradedSubstitution env U registry target callerLocals realization callerAvailable
      replacement captureAvailable)
    (agree : ∀ index < source.length, actual index = (replacement index).subst realization) :
    Nonempty (ConstructorSourceCaptures env U registry target source callerLocals realization seed
      replacement callerAvailable expressions requests) := by
  match captures with
  | .nil => exact ⟨.nil⟩
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨supply⟩ := observed.supply (fun i need member =>
      resources i need (List.mem_append_left _ member))
    obtain ⟨reified⟩ := (value.realizeVariable (replacement.comp realization)).substitute
      henv hscoped hTarget replacement realization rfl callerLocals callerAvailable callerClosed supply
    let selected : GradedResult env U registry target callerLocals realization callerAvailable
        (replacement _) _ := {
      rank := reified.rank
      bound := reified.bound
      raw := reified.raw
      footprint := reified.footprint
      observation := reified.observation
      adapter := reified.adapter.comp (adapter.raise henv hscoped hTarget reified.bound)
      resources := reified.resources
      live := reified.live }
    obtain ⟨rest⟩ := tail.sourceCapturesOriginal henv hscoped hTarget callerClosed substitutions
      (fun i need member => resources i need (List.mem_append_right _ member)) observed agree
    refine ⟨.cons ⟨_, lookup, selected, alignment, anchor, ?_⟩ rest⟩
    have pair := alignment.path.symm.cast (substitutions.lookup lookup)
    simpa only [agree _ lookup.lt] using pair
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem Obs.consumeFamilyOriginal
    {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).Fundamentals env registry)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {atom : Atom n} (member : atom ∈ demand.atoms) :
    ∃ consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
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
    let consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
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
      fits := .nil
      resources := fun _ _ hm => nomatch hm
      observed := NativeGradedValuation.empty }
    let header := origin.familyHeader seedWF
    let cursor := OriginalFamilyPrefix.initial header signature
    let context := cursor.location.contextDerivation .nil
    let emptyFits : TailFits origin.source env U registry target [] []
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
    obtain ⟨prior, ⟨original⟩⟩ := fn.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope.1 first (List.mem_singleton_self _)
    cases atomEq
    rw [getAppFnArgs_app]
    exact prior.appOriginal henv hscoped origin.sourceBelow hTarget original
      arg second (arg.live henv hscoped hTarget
        (fits.leavesLive henv hscoped hTarget second (arg.scoped scope.2))) inputs admitted
  | _, _, _, _, .union left right =>
    have first : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_left _ hm)
    have second : Footprint.Available _ available := fun i need hm => resources i need (List.mem_append_right _ hm)
    rcases List.mem_append.mp member with hm | hm
    · exact left.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope first hm
    · exact right.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
        hTarget fits head scope second hm
  | _, _, _, _, .view original change =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.view henv hscoped hTarget change, ⟨original.view henv hscoped hTarget change⟩⟩
  | _, _, _, _, .pad original =>
    obtain ⟨a, hm, rfl⟩ := List.mem_map.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources hm
    exact ⟨prior.pad henv hscoped hTarget, ⟨original.pad henv hscoped hTarget⟩⟩
  | _, _, _, _, .unpad original =>
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_map_of_mem member)
    exact ⟨prior.unpad, ⟨original.unpad⟩⟩
  | _, _, _, _, .rowShift original =>
    cases List.mem_singleton.mp member
    obtain ⟨prior, ⟨original⟩⟩ := original.consumeFamilyOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget fits head scope resources (List.mem_singleton_self _)
    exact ⟨prior.rowShift henv hscoped hTarget,
      ⟨(original.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; subst_eqs; simp_wf; omega

theorem FamilyPlanConsumption.sourceCapturesOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested)
    (full : arguments.length = consumed.signature.domains.length)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed) :
    Nonempty (FamilyConsumedCaptures consumed) := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, output, footprint, plan, resultAdapter, valuation, valuationClosed,
    originalRaw, originalFits, originalResources, originalObserved⟩
  change arguments.length = signature.domains.length at full
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  have resources := originalResources
  cases front with
  | terminal saturated shape relevant captures bound adapter =>
    have raw := originalRaw
    have fits := originalFits
    rw [full, List.take_length] at raw fits
    rw [← saturated] at fits
    have observed := originalObserved.substitution
    obtain ⟨actual⟩ := captures.sourceCapturesOriginal henv hscoped hTarget
      closed raw resources observed (by
        intro index within
        have bound : index < arguments.length := by simpa only [List.length_reverse, ← full] using within
        simp only [nativeCaptureSubst, List.length_map, dif_pos bound, List.getElem_map])
    exact ⟨{
      rank := _
      level := _
      relevant := _
      resultSort := shape
      relevance := relevant
      requests := _
      bound := bound
      adapter := adapter.comp resultAdapter
      footprint := _
      captures := captures
      resources := resources
      sourceCaptures := actual }⟩
  | binder origin =>
    have bound := (List.getElem?_eq_some_iff.mp origin).1
    have equal := length.trans full
    omega


open private familyObservations_pad FamilyProfileOrigins.pad FamilyProfileOrigins.down
  FamilyProfileOrigins.map FamilyProfileOrigins.refine
  from Lean4Lean.Theory.Typing.AnchoredFamilyCodeOrigins

variable {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headers : ∀ {seedLevels : List VLevel} (wf : ∀ level ∈ seedLevels, level.WF U),
      (origin.familyHeader wf).Fundamentals env registry)
    {domains : List VExpr} {level : VLevel}
    (shape : info.type = wrapForalls domains (.sort level))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {levels : List VLevel}
    (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)

include henv hscoped hTarget closed in
private theorem FamilyPlanConsumption.originsOriginal
    {arguments : List VExpr} {atom : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments atom) :
    FamilyAtomOrigins env U registry target locals σ available arguments atom := by
  match n, atom with
  | _ + 1, .family family =>
    obtain ⟨packet⟩ := consumed.sourceCapturesOriginal henv hscoped
      (consumed.saturated henv hscoped hTarget) hTarget closed
    exact packet.requestObservations
  | _ + 1, .pad atom => exact consumed.unpad.originsOriginal
  | 0, atom => trivial
  | _ + 1, .sort _ | _ + 1, .fn _ _ | _ + 1, .pi _ _ _ _ |
      _ + 1, .ctor _ | _ + 1, .record _ => trivial
termination_by n

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
theorem Obs.familyOriginsOriginal
    (observation : Obs env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileOrigins env U registry target locals σ available expression.getAppFnArgs.2 profile := by
  intro atom member
  obtain ⟨consumed, _⟩ := observation.consumeFamilyOriginal origin henv hscoped headers
    shape notDefinition notNative hTarget fits head scope resources member
  exact consumed.originsOriginal henv hscoped hTarget closed

include origin henv hscoped headers shape notDefinition notNative hTarget closed fits head scope in
/-- Every actual source family certificate supplies observers of its exact
parameter requests, including requests created by family-specific padding. -/
theorem CodeCert.familyOriginsOriginal
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) :
    FamilyProfileOrigins env U registry target locals σ available expression.getAppFnArgs.2 profile := by
  match certificate with
  | .seed observation _ =>
    exact observation.familyOriginsOriginal origin henv hscoped headers shape notDefinition notNative
      hTarget closed fits head scope resources
  | .union left right =>
    intro atom member
    rcases List.mem_append.mp member with member | member
    · exact left.familyOriginsOriginal (fun i need hm => resources i need (List.mem_append_left _ hm)) atom member
    · exact right.familyOriginsOriginal (fun i need hm => resources i need (List.mem_append_right _ hm)) atom member
  | .pad source =>
    exact FamilyProfileOrigins.pad (source.familyOriginsOriginal resources)
  | .familyPad source =>
    intro atom member
    cases List.mem_singleton.mp member
    have original := source.familyOriginsOriginal resources _ (List.mem_singleton_self _)
    exact familyObservations_pad henv hscoped hTarget original
  | .unpad source =>
    intro atom member
    exact source.familyOriginsOriginal resources (.pad atom) (List.mem_map.mpr ⟨atom, member, rfl⟩)
  | .down source =>
    exact FamilyProfileOrigins.down (source.familyOriginsOriginal resources)
  | .map change source =>
    exact FamilyProfileOrigins.map change (source.familyOriginsOriginal resources)
  | .focusMinimal source _ bound =>
    exact FamilyProfileOrigins.refine bound (source.familyOriginsOriginal resources)
  | .select source member =>
    intro atom hm
    cases List.mem_singleton.mp hm
    exact source.familyOriginsOriginal resources _ member
termination_by sizeOf certificate

end Lean4Lean.AnchoredSource.Adapted
