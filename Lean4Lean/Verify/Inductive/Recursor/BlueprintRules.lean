import Lean4Lean.Verify.Inductive.Recursor.SecondPass

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The retained-blueprint rule builder is a transparent read of the current
local context followed by a pure map.  This is the executable boundary used
by the installation proof; in particular it performs no inference, WHNF, or
fresh-name allocation. -/
theorem AddInductive.mkRecRulesFromBlueprints.WF
    (indTypes : Array InductiveType) (elimLevel : Level)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (dIdx : Nat)
    (motives minors : Array Expr) (c : AddInductive.Context) :
    (AddInductive.mkRecRulesFromBlueprints indTypes elimLevel stats recInfos
      dIdx motives minors c).WF fun rules =>
        rules = recInfos[dIdx]!.ruleBlueprints.toList.map fun blueprint =>
          blueprint.build indTypes stats motives minors
            (AddInductive.getRecLevels elimLevel stats.levels) c.lctx := by
  simp only [AddInductive.mkRecRulesFromBlueprints, getLCtx, readThe, read]
  exact Except.WF.pure rfl

/-- Instantiate the producer-retained semantic call row with the completed
minor array and the exact recursor levels.  No call generation, inference,
or constructor traversal is replayed here. -/
theorem RecInfoHypothesisCallSemanticOrigins.retainedGeneratedCalls
    {recLparams : List Name}
    {Rfield : RecursorContextWF fieldRoot recLparams}
    (H : RecInfoHypothesisCallSemanticOrigins Rfield decl depth stats
      motives rootScope fields hypotheses calls)
    (hsize : hypotheses.size = fields.size)
    (indTypes : Array InductiveType) (minors : Array Expr)
    (lvls : List Level) :
    ProducerStagedSemanticBoundGeneratedRecursiveCalls indTypes stats motives
      minors lvls Rfield decl rootScope fields
        (calls.map fun call => call.build indTypes stats motives minors lvls)
        fields.size := by
  refine {
    covered := Nat.le_refl _
    size := by simp [H.size_eq, hsize]
    entries := ?_ }
  intro i hi _hiFields
  have hiHypotheses : i < hypotheses.size := by rwa [hsize]
  rcases H.entry i hiHypotheses with
    ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
      hpriorSize, ⟨Horigin⟩⟩
  rcases Horigin.semantic indTypes minors lvls with
    ⟨S, hscope, Hmotive⟩
  have hiCalls : i < calls.size := by rw [H.size_eq, hsize]; exact hi
  have hbuilt :
      (calls.map fun call =>
        call.build indTypes stats motives minors lvls)[i]! =
          calls[i]!.build indTypes stats motives minors lvls := by
    simp [Array.getElem!_eq_getD, Array.getD, hi, hiCalls]
  rw [hbuilt]
  rw [show fields[i] = fields[i]! from
    (getElem!_pos fields i hi).symm]
  exact ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
    hpriorSize, depth + i, S, hscope, Hmotive⟩

theorem RecInfoCallBlueprintOrigins.boundGeneratedCalls
    {sourceFullContext fieldRoot : AddInductive.Context}
    {recursiveFields hypotheses : Array Expr}
    {origins : RecInfoMinorHypothesisTypeOrigins sourceFullContext
      recursiveFields hypotheses}
    {calls : Array AddInductive.RecCallBlueprint}
    (H : RecInfoCallBlueprintOrigins origins calls)
    (hfieldRoot : origins.fieldRoot = fieldRoot)
    (hsize : hypotheses.size = recursiveFields.size)
    (indTypes : Array InductiveType) (minors : Array Expr)
    (lvls : List Level) :
    BoundGeneratedRecursiveCalls indTypes origins.stats
      (origins.recInfos.map (·.motive)) minors lvls fieldRoot recursiveFields
      (calls.map fun call => call.build indTypes origins.stats
        (origins.recInfos.map (·.motive)) minors lvls)
      recursiveFields.size := by
  subst fieldRoot
  refine {
    covered := Nat.le_refl _
    size := ?_
    entries := ?_ }
  · simp [H.size_eq, hsize]
  · intro i hi _hiFields
    have hiHypotheses : i < hypotheses.size := by omega
    have Hentry := H.entry i hiHypotheses
    rw [getElem!_pos recursiveFields i hi] at Hentry
    rcases Hentry with
      ⟨originRoot, sourceType, O, D, HoriginRoot, htype, hcall⟩
    let value := calls[i]!.build indTypes origins.stats
      (origins.recInfos.map (·.motive)) minors lvls
    have hiCalls : i < calls.size := by rw [H.size_eq]; exact hiHypotheses
    have hvalue :
        (calls.map fun call => call.build indTypes origins.stats
          (origins.recInfos.map (·.motive)) minors lvls)[i]! = value := by
      rw [getElem!_pos _ i (by simpa using hiCalls)]
      simp [value, getElem!_pos calls i hiCalls]
    rw [hvalue]
    refine ⟨{
      exposedType := O.exposedType
      ownerIdx := O.ownerIdx
      owner_valid := O.owner_valid
      localArgs := O.args
      current := O.current
      current_wf := O.current_wf
      current_extends := HoriginRoot.trans O.current_extends
      arguments_bound := O.arguments_bound.rebaseRoot HoriginRoot
      value_eq := ?_ }⟩
    dsimp [value]
    rw [hcall]
    simp only [AddInductive.RecCallBlueprint.build]
    simp [AddInductive.getIIndices, O.owner_valid]

/-- A bound rule together with the exact producer components used to build
it.  These projection equalities prevent later semantic assembly from
recovering them by replay or alpha-conversion. -/
structure RetainedBlueprintBoundRule
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (S : RecInfoMinorTypeShape) (T : RecInfoMinorTraversalShape)
    (B : AddInductive.RecRuleBlueprint)
    (minorIdx : Nat) (fieldRoot outerRoot : AddInductive.Context) where
  certificate : BoundGeneratedRecursorRule indTypes stats motives minors
    lvls S.constructor minorIdx
      (B.build indTypes stats motives minors lvls outerRoot.lctx)
  root_eq : certificate.root = fieldRoot
  target_eq : certificate.target = T.terminal
  allArgs_eq : certificate.allArgs = S.fields
  recursiveArgs_eq : certificate.recursiveArgs = S.recursiveFields
  recursiveResults_eq : certificate.recursiveResults =
    B.recursiveCalls.map fun call =>
      call.build indTypes stats motives minors lvls

theorem RecInfoRuleBlueprintOriginAt.boundGeneratedRule
    {stats : AddInductive.InductiveStats}
    {S : RecInfoMinorTypeShape} {minor : Expr}
    {B : AddInductive.RecRuleBlueprint}
    (Horigin : RecInfoRuleBlueprintOriginAt stats S minor B)
    (indTypes : Array InductiveType) (motives minors : Array Expr)
    (lvls : List Level) (minorIdx : Nat)
    {fieldRoot outerRoot : AddInductive.Context}
    (HfieldWF : BindingContextWF fieldRoot)
    (HouterWF : BindingContextWF outerRoot)
    (HfieldSource : BindingContextLE fieldRoot S.sourceFullContext)
    (HfieldOuter : BindingContextLE fieldRoot outerRoot)
    (Hparams : BoundFVarArray outerRoot stats.params)
    (Hmotives : BoundFVarArray outerRoot motives)
    (Hminors : BoundFVarArray outerRoot minors)
    (HouterNodup : ((Hparams.fvars ++ Hmotives.fvars) ++
      Hminors.fvars).Nodup)
    (Hfields : BoundFVarArray fieldRoot S.fields)
    (HfieldsNodup : Hfields.fvars.Nodup)
    (Hrecursive : BoundFVarArray fieldRoot S.recursiveFields)
    (hrecursive : S.recursiveFields.toList.Sublist S.fields.toList)
    (HrecursiveNodup : Hrecursive.fvars.Nodup)
    (hfieldsFresh : ∀ fv ∈ Hfields.fvars,
      fv ∉ (Hparams.fvars ++ Hmotives.fvars) ++ Hminors.fvars)
    (hminor : minorIdx < minors.size)
    (hminorEq : minors[minorIdx]! = minor)
    (Hcalls : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      fieldRoot S.recursiveFields
      (B.recursiveCalls.map fun call =>
        call.build indTypes stats motives minors lvls)
      S.recursiveFields.size) :
    ∃ T, S.traversal = some T ∧
      Nonempty (RetainedBlueprintBoundRule indTypes stats motives minors lvls
        S T B minorIdx fieldRoot outerRoot) := by
  rcases Horigin with
    ⟨hctor, hfields, hlctx, hminorBlueprint, traversal, origins,
      htraversal, horigins, htargetOwner, htargetIndices, HcallOrigins⟩
  let Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      S.constructor minorIdx
      (B.build indTypes stats motives minors lvls outerRoot.lctx) := {
    root := fieldRoot
    outerRoot := outerRoot
    root_wf := HfieldWF
    outer_wf := HouterWF
    root_le_outer := HfieldOuter
    target := traversal.terminal
    allArgs := S.fields
    recursiveArgs := S.recursiveFields
    recursiveResults := B.recursiveCalls.map fun call =>
      call.build indTypes stats motives minors lvls
    minor_valid := hminor
    params_bound := Hparams
    motives_bound := Hmotives
    minors_bound := Hminors
    outer_binders_nodup := HouterNodup
    all_args_bound := Hfields
    recursive_args_bound := Hrecursive
    recursive_args_sublist := hrecursive
    all_args_nodup := HfieldsNodup
    recursive_args_nodup := HrecursiveNodup
    all_args_outer_fresh := hfieldsFresh
    recursive_calls := Hcalls
    ctor_eq := by
      simpa [AddInductive.RecRuleBlueprint.build] using hctor
    fields_eq := by
      simp [AddInductive.RecRuleBlueprint.build, hfields]
    rhs_eq := by
      simp only [AddInductive.RecRuleBlueprint.build]
      rw [hfields, hminorBlueprint, hlctx, hminorEq]
      have hfieldLambda := Hfields.mkLambda_mono HfieldSource
        (mkAppN (mkAppN minor S.fields)
          (B.recursiveCalls.map fun call =>
            call.build indTypes stats motives minors lvls))
      exact congrArg (fun body =>
        outerRoot.lctx.mkLambda stats.params <|
        outerRoot.lctx.mkLambda motives <|
          outerRoot.lctx.mkLambda minors body) hfieldLambda }
  exact ⟨traversal, htraversal,
    ⟨⟨Hrule, rfl, rfl, rfl, rfl, rfl⟩⟩⟩

theorem RecursorFieldDecisions.selectedSublist
    (H : RecursorFieldDecisions stats root source c terminal fields
      recursiveFields positions) :
    recursiveFields.toList.Sublist fields.toList := by
  induction H with
  | nil => exact .slnil
  | @nonrecursive c name dom body bi fields recursiveFields positions
      Hdecision _ ih =>
      simpa using ih.append
        (List.nil_sublist [Expr.fvar ⟨c.ngen.curr⟩])
  | @recursive c name dom body bi fields recursiveFields positions target
      Hdecision _ ih =>
      simpa using ih.append
        (List.Sublist.refl [Expr.fvar ⟨c.ngen.curr⟩])

/-- The retained blueprint row has exactly one entry for every constructor
of its source owner.  This is derived from the completed second-pass row
counts; the blueprint builder itself does not need to rerun the constructor
traversal to discover its output cardinality. -/
theorem RecInfoRuleBlueprintOrigins.ownerRowSize
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {Horigins : RecInfoTypeOrigins c recInfos}
    (H : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < recInfos.size) :
    recInfos[owner]!.ruleBlueprints.size =
      indTypes[owner]!.ctors.length := by
  calc
    recInfos[owner]!.ruleBlueprints.size =
        Horigins.minorTypes[owner]!.size := H.rows_size owner howner
    _ = recInfos[owner]!.minors.size :=
      (Horigins.minors owner howner).size_eq
    _ = indTypes[owner]!.ctors.length := hcounts owner howner

/-- At a valid owner-local position, the retained blueprint origin names the
literal constructor at that same position in the source owner row. -/
theorem RecInfoRuleBlueprintOrigins.entryConstructor
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {Horigins : RecInfoTypeOrigins c recInfos}
    (H : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (Hsources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    (owner : Nat) (howner : owner < recInfos.size)
    (hsourceOwner : owner < indTypes.size)
    (localIndex : Nat)
    (hlocal : localIndex < Horigins.minorTypes[owner]!.size) :
    let S := Horigins.minorShapes owner howner localIndex hlocal
    let B := recInfos[owner]!.ruleBlueprints[localIndex]!
    ∃ ctor, indTypes[owner]!.ctors[localIndex]? = some ctor ∧
      B.ctor = ctor.name := by
  have Hentry := H.entry owner howner localIndex hlocal
  have Hsource := Hsources owner howner hsourceOwner localIndex hlocal
  dsimp only
  refine ⟨Horigins.minorShapes owner howner localIndex hlocal |>.constructor,
    ?_, Hentry.1⟩
  have hconstructor :=
    (Horigins.minorShapes owner howner localIndex hlocal).sourceConstructor
  rw [Hsource.2.1, Hsource.2.2.1] at hconstructor
  exact hconstructor

/-- Per-owner minor cardinalities identify the flattened minor prefix with
the constructor prefix consumed by recursor installation. -/
theorem recInfoMinorPrefixLength_eq
    (recInfos : Array AddInductive.RecInfo)
    (indTypes : Array InductiveType)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner ≤ recInfos.size) :
    ((recInfos.toList.take owner).flatMap
      (fun info => info.minors.toList)).length =
      recursorMinorOffset indTypes owner := by
  induction owner with
  | zero => simp [recursorMinorOffset]
  | succ owner ih =>
      have hrec : owner < recInfos.size := by omega
      have hind : owner < indTypes.size := by omega
      rw [recursorMinorOffset_step indTypes owner hind]
      simp [List.take_add_one, hrec, ih (by omega)]
      simpa [getElem!_pos recInfos owner hrec,
        getElem!_pos indTypes owner hind] using hcounts owner hrec

/-- The flattened minor selected by the canonical owner offset is literally
the row-local minor paired with that owner's retained rule blueprint. -/
theorem recInfoFlatMinorAtOffset
    (recInfos : Array AddInductive.RecInfo)
    (indTypes : Array InductiveType)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < recInfos.size)
    (localIndex : Nat)
    (hlocal : localIndex < recInfos[owner]!.minors.size) :
    (recInfos.flatMap (·.minors))[
      recursorMinorOffset indTypes owner + localIndex]! =
      recInfos[owner]!.minors[localIndex]! := by
  have hprefix := recInfoMinorPrefixLength_eq recInfos indTypes hsize
    hcounts owner (Nat.le_of_lt howner)
  have hrowsOwner : owner < recInfos.toList.length := by simpa using howner
  have hrowLocal : localIndex < recInfos.toList[owner].minors.toList.length := by
    simpa [getElem!_pos recInfos owner howner] using hlocal
  have hflatIndex :
      ((recInfos.toList.take owner).flatMap
          (fun info => info.minors.toList)).length + localIndex <
        (recInfos.toList.flatMap
          (fun info => info.minors.toList)).length := by
    rw [hprefix, ← Array.toList_flatMap, Array.length_toList]
    have hindOwner : owner < indTypes.size := by omega
    have hroom := recursorMinorOffset_room indTypes owner hindOwner
    have hrowCount := hcounts owner howner
    have htotal : (recInfos.flatMap (·.minors)).size =
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      calc
        (recInfos.flatMap (·.minors)).size =
            (indTypes.flatMap fun type => type.ctors.toArray).size :=
          mkRecInfos.flatMinors_size hsize hcounts
        _ = (indTypes.toList.flatMap
            (fun type => type.ctors)).length :=
          by simpa [ownedConstructors] using
            (ownedConstructors_length_eq_flattened_size indTypes).symm
    rw [htotal]
    omega
  have Hget := List.flatMap_getElem_prefix recInfos.toList
    (fun info => info.minors.toList) owner localIndex hrowsOwner
    hrowLocal hflatIndex
  have harrayIndex : recursorMinorOffset indTypes owner + localIndex <
      (recInfos.flatMap (·.minors)).size := by
    change recursorMinorOffset indTypes owner + localIndex <
      (recInfos.flatMap (·.minors)).toList.length
    simpa [Array.toList_flatMap, hprefix] using hflatIndex
  have Hget' :
      (recInfos.flatMap (·.minors))[
        recursorMinorOffset indTypes owner + localIndex]'harrayIndex =
      recInfos[owner]!.minors[localIndex]'hlocal := by
    change (recInfos.flatMap (·.minors)).toList[
        recursorMinorOffset indTypes owner + localIndex] =
      recInfos[owner]!.minors.toList[localIndex]
    simpa [Array.toList_flatMap, hprefix,
      getElem!_pos recInfos owner howner] using Hget
  rw [getElem!_pos (recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes owner + localIndex) harrayIndex,
    getElem!_pos recInfos[owner]!.minors localIndex hlocal]
  exact Hget'

theorem RecInfoRuleBlueprintOriginAt.boundGeneratedRuleOfSemanticSource
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {S : RecInfoMinorTypeShape} {minor : Expr}
    {B : AddInductive.RecRuleBlueprint}
    (Horigin : RecInfoRuleBlueprintOriginAt stats S minor B)
    {outerRoot : AddInductive.Context} {recLparams : List Name}
    {Router : RecursorContextWF outerRoot recLparams}
    (HS : RecInfoMinorSemanticSource Router S)
    (Hhas : S.HasHypothesisTypeOrigins stats recInfos)
    (hrecursiveFields : HS.traversal.recursiveFields = S.recursiveFields)
    (indTypes : Array InductiveType) (lvls : List Level)
    (minorIdx : Nat)
    (Hparams : BoundFVarArray outerRoot stats.params)
    (Hbindings : RecInfoBindings outerRoot recInfos)
    (HouterNodup : ((Hparams.fvars ++ Hbindings.motives.fvars) ++
      Hbindings.flatMinors.fvars).Nodup)
    (hminor : minorIdx < (recInfos.flatMap (·.minors)).size)
    (hminorEq : (recInfos.flatMap (·.minors))[minorIdx]! = minor)
    (hfieldsFresh : ∀ fv ∈
      HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars) :
    Nonempty (RetainedBlueprintBoundRule indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S HS.traversal B minorIdx HS.traversal.terminalContext outerRoot) := by
  rcases Horigin with
    ⟨hctor, hfields, hlctx, hminorBlueprint, traversal, origins,
      htraversal, horigins, htargetOwner, htargetIndices, HcallOrigins⟩
  have htraversalEq : HS.traversal = traversal := by
    rw [HS.traversal_eq] at htraversal
    exact Option.some.inj htraversal
  subst traversal
  have hfieldRoot : origins.fieldRoot = HS.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins HS.traversal horigins
      HS.traversal_eq
  have HcallsRaw := HcallOrigins.boundGeneratedCalls hfieldRoot
    S.hypotheses_size indTypes (recInfos.flatMap (·.minors)) lvls
  have Hhas' : origins.stats = stats ∧
      origins.recInfos.map (·.motive) = recInfos.map (·.motive) := by
    simpa [RecInfoMinorTypeShape.HasHypothesisTypeOrigins, horigins] using Hhas
  have hstats : origins.stats = stats := by
    exact Hhas'.1
  have hmotives : origins.recInfos.map (·.motive) =
      recInfos.map (·.motive) := by
    exact Hhas'.2
  rw [hstats, hmotives] at HcallsRaw
  have hselected : S.recursiveFields.toList.Sublist S.fields.toList := by
    rw [← HS.traversal_fields, ← hrecursiveFields]
    exact HS.traversal.decisions.selectedSublist
  rcases BoundFVarArray.ofSublist
      HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray hselected with
    ⟨Hrecursive⟩
  have HrecursiveNodup : Hrecursive.fvars.Nodup := by
    have hallExpr : S.fields.toList.Nodup := by
      rw [HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.expressions]
      exact List.Pairwise.map Expr.fvar
        (fun _ _ hne heq => hne (Expr.fvar.inj heq))
        HS.fieldsRecent.toFreshBoundFVarArray.nodup
    have hselectedExpr : S.recursiveFields.toList.Nodup :=
      hallExpr.sublist hselected
    rw [Hrecursive.expressions] at hselectedExpr
    change List.Pairwise (fun a b : Expr => a ≠ b)
      (Hrecursive.fvars.map Expr.fvar) at hselectedExpr
    rw [List.pairwise_map] at hselectedExpr
    change List.Pairwise (fun a b : FVarId => a ≠ b) Hrecursive.fvars
    exact hselectedExpr.imp fun hneq heq =>
      hneq (congrArg Expr.fvar heq)
  rcases RecInfoRuleBlueprintOriginAt.boundGeneratedRule
    (Horigin := ⟨hctor, hfields, hlctx, hminorBlueprint,
      HS.traversal, origins, HS.traversal_eq, horigins,
      htargetOwner, htargetIndices, HcallOrigins⟩)
    indTypes (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
    minorIdx HS.terminalWF.toBindingContextWF Router.toBindingContextWF
    HS.hypothesesRecent.contextLE
    (HS.hypothesesRecent.contextLE.trans HS.extension.contextLE)
    Hparams Hbindings.motives Hbindings.flatMinors HouterNodup
    HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    HS.fieldsRecent.toFreshBoundFVarArray.nodup Hrecursive hselected
    HrecursiveNodup hfieldsFresh hminor hminorEq HcallsRaw with
      ⟨T, hT, ⟨Hretained⟩⟩
  have hTeq : T = HS.traversal := Option.some.inj
    (hT.symm.trans HS.traversal_eq)
  subst T
  exact ⟨Hretained⟩

/-- Semantic payload indexed by the producer's literal components, before
transport to the projections of the retained bound-rule certificate. -/
structure RetainedGeneratedRuleSemantics
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (sourceCtor : Constructor) (minorIdx : Nat) (sourceRule : RecursorRule)
    (producerRoot : AddInductive.Context) (target : Expr)
    (allArgs recursiveArgs recursiveResults : Array Expr)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (expectedOwnerIdx : Nat) where
  depth : Nat
  context : RecursorContextWF producerRoot recLparams
  fieldRoot : AddInductive.Context
  fieldRootContext : RecursorContextWF fieldRoot recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix fieldRootContext stats
    parameterDepth
  parameterDecls : VLCtx
  parameterDecls_eq : parameterSuffix.parameterDecls = parameterDecls
  fieldRootExtension : RecursorContextExtension fieldRootContext Rroot
  fieldsRecent : RecursorRecentBoundFVarArray fieldRootContext context allArgs
  parameterTail : Expr
  parameterPrefix : RecursorParamPrefix stats 0 sourceCtor.type parameterTail
  parameterTail_fvars : parameterTail.FVarsIn
    (· ∈ ExprArrayFVarIds stats.params)
  parameterTarget : VExpr
  parameterTranslation : TrExprS fieldRootContext.venv recLparams
    fieldRootContext.mlctx.vlctx parameterTail parameterTarget
  parameterType : fieldRootContext.venv.IsType recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
  fieldOpening : ConstructorFieldOpening parameterTail target allArgs
  fieldParameterUp : IsFVarUpSet (fun fv =>
    fv ∈ fieldsRecent.fvars ∨ fv ∈ ExprArrayFVarIds stats.params)
      context.mlctx.vlctx
  context_venv : context.venv = Rroot.venv
  validStats : RecursorValidAppStatsWF context.venv recLparams
    context.mlctx.vlctx stats decl depth
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  expected_owner_lt : expectedOwnerIdx < decl.types.length
  expected_target_valid : AddInductive.isValidIndAppIdx stats target
    expectedOwnerIdx = true
  targetTarget : VExpr
  target_not_forall : target.isForall = false
  target_translation : TrExprS context.venv recLparams context.mlctx.vlctx
    target targetTarget
  target_type : context.venv.IsType recLparams.length
    context.mlctx.vlctx.toCtx targetTarget
  fieldTargetDefEq : fieldRootContext.venv.IsDefEqU recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
      (context.mlctx.mkForall' allArgs.size fieldsRecent.size_le targetTarget)
  constructorTarget : VExpr
  constructor_translation : TrExprS context.venv recLparams
    context.mlctx.vlctx
      (mkAppN (mkAppN (.const sourceCtor.name stats.levels) stats.params)
        allArgs) constructorTarget
  constructor_typing : context.venv.HasType recLparams.length
    context.mlctx.vlctx.toCtx constructorTarget targetTarget
  target_valid : AddInductive.isValidIndApp? stats target = some ownerIdx
  validated : RecursorValidatedIndAppAt context.venv recLparams
    context.mlctx.vlctx stats decl depth target targetTarget ownerIdx
  fields : List (RecursorRecursiveDomainAt context.venv decl recLparams.length)
  selection : RecursorFieldSelectionsAt context.venv decl recLparams.length
    allArgs recursiveArgs fields
  decisionPositions : List Nat
  decisions : RecursorFieldDecisions stats fieldRoot parameterTail producerRoot
    target allArgs recursiveArgs decisionPositions
  calls : ProducerStagedSemanticBoundGeneratedRecursiveCalls indTypes stats motives
    minors lvls context decl
      (fun fv => fv ∈ fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      recursiveArgs recursiveResults recursiveArgs.size

theorem RetainedGeneratedRuleSemantics.toSemantics
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (C : RetainedGeneratedRuleSemantics indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule producerRoot target allArgs recursiveArgs
      recursiveResults Rroot decl expectedOwnerIdx)
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (hroot : H.root = producerRoot) (htarget : H.target = target)
    (hall : H.allArgs = allArgs) (hrecursive : H.recursiveArgs = recursiveArgs)
    (hresults : H.recursiveResults = recursiveResults)
    {recInfos : Array AddInductive.RecInfo} {elimLevel : Level}
    (binding : RecursorMotiveBinding C.context
      recInfos[C.ownerIdx]! elimLevel)
    (HmotiveTelescope : Nonempty
      (RecursorMotiveTelescopeEvidence C.context stats
        recInfos[C.ownerIdx]! binding target C.targetTarget))
    (Hlookup : RecInfoMotiveTelescopeLookup C.context stats decl recInfos
      elimLevel) :
    ∃ S : H.Semantics Rroot decl expectedOwnerIdx,
      ∃ binding' : RecursorMotiveBinding S.context
          recInfos[S.ownerIdx]! elimLevel,
        Nonempty (RecursorMotiveTelescopeEvidence S.context stats
          recInfos[S.ownerIdx]! binding' H.target S.targetTarget) ∧
        RecInfoMotiveTelescopeLookup S.context stats decl recInfos elimLevel ∧
        S.recursivePositions = C.decisionPositions ∧
        S.parameterDecls = C.parameterDecls ∧
        Nonempty (ProducerStagedSemanticBoundGeneratedRecursiveCalls
          indTypes stats motives minors lvls S.context decl
            (fun fv => fv ∈ S.fieldOpening.fvars ∨
              fv ∈ ExprArrayFVarIds stats.params)
            H.recursiveArgs H.recursiveResults H.recursiveArgs.size) := by
  subst producerRoot
  subst target
  subst allArgs
  subst recursiveArgs
  subst recursiveResults
  let S : H.Semantics Rroot decl expectedOwnerIdx := {
    depth := C.depth
    context := C.context
    fieldRoot := C.fieldRoot
    fieldRootContext := C.fieldRootContext
    parameterDepth := C.parameterDepth
    parameterSuffix := C.parameterSuffix
    parameterDecls := C.parameterDecls
    parameterDecls_eq := C.parameterDecls_eq
    fieldRootExtension := C.fieldRootExtension
    fieldsRecent := C.fieldsRecent
    parameterTail := C.parameterTail
    parameterPrefix := C.parameterPrefix
    parameterTail_fvars := C.parameterTail_fvars
    parameterTarget := C.parameterTarget
    parameterTranslation := C.parameterTranslation
    parameterType := C.parameterType
    fieldOpening := C.fieldOpening
    fieldParameterUp := C.fieldParameterUp
    context_venv := C.context_venv
    validStats := C.validStats
    ownerIdx := C.ownerIdx
    owner_lt := C.owner_lt
    expected_owner_lt := C.expected_owner_lt
    expected_target_valid := C.expected_target_valid
    targetTarget := C.targetTarget
    target_not_forall := C.target_not_forall
    target_translation := C.target_translation
    target_type := C.target_type
    fieldTargetDefEq := C.fieldTargetDefEq
    constructorTarget := C.constructorTarget
    constructor_translation := by
      simpa [BoundGeneratedRecursorRule.sourceConstructorMajor] using
        C.constructor_translation
    constructor_typing := C.constructor_typing
    target_valid := C.target_valid
    validated := C.validated
    fields := C.fields
    selection := C.selection
    decisionPositions := C.decisionPositions
    decisions := C.decisions
    calls := C.calls.toStaged }
  exact ⟨S, binding, HmotiveTelescope, Hlookup, rfl, rfl, ⟨C.calls⟩⟩

/-- The motive binder and telescope retained at the exact context in which
the rule target was validated.  This is producer evidence, not a replay of
the completed recursor pass. -/
structure BoundGeneratedRecursorRule.ProducerMotiveEvidence
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) where
  minorShape : RecInfoMinorTypeShape
  minorTraversal : RecInfoMinorTraversalShape
  minorTraversal_eq : minorShape.traversal = some minorTraversal
  decisionPositions_eq : minorTraversal.recursivePositions =
    S.recursivePositions
  calls : ProducerStagedSemanticBoundGeneratedRecursiveCalls indTypes stats
    motives minors lvls S.context decl
      (fun fv => fv ∈ S.fieldOpening.fvars ∨
        fv ∈ ExprArrayFVarIds stats.params)
      H.recursiveArgs H.recursiveResults H.recursiveArgs.size
  binding : RecursorMotiveBinding S.context recInfos[S.ownerIdx]! elimLevel
  telescope : Nonempty (RecursorMotiveTelescopeEvidence S.context stats
    recInfos[S.ownerIdx]! binding H.target S.targetTarget)
  motiveLookup : RecInfoMotiveTelescopeLookup S.context stats decl recInfos
    elimLevel

/-- Row-wise producer motive evidence, indexed by the exact semantic batch
stored for installation.  Indexing by the batch prevents a later consumer
from pairing a telescope with a different semantic reconstruction. -/
inductive SemanticBoundGeneratedRecursorRules.ProducerMotiveEvidence
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) :
    {ctors : List Constructor} → {start : Nat} →
    {rules : List RecursorRule} →
    SemanticBoundGeneratedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      Rroot decl ownerIdx ctors start rules → Prop
  | nil : ProducerMotiveEvidence recInfos elimLevel
      (.nil : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx [] start [])
  | cons
      (Hrule : BoundGeneratedRecursorRule indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        ctor start rule)
      (S : Hrule.Semantics Rroot decl ownerIdx)
      (Hmotive : Nonempty
        (Hrule.ProducerMotiveEvidence S recInfos elimLevel))
      (Htail : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx ctors (start + 1) rules)
      (HtailMotive : ProducerMotiveEvidence recInfos elimLevel Htail) :
      ProducerMotiveEvidence recInfos elimLevel
        (.cons Hrule ⟨S⟩ Htail)

theorem SemanticBoundGeneratedRecursorRules.ProducerMotiveEvidence.entry
    {ctors : List Constructor} {start : Nat} {rules : List RecursorRule}
    {H : SemanticBoundGeneratedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      Rroot decl ownerIdx ctors start rules}
    (M : SemanticBoundGeneratedRecursorRules.ProducerMotiveEvidence
      recInfos elimLevel H) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
          (ctors[i]'hctor) (start + i) (rules[i]'hrule),
        ∃ S : Hrule.Semantics Rroot decl ownerIdx,
          Nonempty (Hrule.ProducerMotiveEvidence S recInfos elimLevel) := by
  induction M with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor branchStart rule _ _ _ _ _ ctors rules Hrule S
      Hmotive Htail HtailMotive ih =>
      intro i hctor hrule
      cases i with
      | zero => exact ⟨Hrule, S, Hmotive⟩
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        have hoffset : branchStart + 1 + i = branchStart + (i + 1) := by
          omega
        rw [hoffset] at h
        exact h

/-- The producer evidence for one rule, tied to the exact persistent origin
row and local constructor slot from which its blueprint was emitted. -/
structure BoundGeneratedRecursorRule.ProducerOriginEvidence
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level)
    (Horigins : RecInfoTypeOrigins semanticRoot recInfos)
    (owner localIndex : Nat) where
  producer : H.ProducerMotiveEvidence S recInfos elimLevel
  owner_lt : owner < recInfos.size
  local_lt : localIndex < Horigins.minorTypes[owner]!.size
  shape_eq : producer.minorShape =
    Horigins.minorShapes owner owner_lt localIndex local_lt

theorem RecInfoTypeOrigins.minorShapes_congr
    (H : RecInfoTypeOrigins c recInfos)
    {owner owner' localIndex localIndex' : Nat}
    (howner : owner = owner')
    (owner_lt : owner < recInfos.size) (owner_lt' : owner' < recInfos.size)
    (hlocal : localIndex = localIndex')
    (local_lt : localIndex < H.minorTypes[owner]!.size)
    (local_lt' : localIndex' < H.minorTypes[owner']!.size) :
    H.minorShapes owner owner_lt localIndex local_lt =
      H.minorShapes owner' owner_lt' localIndex' local_lt' := by
  subst owner'
  subst localIndex'
  rfl

/-- Row-wise origin alignment for the exact semantic batch.  The local slot
advances with the constructor/rule batch, so consumers recover the same
`H.origins` shape without any alpha replay. -/
inductive SemanticBoundGeneratedRecursorRules.ProducerOriginEvidence
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level)
    (Horigins : RecInfoTypeOrigins semanticRoot recInfos)
    {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) :
    (localStart : Nat) →
    {ctors : List Constructor} → {start : Nat} →
    {rules : List RecursorRule} →
    SemanticBoundGeneratedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      Rroot decl ownerIdx ctors start rules → Prop
  | nil : ProducerOriginEvidence recInfos elimLevel Horigins Rroot localStart
      (.nil : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx [] start [])
  | cons
      (Hrule : BoundGeneratedRecursorRule indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        ctor start rule)
      (S : Hrule.Semantics Rroot decl ownerIdx)
      (Horigin : Nonempty (Hrule.ProducerOriginEvidence S recInfos
        elimLevel Horigins ownerIdx localStart))
      (Htail : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx ctors (start + 1) rules)
      (HtailOrigin : ProducerOriginEvidence recInfos elimLevel Horigins Rroot
        (localStart + 1) Htail) :
      ProducerOriginEvidence recInfos elimLevel Horigins Rroot localStart
        (.cons Hrule ⟨S⟩ Htail)

/-- Assemble the semantic certificate for the exact retained blueprint rule.
Every field comes from first-pass producer evidence; no constructor traversal,
call generation, inference, or alpha-renaming is replayed. -/
theorem RetainedBlueprintBoundRule.semanticsOfProducer
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {S : RecInfoMinorTypeShape} {B : AddInductive.RecRuleBlueprint}
    {outerRoot : AddInductive.Context} {recLparams : List Name}
    {Router : RecursorContextWF outerRoot recLparams}
    {indTypes : Array InductiveType} {lvls : List Level}
    {minorIdx expectedOwnerIdx : Nat} {elimLevel : Level}
    (HS : RecInfoMinorSemanticSource Router S)
    (H : RetainedBlueprintBoundRule indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S HS.traversal B minorIdx HS.traversal.terminalContext outerRoot)
    (Hsem : RecInfoRuleBlueprintSemanticOriginAt Router decl stats recInfos
      elimLevel parameterDecls expectedOwnerIdx S B) :
    ∃ Ssemantic : H.certificate.Semantics Router decl expectedOwnerIdx,
      ∃ producer : H.certificate.ProducerMotiveEvidence Ssemantic recInfos
          elimLevel,
        producer.minorShape = S ∧
        Ssemantic.parameterDecls = parameterDecls := by
  unfold RecInfoRuleBlueprintSemanticOriginAt at Hsem
  rcases Hsem with
    ⟨_origins, _horigins, _hstats, _hmotives, F, hparameterDecls, depth,
      HvalidStats, fields, Hselection,
      hexpectedValid, hexpectedLt, ownerIdx,
      htargetValid, HvalidatedNonempty, binding, Htail⟩
  rcases HvalidatedNonempty with ⟨Hvalidated⟩
  let HmotiveTelescope := Htail.1
  let Htail' := Htail.2
  let HlookupNonempty := Htail'.1
  let HcallsNonempty := Htail'.2
  rcases HlookupNonempty with ⟨Hlookup⟩
  let Hcalls := Classical.choice HcallsNonempty
  have htraversalEq : HS.traversal = F.traversal :=
    Option.some.inj (HS.traversal_eq.symm.trans F.traversal_eq)
  have hroot : H.certificate.root = F.traversal.terminalContext :=
    H.root_eq.trans (congrArg (·.terminalContext) htraversalEq)
  have htarget : H.certificate.target = F.traversal.terminal :=
    H.target_eq.trans (congrArg (·.terminal) htraversalEq)
  have hterminalNotForall : F.traversal.terminal.isForall = false := by
    rw [← Expr.abstractList_isForall F.traversal.terminal
      F.traversal.fieldFVars, F.traversal.fieldClosed]
    exact F.traversal.fieldResidual_not_forall
  have Hstaged := Hcalls.retainedGeneratedCalls S.hypotheses_size
    indTypes (recInfos.flatMap (·.minors)) lvls
  let C : RetainedGeneratedRuleSemantics indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
      S.constructor minorIdx
      (B.build indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors)) lvls outerRoot.lctx)
      F.traversal.terminalContext F.traversal.terminal S.fields
      S.recursiveFields
      (B.recursiveCalls.map fun call => call.build indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls)
      Router decl expectedOwnerIdx := {
    depth := depth
    context := F.terminalWF
    fieldRoot := F.traversal.rootContext
    fieldRootContext := F.rootWF
    parameterDepth := F.parameterDepth
    parameterSuffix := F.parameterSuffix
    parameterDecls := parameterDecls
    parameterDecls_eq := hparameterDecls
    fieldRootExtension := F.fieldsRecent.contextExtension.trans
      F.terminalExtension
    fieldsRecent := F.fieldsRecent
    parameterTail := F.traversal.parameterTail
    parameterPrefix := by
      simpa only [F.traversal_stats, F.traversal_constructor] using
        F.traversal.parameterPrefix
    parameterTail_fvars := F.parameterTail_params
    parameterTarget := F.parameterTarget
    parameterTranslation := F.parameterTranslation
    parameterType := F.parameterType
    fieldOpening := F.fieldOpening
    fieldParameterUp := F.fieldParameterUp
    context_venv := F.terminalExtension.venv_eq.symm
    validStats := HvalidStats
    ownerIdx := ownerIdx
    owner_lt := Hvalidated.target_lt
    expected_owner_lt := hexpectedLt
    expected_target_valid := hexpectedValid
    targetTarget := F.terminalTarget
    target_not_forall := hterminalNotForall
    target_translation := F.terminalTranslation
    target_type := F.terminalType
    fieldTargetDefEq := F.fieldTargetDefEq
    constructorTarget := F.constructorApplication.introTarget
    constructor_translation := by
      simpa [mkAppN, F.traversal_constructor, F.traversal_stats] using
        F.constructorApplication.intro
    constructor_typing := F.constructorApplication.typing
    target_valid := htargetValid
    validated := Hvalidated
    fields := fields
    selection := Hselection
    decisionPositions := F.traversal.recursivePositions
    decisions := by
      simpa only [hroot, htarget, H.allArgs_eq, H.recursiveArgs_eq,
        F.traversal_stats, F.traversal_fields,
        F.traversal_recursiveFields] using F.traversal.decisions
    calls := by
      rw [F.fieldOpening.fvars_eq_bound
        F.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray]
      exact Hstaged }
  rcases C.toSemantics H.certificate hroot htarget H.allArgs_eq
      H.recursiveArgs_eq H.recursiveResults_eq binding HmotiveTelescope
      Hlookup with
    ⟨Ssemantic, binding', HmotiveTelescope', Hlookup', hdecisionPositions,
      hsemanticParameterDecls, ⟨HproducerCalls⟩⟩
  let producer : H.certificate.ProducerMotiveEvidence Ssemantic recInfos
      elimLevel := {
    minorShape := S
    minorTraversal := F.traversal
    minorTraversal_eq := F.traversal_eq
    decisionPositions_eq := hdecisionPositions.symm
    calls := HproducerCalls
    binding := binding'
    telescope := HmotiveTelescope'
    motiveLookup := Hlookup' }
  exact ⟨Ssemantic, producer, rfl, hsemanticParameterDecls⟩

/-- Pointwise retained-blueprint certificates assemble into the ordered rule
batch consumed by recursor installation.  The index in the pointwise premise
is relative to this owner row; the generated minor ordinal advances from the
supplied flattened-row offset. -/
theorem BoundGeneratedRecursorRules.ofEntries
    {ctors : List Constructor} {rules : List RecursorRule} {start : Nat}
    (hsize : ctors.length = rules.length)
    (H : ∀ i (hi : i < ctors.length),
      Nonempty (BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctors[i] (start + i) rules[i])) :
    BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules := by
  induction ctors generalizing rules start with
  | nil =>
    cases rules with
    | nil => exact .nil
    | cons rule rules => simp at hsize
  | cons ctor ctors ih =>
    cases rules with
    | nil => simp at hsize
    | cons rule rules =>
      have hhead := H 0 (by simp)
      have htailSize : ctors.length = rules.length := by simpa using hsize
      refine .cons (by simpa using hhead) (ih htailSize ?_)
      intro i hi
      have hentry := H (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hentry

theorem SemanticBoundGeneratedRecursorRules.ofEntries
    {ctors : List Constructor} {rules : List RecursorRule} {start : Nat}
    (hsize : ctors.length = rules.length)
    (H : ∀ i (hi : i < ctors.length),
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
          ctors[i] (start + i) rules[i],
        Nonempty (Hrule.Semantics Rroot decl ownerIdx)) :
    SemanticBoundGeneratedRecursorRules indTypes stats motives minors lvls
      Rroot decl ownerIdx ctors start rules := by
  induction ctors generalizing rules start with
  | nil =>
    cases rules with
    | nil => exact .nil
    | cons rule rules => simp at hsize
  | cons ctor ctors ih =>
    cases rules with
    | nil => simp at hsize
    | cons rule rules =>
      rcases H 0 (by simp) with ⟨Hhead, HheadSemantics⟩
      have htailSize : ctors.length = rules.length := by simpa using hsize
      refine .cons (by simpa using Hhead) HheadSemantics
        (ih htailSize ?_)
      intro i hi
      have Hentry := H (i + 1) (by simp; omega)
      have hoffset : start + (i + 1) = start + 1 + i := by omega
      rw [hoffset] at Hentry
      simpa using Hentry

theorem SemanticBoundGeneratedRecursorRules.ofEntriesWithProducer
    {ctors : List Constructor} {rules : List RecursorRule} {start : Nat}
    (hsize : ctors.length = rules.length)
    (H : ∀ i (hi : i < ctors.length),
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
          ctors[i] (start + i) rules[i],
        ∃ S : Hrule.Semantics Rroot decl ownerIdx,
          Nonempty (Hrule.ProducerMotiveEvidence S recInfos elimLevel)) :
    ∃ Hrules : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors)) lvls
        Rroot decl ownerIdx ctors start rules,
      Nonempty (Hrules.ProducerMotiveEvidence recInfos elimLevel) := by
  induction ctors generalizing rules start with
  | nil =>
    cases rules with
    | nil => exact ⟨.nil, ⟨.nil⟩⟩
    | cons rule rules => simp at hsize
  | cons ctor ctors ih =>
    cases rules with
    | nil => simp at hsize
    | cons rule rules =>
      rcases H 0 (by simp) with ⟨Hhead, Shead, HheadMotive⟩
      have htailSize : ctors.length = rules.length := by simpa using hsize
      rcases ih htailSize (fun i hi => by
        have Hentry := H (i + 1) (by simp; omega)
        have hoffset : start + (i + 1) = start + 1 + i := by omega
        rw [hoffset] at Hentry
        simpa using Hentry) with ⟨Htail, ⟨HtailMotive⟩⟩
      exact ⟨.cons Hhead ⟨Shead⟩ Htail,
        ⟨.cons Hhead Shead HheadMotive Htail HtailMotive⟩⟩

/-- Assemble the exact retained blueprint row for one mutual-family owner.
All rule syntax comes from the production blueprints; source alignment,
minor ordinals, field freshness, and recursive-call binding are supplied by
the certificates accumulated while producing those blueprints. -/
theorem RecInfoRuleBlueprintOrigins.boundGeneratedRules
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {c : AddInductive.Context}
    {Horigins : RecInfoTypeOrigins c recInfos}
    (H : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (Hsources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    {recLparams : List Name} {R : RecursorContextWF c recLparams}
    (Hsemantics : RecInfoMinorSemanticAlignment R Horigins parameterDecls)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (elimLevel : Level) (owner : Nat) (howner : owner < indTypes.size) :
    let rules := recInfos[owner]!.ruleBlueprints.toList.map fun blueprint =>
      blueprint.build indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
    BoundGeneratedRecursorRules indTypes stats
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels)
      indTypes[owner]!.ctors (recursorMinorOffset indTypes owner) rules := by
  dsimp only
  have hownerRec : owner < recInfos.size := by omega
  have hrowSize := H.ownerRowSize hcounts owner hownerRec
  apply BoundGeneratedRecursorRules.ofEntries (by simpa using hrowSize.symm)
  intro localIndex hlocal
  have hshapeLocal : localIndex < Horigins.minorTypes[owner]!.size := by
    rw [← H.rows_size owner hownerRec]
    rw [hrowSize]
    exact hlocal
  let S := Horigins.minorShapes owner hownerRec localIndex hshapeLocal
  let B := recInfos[owner]!.ruleBlueprints[localIndex]!
  have Horigin : RecInfoRuleBlueprintOriginAt stats S
      recInfos[owner]!.minors[localIndex]! B :=
    H.entry owner hownerRec localIndex hshapeLocal
  have Hsource := Hsources owner hownerRec howner localIndex hshapeLocal
  have hlocalMinor : localIndex < recInfos[owner]!.minors.size := by
    rw [← (Horigins.minors owner hownerRec).size_eq]
    exact hshapeLocal
  rcases Hsemantics owner hownerRec localIndex hshapeLocal with ⟨HSat⟩
  let HS := HSat.semantic
  have hminorEq := recInfoFlatMinorAtOffset recInfos indTypes hsize hcounts
    owner hownerRec localIndex hlocalMinor
  have hminorValid : recursorMinorOffset indTypes owner + localIndex <
      (recInfos.flatMap (·.minors)).size := by
    have htotal := mkRecInfos.flatMinors_size hsize hcounts
    have hroom := recursorMinorOffset_room indTypes owner howner
    have htotalList : (recInfos.flatMap (·.minors)).size =
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      calc
        (recInfos.flatMap (·.minors)).size =
            (indTypes.flatMap fun type => type.ctors.toArray).size := htotal
        _ = (indTypes.toList.flatMap (fun type => type.ctors)).length := by
          simpa [ownedConstructors] using
            (ownedConstructors_length_eq_flattened_size indTypes).symm
    rw [htotalList]
    omega
  have hfieldsFresh : ∀ fv ∈
      HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars,
      fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
        Hbindings.flatMinors.fvars := by
    intro fv hfv
    have hshapeFields :
        HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars =
          S.fields_bound.fvars := by
      exact HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
        |>.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
    rw [hshapeFields] at hfv
    have hfresh := H.fields_outer_fresh owner hownerRec localIndex
      hshapeLocal fv hfv
    simpa only [Hparams.exprArrayFVarIds,
      Hbindings.motives.exprArrayFVarIds,
      Hbindings.flatMinors.exprArrayFVarIds] using hfresh
  let T := Hsource.2.2.2.2.choose
  have htraversal : HS.traversal = T := by
    have hT := Hsource.2.2.2.2.choose_spec.1
    exact Option.some.inj (HS.traversal_eq.symm.trans hT)
  have hrecursive : HS.traversal.recursiveFields = S.recursiveFields := by
    rw [htraversal]
    exact Hsource.2.2.2.2.choose_spec.2.2.2.1
  have Hrule := Horigin.boundGeneratedRuleOfSemanticSource HS
    Hsource.2.2.2.1 hrecursive
    indTypes (AddInductive.getRecLevels elimLevel stats.levels)
    (recursorMinorOffset indTypes owner + localIndex) Hparams Hbindings
    (Hbindings.outerNodup Hparams hnoalias) hminorValid hminorEq
    hfieldsFresh
  have hctor : indTypes[owner]!.ctors[localIndex] = S.constructor := by
    have hget := S.sourceConstructor
    rw [Hsource.2.1, Hsource.2.2.1] at hget
    have hlist : indTypes[owner]!.ctors[localIndex]? =
        some indTypes[owner]!.ctors[localIndex] := by
      exact List.getElem?_eq_getElem hlocal
    rw [hlist] at hget
    exact Option.some.inj hget
  have hblueLocal : localIndex <
      recInfos[owner]!.ruleBlueprints.size := by
    rw [hrowSize]
    exact hlocal
  let built := recInfos[owner]!.ruleBlueprints.toList.map fun blueprint =>
    blueprint.build indTypes stats (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
  have hbuilt : localIndex < built.length := by
    simpa [built] using hblueLocal
  have hruleBang : built[localIndex]! =
      B.build indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) c.lctx := by
    simp [built, B, hblueLocal]
  change Nonempty (BoundGeneratedRecursorRule indTypes stats
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels elimLevel stats.levels)
    indTypes[owner]!.ctors[localIndex]
    (recursorMinorOffset indTypes owner + localIndex) built[localIndex])
  rw [hctor, (getElem!_pos built localIndex hbuilt).symm, hruleBang]
  rcases Hrule with ⟨Hrule⟩
  exact ⟨Hrule.certificate⟩

/-- Semantic owner row assembled from the exact retained blueprint and the
semantic-origin row produced by the same second-pass iteration. -/
theorem RecInfoRuleBlueprintOrigins.semanticBoundGeneratedRules
    {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {recInfos : Array AddInductive.RecInfo}
    {c : AddInductive.Context}
    {Horigins : RecInfoTypeOrigins c recInfos}
    (H : RecInfoRuleBlueprintOrigins stats recInfos Horigins)
    (Hsources : RecInfoMinorSourceAlignment stats indTypes Horigins)
    {recLparams : List Name} {R : RecursorContextWF c recLparams}
    (elimLevel : Level)
    (HsemanticOrigins : RecInfoRuleBlueprintSemanticOrigins R decl stats
      recInfos elimLevel parameterDecls Horigins)
    (Hsemantics : RecInfoMinorSemanticAlignment R Horigins parameterDecls)
    (Hbindings : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : Hbindings.NoAlias Hparams)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (owner : Nat) (howner : owner < indTypes.size) :
    let rules := recInfos[owner]!.ruleBlueprints.toList.map fun blueprint =>
      blueprint.build indTypes stats (recInfos.map (·.motive))
        (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
    ∃ Hrules : SemanticBoundGeneratedRecursorRules indTypes stats
        (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels elimLevel stats.levels) R decl owner
        indTypes[owner]!.ctors (recursorMinorOffset indTypes owner) rules,
      Nonempty (Hrules.ProducerMotiveEvidence recInfos elimLevel) ∧
      ∀ localIndex (hlocal : localIndex < indTypes[owner]!.ctors.length)
          (hrule : localIndex < rules.length),
        ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
            (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
            (AddInductive.getRecLevels elimLevel stats.levels)
            indTypes[owner]!.ctors[localIndex]
            (recursorMinorOffset indTypes owner + localIndex)
            (rules[localIndex]'hrule),
          ∃ S : Hrule.Semantics R decl owner,
            Nonempty (Hrule.ProducerOriginEvidence S recInfos elimLevel
              Horigins owner localIndex) ∧
            S.parameterDecls = parameterDecls := by
  dsimp only
  have hownerRec : owner < recInfos.size := by omega
  have hrowSize := H.ownerRowSize hcounts owner hownerRec
  let rules := recInfos[owner]!.ruleBlueprints.toList.map fun blueprint =>
    blueprint.build indTypes stats (recInfos.map (·.motive))
      (recInfos.flatMap (·.minors))
      (AddInductive.getRecLevels elimLevel stats.levels) c.lctx
  have Hentry : ∀ localIndex
      (hlocal : localIndex < indTypes[owner]!.ctors.length)
      (hrule : localIndex < rules.length),
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats
          (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels)
          indTypes[owner]!.ctors[localIndex]
          (recursorMinorOffset indTypes owner + localIndex)
          (rules[localIndex]'hrule),
        ∃ S : Hrule.Semantics R decl owner,
          Nonempty (Hrule.ProducerOriginEvidence S recInfos elimLevel
            Horigins owner localIndex) ∧
          S.parameterDecls = parameterDecls := by
    intro localIndex hlocal hrule
    have hshapeLocal : localIndex < Horigins.minorTypes[owner]!.size := by
      rw [← H.rows_size owner hownerRec, hrowSize]
      exact hlocal
    let S := Horigins.minorShapes owner hownerRec localIndex hshapeLocal
    let B := recInfos[owner]!.ruleBlueprints[localIndex]!
    have Horigin : RecInfoRuleBlueprintOriginAt stats S
        recInfos[owner]!.minors[localIndex]! B :=
      H.entry owner hownerRec localIndex hshapeLocal
    have Hsource := Hsources owner hownerRec howner localIndex hshapeLocal
    have hlocalMinor : localIndex < recInfos[owner]!.minors.size := by
      rw [← (Horigins.minors owner hownerRec).size_eq]
      exact hshapeLocal
    rcases Hsemantics owner hownerRec localIndex hshapeLocal with ⟨HSat⟩
    let HS := HSat.semantic
    have hminorEq := recInfoFlatMinorAtOffset recInfos indTypes hsize hcounts
      owner hownerRec localIndex hlocalMinor
    have hminorValid : recursorMinorOffset indTypes owner + localIndex <
        (recInfos.flatMap (·.minors)).size := by
      have htotal := mkRecInfos.flatMinors_size hsize hcounts
      have hroom := recursorMinorOffset_room indTypes owner howner
      have htotalList : (recInfos.flatMap (·.minors)).size =
          (indTypes.toList.flatMap (fun type => type.ctors)).length := by
        calc
          (recInfos.flatMap (·.minors)).size =
              (indTypes.flatMap fun type => type.ctors.toArray).size := htotal
          _ = (indTypes.toList.flatMap (fun type => type.ctors)).length := by
            simpa [ownedConstructors] using
              (ownedConstructors_length_eq_flattened_size indTypes).symm
      rw [htotalList]
      omega
    have hfieldsFresh : ∀ fv ∈
        HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars,
        fv ∉ (Hparams.fvars ++ Hbindings.motives.fvars) ++
          Hbindings.flatMinors.fvars := by
      intro fv hfv
      have hshapeFields :
          HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray.fvars =
            S.fields_bound.fvars :=
        HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
          |>.exprArrayFVarIds.symm.trans S.fields_bound.exprArrayFVarIds
      rw [hshapeFields] at hfv
      have hfresh := H.fields_outer_fresh owner hownerRec localIndex
        hshapeLocal fv hfv
      simpa only [Hparams.exprArrayFVarIds,
        Hbindings.motives.exprArrayFVarIds,
        Hbindings.flatMinors.exprArrayFVarIds] using hfresh
    let T := Hsource.2.2.2.2.choose
    have htraversal : HS.traversal = T := by
      have hT := Hsource.2.2.2.2.choose_spec.1
      exact Option.some.inj (HS.traversal_eq.symm.trans hT)
    have hrecursive : HS.traversal.recursiveFields = S.recursiveFields := by
      rw [htraversal]
      exact Hsource.2.2.2.2.choose_spec.2.2.2.1
    rcases Horigin.boundGeneratedRuleOfSemanticSource HS
      Hsource.2.2.2.1 hrecursive indTypes
      (AddInductive.getRecLevels elimLevel stats.levels)
      (recursorMinorOffset indTypes owner + localIndex) Hparams Hbindings
      (Hbindings.outerNodup Hparams hnoalias) hminorValid hminorEq
      hfieldsFresh with ⟨Hrule⟩
    rcases HsemanticOrigins.entry owner hownerRec localIndex hshapeLocal with
      ⟨Hsemantic⟩
    rcases Hrule.semanticsOfProducer HS Hsemantic with
      ⟨HruleSemantic, HmotiveEvidence, hshapeEq,
        hsemanticParameterDecls⟩
    have hctor : indTypes[owner]!.ctors[localIndex] = S.constructor := by
      have hget := S.sourceConstructor
      rw [Hsource.2.1, Hsource.2.2.1] at hget
      have hlist : indTypes[owner]!.ctors[localIndex]? =
          some indTypes[owner]!.ctors[localIndex] :=
        List.getElem?_eq_getElem hlocal
      rw [hlist] at hget
      exact Option.some.inj hget
    have hblueLocal : localIndex <
        recInfos[owner]!.ruleBlueprints.size := by
      rw [hrowSize]
      exact hlocal
    have hruleGet : (rules[localIndex]'hrule) =
        B.build indTypes stats (recInfos.map (·.motive))
          (recInfos.flatMap (·.minors))
          (AddInductive.getRecLevels elimLevel stats.levels) c.lctx := by
      simp [rules, B, hblueLocal]
    rw [hctor, hruleGet]
    exact ⟨Hrule.certificate, HruleSemantic, ⟨{
      producer := HmotiveEvidence
      owner_lt := hownerRec
      local_lt := hshapeLocal
      shape_eq := hshapeEq }⟩, hsemanticParameterDecls⟩
  have hrulesSize : indTypes[owner]!.ctors.length = rules.length := by
    simpa [rules] using hrowSize.symm
  rcases SemanticBoundGeneratedRecursorRules.ofEntriesWithProducer
      hrulesSize (fun localIndex hlocal => by
        have hrule : localIndex < rules.length := by omega
        rcases Hentry localIndex hlocal hrule with
          ⟨Hrule, S, ⟨Horigin⟩, _hparams⟩
        exact ⟨Hrule, S, ⟨Horigin.producer⟩⟩) with
    ⟨Hrules, Hmotive⟩
  exact ⟨Hrules, Hmotive, Hentry⟩

end VerifyInductive

end Lean4Lean
