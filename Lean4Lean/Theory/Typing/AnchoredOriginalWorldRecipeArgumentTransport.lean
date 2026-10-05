import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedReplyMerge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredConversion

/-! Joint resource selection for heterogeneous recipe arguments. The term
query and the assigned-type reply may select different frames. This module
retains both actual frames before interpreting either query; it never infers
resource agreement from their equal numerical capacity. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable def WorldCallFrameData.merge
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {left : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight leftAvailable}
    {right : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight rightAvailable}
    (first : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier left)
    (second : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier right) :
    WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier
      (⟨left.frame.merge right.frame, left.substitutions⟩ :
        OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight
          (leftAvailable.append rightAvailable)) where
  generation := first.generation.merge second.generation
  replayable := ⟨first.replayable, second.replayable⟩
  controlled := first.controlled.merge second.controlled
  compatible := ⟨first.compatible, second.compatible⟩
  hereditary := first.hereditary.merge second.hereditary
  closed := by
    intro index need member selected present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (first.closed index need member selected present)
    · exact List.mem_append_right _ (second.closed index need member selected present)
  capacity := by
    rw [left.frame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨first.capacity, second.capacity⟩
  covered := by
    rw [WorldGenerated.merge_worlds]
    exact first.covered.merge second.covered

/-- The actual argument query and the actual assigned-code query coexist in
one selected frame. Their profiles can differ; neither query is unioned with
an unrelated type observation. All dormant histories remain in the merge. -/
structure WorldRecipeArgumentSelection
    {strata : EquationStratification env} {P : VEnv → Prop}
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (display : OriginalNestedDisplay U common expression assigned)
    (commonLeft commonRight : Subst)
    (controls : OriginalWorldControls strata display.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length)) (input : Profile n) (support : Profile m) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization display.graph env registry target locals commonLeft commonRight available
  frameData : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier realization
  argument : RichGradedResult display.sourceEnv env U registry target display.node locals
    (display.raw.comp commonLeft) available input
  argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation)
  codeFootprint : Footprint
  certificate : RichCert display.sourceEnv env U registry target display.node.typeFormation.node locals
    (display.raw.comp commonLeft) true support codeFootprint
  codeAvailable : codeFootprint.Available available
  codeReady : ControlledStoredQuery controls frontier (.certificate certificate)

private theorem selectArgumentAndCode
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    {left : OriginalCaptureRealization display.graph env registry target leftLocals commonLeft commonRight leftAvailable}
    {right : OriginalCaptureRealization display.graph env registry target rightLocals commonLeft commonRight rightAvailable}
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier left)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps) controls baseline frontier right)
    (argument : RichGradedResult display.sourceEnv env U registry target display.node leftLocals
      (display.raw.comp commonLeft) leftAvailable input)
    (argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation))
    (certificate : RichCert display.sourceEnv env U registry target display.node.typeFormation.node rightLocals
      (display.raw.comp commonLeft) true support footprint)
    (resources : footprint.Available rightAvailable)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    Nonempty (WorldRecipeArgumentSelection (P := P) base caps display commonLeft commonRight
      controls baseline frontier input support) := by
  have localsEq : leftLocals = rightLocals :=
    leftData.generation.erase.capped.generated.locals_eq.trans
      rightData.generation.erase.capped.generated.locals_eq.symm
  cases localsEq
  exact ⟨{
    locals := leftLocals
    available := leftAvailable.append rightAvailable
    realization := ⟨left.frame.merge right.frame, left.substitutions⟩
    frameData := leftData.merge rightData
    argument := argument.availableMono (fun _ _ member => List.mem_append_left _ member)
    argumentReady := argumentReady
    codeFootprint := footprint
    certificate := certificate
    codeAvailable := fun index need member => List.mem_append_right _ (resources index need member)
    codeReady := ready }⟩

/-- Construct the common resource frame from the SAME independently returned
R and C witnesses. The type comparison itself is deliberately not invented
here: its returned code is retained, with exactly its original annotation. -/
theorem WorldRecipeArgumentSelection.ofReplies
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered)
    (argument : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight input
      (environmentCost baselineEnvironment))
    (argumentData : WorldGeneratedQueryReplyData (P := P) controls baseline frontier argument)
    (code : AmbientBoundedParameterReply base caps start display.formationDisplay commonLeft commonRight support
      (environmentCost baselineEnvironment))
    (codeData : WorldParameterReplyData (P := P) (display := display.formationDisplay) controls baseline frontier code)
    (sorted : support.HasType (.sort true)) :
    Nonempty (WorldRecipeArgumentSelection (P := P) base caps display commonLeft commonRight
      controls baseline frontier input support) := by
  obtain ⟨footprint, certificate, ready, resources, depth⟩ :=
    code.reply.answer.reply.query.code_controlled henv controls codeData.query sorted
  let left := argument.answer.reply.realization
  let right := code.reply.answer.reply.realization
  have leftData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := display) controls baseline frontier left := {
    generation := argumentData.generation
    replayable := argumentData.replayable
    controlled := argumentData.controlled
    compatible := argumentData.compatible
    hereditary := argumentData.hereditary
    closed := argument.answer.reply.closed
    capacity := argument.bounded controls.ordered
    covered := argumentData.covered }
  have rightData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := display) controls baseline frontier right := {
    generation := codeData.generation
    replayable := codeData.replayable
    controlled := codeData.controlled
    compatible := codeData.compatible
    hereditary := codeData.hereditary
    closed := code.reply.answer.reply.closed
    capacity := code.reply.bounded controls.ordered
    covered := codeData.covered }
  exact selectArgumentAndCode leftData rightData argument.answer.reply.query argumentData.query
    certificate resources ready

private theorem replaceRecipePair
    {count : Nat} {a b x y : World count}
    (first : WorldBelow count a x) (second : WorldBelow count b y)
    (frontier : List (World count)) :
    CallBelow count (frontier ++ [a,b]) (frontier ++ [x,y]) := by
  have head : CallBelow count [a,b] [x,b] :=
    .single (.head (tail := [b]) (replacement := [a]) (by
      intro node member
      cases List.mem_singleton.mp member
      exact first))
  have tail : CallBelow count [x,b] [x,y] :=
    (EquationWorldPolynomial.lower_mass (mass := [b]) (by
      intro node member
      cases List.mem_singleton.mp member
      exact second)).cons x
  have pair := head.trans tail
  induction frontier with
  | nil => exact pair
  | cons node rest ih => exact ih.cons node

private theorem prefixRecipeCall {count : Nat} {xs ys : List (World count)}
    (step : CallBelow count xs ys) (front : List (World count)) :
    CallBelow count (front ++ xs) (front ++ ys) := by
  induction front with
  | nil => exact step
  | cons head tail ih => exact ih.cons head

/-- The comparison is executed, not supplied as a type-alignment premise.
Its genuine C endpoints and the subsequent actual argument F are strictly
below the retained R pair. Independently selected resources are merged before
F; the requested argument is then converted at the comparison's exact support.
The source input is an actual assigned certificate, as in the C induction
clause. Producing that input from a particular capture remains the caller's
original head/history operation. -/
theorem transportRecipeArgument
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression declared}
    {right : OriginalNestedDisplay U common expression assigned}
    {n : Nat} {input support : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier parent : List (World strata.rules.length))
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := left)
      leftControls leftWorld frontier leftFrame)
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := right)
      rightControls rightWorld frontier rightFrame)
    (certificate : RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
      (left.raw.comp commonLeft) true support footprint)
    (resources : footprint.Available leftAvailable)
    (certificateReady : ControlledStoredQuery leftControls frontier (.certificate certificate))
    (typed : (input : Profile n).HasType support)
    (argument : AmbientBoundedGeneratedQueryReply base caps right commonLeft commonRight input
      (environmentCost rightEnvironment))
    (argumentData : WorldGeneratedQueryReplyData (P := P) rightControls rightWorld frontier argument)
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
        originalCallWorld rightControls .expressionReindex right.node rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent) :
    ∃ selected : WorldRecipeArgumentSelection (P := P) base caps right commonLeft commonRight
        rightControls rightWorld frontier input support,
      Related env U registry target (expression.subst commonLeft) (expression.subst commonRight)
        (declared.subst commonLeft) input support ∧
      env.IsDefEq U target (expression.subst commonLeft) (expression.subst commonRight)
        (declared.subst commonLeft) ∧
      (∃ rightArgument : RichGradedResult right.sourceEnv env U registry target right.node selected.locals
          (right.raw.comp commonRight) selected.available input,
        Nonempty (ControlledStoredQuery rightControls frontier (.observation rightArgument.observation))) ∧
      (∃ nextFootprint, ∃ nextCertificate : RichCert left.sourceEnv env U registry target
          left.node.typeFormation.node leftLocals (left.raw.comp commonRight) true support nextFootprint,
        nextFootprint.Available leftAvailable ∧
        Nonempty (ControlledStoredQuery leftControls frontier (.certificate nextCertificate))) := by
  have leftLower : WorldBelow strata.rules.length
      (originalCallWorld leftControls .assignedComparison left.node leftWorld)
      (originalCallWorld leftControls .expressionReindex left.node leftWorld) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have rightLower : WorldBelow strata.rules.length
      (originalCallWorld rightControls .assignedComparison right.node rightWorld)
      (originalCallWorld rightControls .expressionReindex right.node rightWorld) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have compareBelow := (replaceRecipePair leftLower rightLower frontier).trans smaller
  have compareSponsored : Sponsored frontier
      [originalCallWorld leftControls .assignedComparison left.node leftWorld,
       originalCallWorld rightControls .assignedComparison right.node rightWorld] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨sponsor, present, bound⟩ := sponsored _ List.mem_cons_self
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans leftLower bound⟩
    · cases List.mem_singleton.mp member
      obtain ⟨sponsor, present, bound⟩ := sponsored _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans rightLower bound⟩
  obtain ⟨code, ⟨codeData⟩⟩ := (bank _ compareBelow).assigned base caps left right commonLeft commonRight
    leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier rfl compareSponsored
    leftFrame leftData rightFrame rightData certificate resources certificateReady
  obtain ⟨selected⟩ := WorldRecipeArgumentSelection.ofReplies henv argument argumentData code codeData certificate.formed
  have fLower : WorldBelow strata.rules.length
      (originalCallWorld rightControls .fundamental right.node rightWorld)
      (originalCallWorld rightControls .expressionReindex right.node rightWorld) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have fBelow : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld rightControls .fundamental right.node rightWorld]) parent := by
    have drop : CallBelow strata.rules.length
        [originalCallWorld rightControls .fundamental right.node rightWorld]
        [originalCallWorld leftControls .assignedComparison left.node leftWorld,
         originalCallWorld rightControls .fundamental right.node rightWorld] :=
      .single (.head (replacement := []) (by intro node member; cases member))
    have pair := replaceRecipePair leftLower fLower ([] : List (World strata.rules.length))
    have step := drop.trans pair
    have lifted : CallBelow strata.rules.length
        (frontier ++ [originalCallWorld rightControls .fundamental right.node rightWorld])
        (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
          originalCallWorld rightControls .expressionReindex right.node rightWorld]) :=
      prefixRecipeCall step frontier
    exact lifted.trans smaller
  have fSponsored : Sponsored frontier [originalCallWorld rightControls .fundamental right.node rightWorld] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, bound⟩ := sponsored _ (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans fLower bound⟩
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated selected.realization.frame
    selected.frameData.generation selected.frameData.controlled
    selected.frameData.replayable selected.frameData.compatible selected.frameData.hereditary
  obtain ⟨answer, _, ⟨answerReady⟩⟩ := (unary _ fBelow).computational right.node right.provenance rightControls
    selected.realization.frame selected.frameData.generation.environment rightWorld frontier
    selected.frameData.capacity selected.frameData.covered rfl fSponsored frameData
    selected.frameData.closed formed selected.realization.substitutions selected.argument.observation
    selected.argument.resources selected.argumentReady
  have bridge := code.related.symm henv typed.wf_type
  have argumentCode := bridge.left_diagonal
  have rawRelated : Related env U registry target (expression.subst commonLeft) (expression.subst commonRight)
      (assigned.subst commonLeft) selected.argument.raw answer.support := by
    simpa only [← right.realizedExpression, ← right.realizedType] using answer.related
  have high := selected.argument.adapter.termMap henv hscoped formed
    (Profile.HasType.raise selected.argument.bound typed)
    (argumentCode.raise henv selected.argument.bound) rawRelated
  have paired : Related env U registry target (expression.subst commonLeft) (expression.subst commonRight)
      (assigned.subst commonLeft) input support := by
    simpa only [lower_raised, ← right.realizedExpression, ← right.realizedType] using
      Related.lower henv selected.argument.bound formed high
  have rawAtAssigned := (right.node.sound.defeq.mono frameData.ambient.below).substDF henv
    selected.realization.substitutions.wf formed selected.realization.substitutions
  have raw : env.IsDefEq U target (expression.subst commonLeft) (expression.subst commonRight)
      (assigned.subst commonLeft) := by
    simpa only [← right.realizedExpression, ← right.realizedType] using rawAtAssigned
  have formationLower : WorldBelow strata.rules.length
      (originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld)
      (originalCallWorld leftControls .expressionReindex left.node leftWorld) := by
    apply original_child
    have cost := left.node.typeFormation_dependency_cost_le leftControls.ordered leftEnvironment
    simp only [richSchedule, RichPhase.code]
    omega
  have formationBelow : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld]) parent := by
    have discard : CallBelow strata.rules.length
        [originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld]
        [originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld,
          originalCallWorld rightControls .expressionReindex right.node rightWorld] :=
      (EquationWorldPolynomial.lower_mass (mass := []) (world :=
        originalCallWorld rightControls .expressionReindex right.node rightWorld)
        (by intro node member; cases member)).cons _
    have lower : CallBelow strata.rules.length
        [originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld,
          originalCallWorld rightControls .expressionReindex right.node rightWorld]
        [originalCallWorld leftControls .expressionReindex left.node leftWorld,
          originalCallWorld rightControls .expressionReindex right.node rightWorld] :=
      .single (.head (replacement := [_]) (by
        intro node member
        cases List.mem_singleton.mp member
        exact formationLower))
    exact (prefixRecipeCall (discard.trans lower) frontier).trans smaller
  have formationSponsored : Sponsored frontier
      [originalCallWorld leftControls .fundamental left.node.typeFormation.node leftWorld] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, bound⟩ := sponsored _ List.mem_cons_self
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans formationLower bound⟩
  obtain ⟨sourceFrameData⟩ := WorldUnaryFrameData.ofGenerated leftFrame.frame leftData.generation leftData.controlled
    leftData.replayable leftData.compatible leftData.hereditary
  obtain ⟨sourceCode, _, ⟨sourceCodeReady⟩⟩ := (unary _ formationBelow).computational
    left.node.typeFormation.node left.formationDisplay.provenance leftControls leftFrame.frame
    leftData.generation.environment leftWorld frontier leftData.capacity leftData.covered
    rfl formationSponsored sourceFrameData leftData.closed formed leftFrame.substitutions
    (.code certificate) resources
    ⟨.code certificateReady.annotation, (by
      simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using certificateReady.within),
      certificateReady.sponsored⟩
  obtain ⟨nextFootprint, nextCertificate, nextReady, nextResources, _⟩ :=
    sourceCode.rightQuery.code_controlled henv leftControls sourceCodeReady certificate.formed
  exact ⟨selected, paired.convert henv typed bridge, code.path.symm.cast raw,
    ⟨answer.rightQuery.adaptRequest henv hscoped formed selected.argument.bound selected.argument.adapter,
      ⟨answerReady⟩⟩,
    ⟨nextFootprint, nextCertificate, nextResources, ⟨nextReady⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
