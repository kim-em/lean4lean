import Lean4Lean.Theory.Typing.CanonicalDataHeadSubstitution
import Lean4Lean.Theory.Typing.CanonicalDataHeadTrace
import Lean4Lean.Theory.Typing.CanonicalTraceSubstitution

/-! Exact substitution of successful data-head traces. Structure dispatch
uses projections uniformly, so substitution cannot switch a terminal Pi's
field syntax from projections to constructor arguments. -/
namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem run_exists_of_length
    {indices indices' : List VExpr} {instructions : List CaptureInstruction}
    {state final : SaturatedCaptureState}
    (run : state.run indices instructions = some final)
    (same : indices'.length = indices.length) (state' : SaturatedCaptureState) :
    ∃ final', state'.run indices' instructions = some final' := by
  induction instructions generalizing state state' with
  | nil => exact ⟨state', rfl⟩
  | cons instruction rest ih =>
    simp only [SaturatedCaptureState.run, bind, Option.bind_eq_some_iff] at run ⊢
    obtain ⟨next, step, tail⟩ := run
    cases instruction with
    | proof domain =>
      let next' : SaturatedCaptureState := {
        added := instantiateParams domain state'.captures :: state'.added
        captures := state'.captures.map (·.lift) ++ [.bvar 0] }
      obtain ⟨final', tail'⟩ := ih tail next'
      exact ⟨final', next', rfl, tail'⟩
    | index domain slot =>
      simp only [SaturatedCaptureState.step, bind, Option.bind_eq_some_iff] at step
      obtain ⟨value, found, _⟩ := step
      have bound : slot < indices'.length := by
        rw [same]
        exact (List.getElem?_eq_some_iff.mp found).choose
      have found' : indices'[slot]? = some indices'[slot] := List.getElem?_eq_getElem bound
      let next' : SaturatedCaptureState := {
        added := state'.added
        captures := state'.captures ++ [indices'[slot].liftN state'.added.length] }
      obtain ⟨final', tail'⟩ := ih tail next'
      exact ⟨final', next', by simp only [SaturatedCaptureState.step, found', Option.bind_some]; rfl, tail'⟩

private theorem program_exists_of_length
    {data : NativeRecursorData} {levels : List VLevel} {arguments arguments' : List VExpr}
    {program : SaturatedProgram data}
    (run : data.saturatedProgram levels arguments = some program)
    (same : arguments'.length = arguments.length) :
    ∃ program', data.saturatedProgram levels arguments' = some program' := by
  unfold saturatedProgram at run
  dsimp only at run
  split at run <;> try contradiction
  rename_i levelsValid
  simp only [bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨prefixArgs, trailing⟩, splitArgs, major, foundMajor, source, foundSource, run⟩ := run
  split at run <;> try contradiction
  rename_i sourceCounts
  simp only [Option.bind_eq_some_iff] at run
  obtain ⟨equation, foundEquation, body, foundBody, run⟩ := run
  split at run <;> try contradiction
  rename_i domainCount
  split at run <;> try contradiction
  rename_i headShape
  simp only [Option.bind_eq_some_iff] at run
  obtain ⟨state, run, result⟩ := run
  have prefixLength := (splitSaturated_spec splitArgs).1
  have enough : data.majorOffset + 1 ≤ arguments'.length := by
    have decomposition := congrArg List.length (splitSaturated_spec splitArgs).2.1
    simp only [List.length_append] at decomposition
    omega
  let prefix' := arguments'.take (data.majorOffset + 1)
  have prefixLength' : prefix'.length = data.majorOffset + 1 := by
    simp only [prefix', List.length_take, Nat.min_eq_left enough]
  have majorBound : data.majorOffset < prefix'.length := by omega
  have majorFound : prefix'[data.majorOffset]? = some prefix'[data.majorOffset] :=
    List.getElem?_eq_getElem majorBound
  obtain ⟨state', run'⟩ := run_exists_of_length run
    (indices' := (prefix'.drop data.indexOffset).take data.numIndices)
    (by simp only [List.length_take, List.length_drop, prefixLength, prefixLength'])
    { added := [], captures := prefix'.take data.indexOffset }
  dsimp only [prefix'] at majorFound run'
  refine ⟨⟨levels, prefix', arguments'.drop (data.majorOffset + 1), prefix'[data.majorOffset],
    source, equation, body, fieldInstructions source ((body.domains.drop data.indexOffset).map (·.instL levels)), state'⟩, ?_⟩
  simp only [saturatedProgram, levelsValid, splitSaturated, enough, ↓reduceIte,
    bind, Option.bind_some]
  simp only [majorFound, foundSource, sourceCounts, foundEquation, foundBody, domainCount, headShape,
    run', bind, Option.bind_some, Bool.false_eq_true, if_false, ↓reduceIte, pure, Option.pure_def]
  rfl

private def Rigid (expression : VExpr) : Prop :=
  ∀ index, expression.getAppFnArgs.1 ≠ .bvar index

private theorem spine_subst (rigid : Rigid expression) (σ : Subst) :
    (expression.subst σ).getAppFnArgs =
      (expression.getAppFnArgs.1.subst σ, expression.getAppFnArgs.2.map (·.subst σ)) := by
  induction expression with
  | bvar i => exact False.elim (rigid i rfl)
  | app fn arg ih _ =>
    have child : Rigid fn := by simpa only [Rigid, getAppFnArgs_app] using rigid
    simp only [subst, getAppFnArgs_app, ih child, List.map_append, List.map_singleton]
  | _ => rfl

private theorem step_bvarSpine (head : expression.getAppFnArgs.1 = .bvar index) :
    step registry expression = none := by
  induction expression with
  | app fn arg ih _ =>
    have child : fn.getAppFnArgs.1 = .bvar index := by simpa only [getAppFnArgs_app] using head
    rw [step]
    have legacy : CanonicalHead.step registry.toRegistry (.app fn arg) = none := by
      simp only [CanonicalHead.step, getAppFnArgs_app, child, CanonicalHead.spineStep]
    have selection : select registry fn = none := by
      unfold select
      cases spine : fn.getAppFnArgs with
      | mk head args =>
        have same : head = .bvar index := by simpa only [spine] using child
        rw [same]
    rw [legacy, selection, ih child]
    rfl
  | bvar => simp only [step, CanonicalHead.step, CanonicalHead.spineStep, getAppFnArgs, getAppFnArgs.go]
  | _ => cases head

private theorem rigid_of_step (selected : step registry expression = some out) : Rigid expression := by
  intro index head
  rw [step_bvarSpine head] at selected
  contradiction

private theorem select_subst_exact (rigid : Rigid expression) (σ : Subst) :
    select registry (expression.subst σ) = (select registry expression).map (·.subst σ) := by
  unfold select
  rw [spine_subst rigid]
  cases spine : expression.getAppFnArgs with
  | mk head arguments =>
    cases head <;> simp only [subst] <;> try rfl
    case bvar index => exact False.elim (rigid index (congrArg Prod.fst spine))
    case const name levels =>
      cases lookup : registry.natives name with
      | none => simp only; split <;> rfl
      | some data => simp only; split <;> rfl
    case elim block owner levels =>
      cases lookup : registry.cases block owner with
      | none => rfl
      | some entry => simp only; split <;> rfl

private theorem program_none_subst {data : NativeRecursorData} {levels : List VLevel}
    (absent : data.saturatedProgram levels arguments = none) (σ : Subst) :
    data.saturatedProgram levels (arguments.map (·.subst σ)) = none := by
  cases changed : data.saturatedProgram levels (arguments.map (·.subst σ)) with
  | none => rfl
  | some program =>
    obtain ⟨original, successful⟩ := program_exists_of_length changed (List.length_map _).symm
    rw [absent] at successful
    contradiction

private theorem legacy_none_subst (rigid : Rigid expression)
    (absent : CanonicalHead.step registry expression = none) (σ : Subst) :
    CanonicalHead.step registry (expression.subst σ) = none := by
  unfold CanonicalHead.step at absent ⊢
  rw [spine_subst rigid]
  cases spine : expression.getAppFnArgs with
  | mk head arguments =>
    rw [spine] at absent
    cases head <;> simp only [subst, CanonicalHead.spineStep] at absent ⊢ <;> try rfl
    case bvar index => exact False.elim (rigid index (congrArg Prod.fst spine))
    case lam A body =>
      cases arguments with
      | nil => rfl
      | cons => cases absent
    case const name levels =>
      cases lookup : registry.definitions name with
      | some value => simp only [lookup] at absent ⊢; split at absent <;> simp_all
      | none =>
        simp only [lookup] at absent ⊢
        cases native : registry.natives name with
        | none => rfl
        | some data =>
          simp only [native] at absent ⊢
          split at absent
          · rename_i same
            rw [if_pos same]
            unfold CanonicalHead.nativeOutput at absent ⊢
            rw [program_none_subst (Option.map_eq_none_iff.mp absent) σ]
            rfl
          · rename_i different
            rw [if_neg different]

private theorem run_subst_exact {rule : Rule} (rigid : Rigid major) (closed : rule.equation.rhs.Closed)
    (selected : Selected) (σ : Subst) :
    rule.run (selected.subst σ) (major.subst σ) = (rule.run selected major).map (·.subst σ) := by
  unfold Rule.run
  rw [spine_subst rigid]
  cases spine : major.getAppFnArgs with
  | mk head arguments =>
    cases head <;> simp only [subst] <;> try rfl
    case bvar index => exact False.elim (rigid index (congrArg Prod.fst spine))
    case const name levels =>
      simp only [Selected.subst, List.length_map]
      split
      · simp only [Option.map_some, subst_mkApps,
          (closed.instL (ls := selected.levels)).subst_eq Subst.Fixes.zero,
          Rule.captures, List.map_append, List.map_take, List.map_drop, List.length_map]
      · rfl

private theorem direct_subst_exact (rigid : Rigid major) (selected : Selected)
    (closed : ∀ rule ∈ selected.rules, rule.equation.rhs.Closed) (σ : Subst) :
    directIota (selected.subst σ) (major.subst σ) = (directIota selected major).map (·.subst σ) := by
  have mapped : ∀ rules : List Rule, (∀ rule ∈ rules, rule.equation.rhs.Closed) →
      rules.findSome? (fun rule => rule.run (selected.subst σ) (major.subst σ)) =
        (rules.findSome? (fun rule => rule.run selected major)).map (·.subst σ) := by
    intro rules scopes
    induction rules with
    | nil => rfl
    | cons rule rest ih =>
      simp only [List.findSome?]
      rw [run_subst_exact rigid (scopes rule List.mem_cons_self)]
      cases rule.run selected major with
      | some result => rfl
      | none => exact ih (fun r hr => scopes r (List.mem_cons_of_mem _ hr))
  exact mapped selected.rules closed

private theorem project_subst_exact (rigid : Rigid major) (σ : Subst) :
    project registry typeName index (major.subst σ) = (project registry typeName index major).map (·.subst σ) := by
  unfold project
  cases lookup : registry.projections typeName with
  | none => rfl
  | some info =>
    simp only [bind, Option.bind_some]
    rw [spine_subst rigid]
    cases spine : major.getAppFnArgs with
    | mk head arguments =>
      cases head <;> simp only [subst] <;> try rfl
      case bvar index => exact False.elim (rigid index (congrArg Prod.fst spine))
      case const name levels =>
        split
        · exact List.getElem?_map ..
        · rfl

private theorem appFunction_subst (out : CanonicalHead.Output) (argument : VExpr) (σ : Subst) :
    appFunction (out.subst σ) (argument.subst σ) = (appFunction out argument).subst σ := by
  simp only [appFunction, CanonicalHead.Output.subst, subst, substAdded_length]
  congr 2
  simpa only [← lift'_consN_skipN (k := 0), Lift.consN] using (liftN_subst_liftN argument σ out.added.length).symm

private theorem appMajor_subst (function : VExpr) (out : CanonicalHead.Output) (σ : Subst) :
    appMajor (function.subst σ) (out.subst σ) = (appMajor function out).subst σ := by
  simp only [appMajor, CanonicalHead.Output.subst, subst, substAdded_length]
  congr 2
  simpa only [← lift'_consN_skipN (k := 0), Lift.consN] using (liftN_subst_liftN function σ out.added.length).symm


/-- Exact naturality of a successful data step. Failure is used only at rigid
heads or alongside a successful child, never reflected for arbitrary terms. -/
theorem step_subst (hscope : registry.Scoped)
    (selected : step registry expression = some out) (σ : Subst) :
    step registry (expression.subst σ) = some (out.subst σ) := by
  induction expression generalizing out with
  | app function argument functionIH argumentIH =>
    have rigid := rigid_of_step selected
    rw [step] at selected
    change step registry (.app (function.subst σ) (argument.subst σ)) = _
    rw [step]
    cases old : CanonicalHead.step registry.toRegistry (.app function argument) with
    | some oldOut =>
      simp only [old] at selected
      cases selected
      rw [show CanonicalHead.step registry.toRegistry (.app (function.subst σ) (argument.subst σ)) =
        some (out.subst σ) from CanonicalHead.step_subst hscope.base old σ]
    | none =>
      rw [show CanonicalHead.step registry.toRegistry (.app (function.subst σ) (argument.subst σ)) = none from
        legacy_none_subst rigid old σ]
      simp only [old] at selected
      cases selection : select registry function with
      | none =>
        simp only [selection] at selected
        obtain ⟨child, stepChild, rfl⟩ := Option.map_eq_some_iff.mp selected
        rw [select_subst_exact (rigid_of_step stepChild) σ, selection]
        simp only [Option.map_none]
        rw [functionIH stepChild]
        exact congrArg some (appFunction_subst child argument σ)
      | some chosen =>
        rw [select_subst selection σ]
        dsimp only
        simp only [selection] at selected
        have isMajor : (chosen.subst σ).isMajor = chosen.isMajor := by
          simp only [Selected.isMajor, Selected.subst, List.length_map]
        rw [isMajor]
        cases isMajorCase : chosen.isMajor with
        | false =>
          simp only [isMajorCase, Bool.false_eq_true, ↓reduceIte] at selected ⊢
          obtain ⟨child, stepChild, rfl⟩ := Option.map_eq_some_iff.mp selected
          rw [functionIH stepChild]
          exact congrArg some (appFunction_subst child argument σ)
        | true =>
          simp only [isMajorCase, ↓reduceIte] at selected ⊢
          rw [etaIota_subst registry chosen (hscope.rule _ _ selection)]
          cases etaReduction : etaIota registry chosen argument with
          | some result =>
            simp only [etaReduction] at selected
            cases selected
            rfl
          | none =>
            simp only [etaReduction, Option.map_none] at selected ⊢
            cases direct : directIota chosen argument with
            | some result =>
              rw [directIota_subst chosen (hscope.rule _ _ selection) direct σ]
              simp only [direct] at selected
              cases selected
              rfl
            | none =>
              simp only [direct] at selected
              obtain ⟨child, stepChild, rfl⟩ := Option.map_eq_some_iff.mp selected
              rw [direct_subst_exact (rigid_of_step stepChild) chosen (hscope.rule _ _ selection), direct]
              simp only [Option.map_none]
              rw [argumentIH stepChild]
              exact congrArg some (appMajor_subst function child σ)
  | proj typeName index major majorIH =>
    have rigid := rigid_of_step selected
    rw [step] at selected
    change step registry (.proj typeName index (major.subst σ)) = _
    rw [step]
    cases old : CanonicalHead.step registry.toRegistry (.proj typeName index major) with
    | some oldOut =>
      simp only [old] at selected
      cases selected
      rw [show CanonicalHead.step registry.toRegistry (.proj typeName index (major.subst σ)) =
        some (out.subst σ) from CanonicalHead.step_subst hscope.base old σ]
    | none =>
      rw [show CanonicalHead.step registry.toRegistry (.proj typeName index (major.subst σ)) = none from
        legacy_none_subst rigid old σ]
      simp only [old] at selected
      cases projection : project registry typeName index major with
      | some result =>
        rw [project_subst projection σ]
        simp only [projection] at selected
        cases selected
        rfl
      | none =>
        simp only [projection] at selected
        obtain ⟨child, stepChild, rfl⟩ := Option.map_eq_some_iff.mp selected
        rw [project_subst_exact (rigid_of_step stepChild) σ, projection]
        simp only [Option.map_none]
        rw [majorIH stepChild]
        rfl
  | const name levels =>
    have old : CanonicalHead.step registry.toRegistry (.const name levels) = some out := by
      cases equation : CanonicalHead.step registry.toRegistry (.const name levels) with
      | none => simp only [step, equation] at selected; contradiction
      | some oldOut =>
        simp only [step, equation] at selected
        exact selected
    have changed : CanonicalHead.step registry.toRegistry (.const name levels) = some (out.subst σ) := by
      simpa only [subst] using CanonicalHead.step_subst hscope.base old σ
    simp only [subst, step, changed]
  | _ =>
    simp only [step, CanonicalHead.step, CanonicalHead.spineStep,
      getAppFnArgs, getAppFnArgs.go] at selected
    contradiction

private theorem liftN_add (σ : Subst) (a b : Nat) :
    (σ.liftN a).liftN b = σ.liftN (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Subst.liftN, ih]; rfl

/-- Full successful trace substitution, preserving the exact final Pi/sort/
constructor syntax and all freshly generated proof domains. -/
theorem Trace.subst (hscope : registry.Scoped)
    (trace : Trace registry expression added result) (σ : Subst) :
    Trace registry (expression.subst σ) (substAdded σ added)
      (result.subst (σ.liftN added.length)) := by
  induction trace generalizing σ with
  | refl => exact .refl
  | @next expression out added result selected tail ih =>
    have next := Trace.next (step_subst hscope selected σ) (ih (σ.liftN out.added.length))
    simpa only [CanonicalHead.Output.subst, CanonicalHead.substAdded_append,
      List.length_append, liftN_add, Nat.add_comm out.added.length added.length] using next


end Lean4Lean.CanonicalDataHead
