import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHead

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private noncomputable def headerMeasuredSuffix
    {capturedEnv : VEnv}
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (capturedOrdered : capturedEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target
      (.cons context domain) locals left right available) :
    { suffix : OriginalRichFrameSuffix (context := context) (env := env) (registry := registry)
        (target := target) domain locals left right available //
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost ≤
        environmentCost (frame.dependencyEnvironment ordered capturedOrdered initial) } := by
  cases frame with
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    exact ⟨⟨_, .header capturedOrdered initial tail, rfl⟩, fun _ => Nat.le_max_left _ _⟩
  | captured tail =>
    cases tail with
    | skip tail domain location lineage arguments =>
      refine ⟨⟨_, .header capturedOrdered initial (.captured tail), rfl⟩, ?_⟩
      intro ordered
      exact Nat.le_max_left _ _
    | push tail domain location lineage owner answer arguments needs bounded covered =>
      refine ⟨⟨_, .header capturedOrdered initial (.captured tail), rfl⟩, ?_⟩
      intro ordered
      simp only [HeaderBinderFrame.dependencyEnvironment, HeaderRichTail.dependencyEnvironment,
        HeaderRichTail.dependencySteps, HeaderRichTail.steps, List.map_cons,
        Dependency.headerCaptureEnvironment, Dependency.measureStep,
        Dependency.HeaderCaptureStep.argumentClosure, Option.map_some]
      split
      all_goals
        apply Nat.le_trans _ (Nat.le_max_left _ _)
        simp only [OriginalRichFrame.dependencyEnvironment, OriginalRichFrame.header,
          RawOriginalRichFrame.dependencyEnvironment, HeaderBinderFrame.dependencyEnvironment,
          HeaderRichTail.dependencyEnvironment, HeaderRichTail.dependencySteps, Dependency.measureLocated, EndpointState.dependencyOrigin, Closure.cost]
        omega

private theorem localsCast_environment
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    {otherLocals : List Nat} (same : locals = otherLocals) (ordered : sourceEnv.Ordered) :
    (same ▸ frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases same
  rfl

noncomputable def OriginalRichFrame.peelMeasuredData
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) :
    { suffix : OriginalRichFrameSuffix (context := context) (env := env) (registry := registry)
        (target := target) domain locals left right available //
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost ≤
        environmentCost (frame.dependencyEnvironment ordered) } := by
  rcases frame with ⟨raw, valid⟩
  match raw, valid with
  | .reserve frame closures, valid =>
    let inner : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ :=
      ⟨frame, by simpa only [RawOriginalRichFrame.Valid] using valid⟩
    obtain ⟨suffix, bound⟩ := inner.peelMeasuredData
    refine ⟨suffix, fun ordered => Nat.le_trans (bound ordered) ?_⟩
    change environmentCost (frame.dependencyEnvironment ordered) ≤
      environmentCost (closures ++ frame.dependencyEnvironment ordered)
    rw [merge_environmentCost_append]
    exact Nat.le_max_right _ _
  | .header ordered initial frame, _ => exact headerMeasuredSuffix ordered initial frame
  | .bind tail domain .., valid =>
    exact ⟨⟨_, ⟨tail, by simpa only [RawOriginalRichFrame.Valid] using valid⟩, rfl⟩,
      fun _ => Nat.le_max_left _ _⟩
  | .capture tail domain _ argument .., valid =>
    refine ⟨⟨_, ⟨tail, by simpa only [RawOriginalRichFrame.Valid] using valid⟩, rfl⟩, ?_⟩
    intro ordered
    apply Nat.le_trans _ (Nat.le_max_left _ _)
    simp only [Closure.cost, OriginalRichFrame.dependencyEnvironment]
    omega
  | .group tail domain _ _ entries, valid =>
    simp only [RawOriginalRichFrame.Valid] at valid
    exact ⟨⟨_, ⟨tail, valid.1⟩, rfl⟩, fun _ => Nat.le_max_left _ _⟩
  | .merge first second, valid =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨firstSuffix, firstBound⟩ := (OriginalRichFrame.mk first valid.1).peelMeasuredData
    obtain ⟨secondSuffix, secondBound⟩ := (OriginalRichFrame.mk second valid.2).peelMeasuredData
    have same : firstSuffix.tailLocals = secondSuffix.tailLocals :=
      (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
        (List.cons.inj (firstSuffix.positions.trans secondSuffix.positions.symm)).2
    let secondFrame := same.symm ▸ secondSuffix.frame
    refine ⟨⟨_, firstSuffix.frame.merge secondFrame, firstSuffix.positions⟩, ?_⟩
    intro ordered
    have castEnvironment : secondFrame.dependencyEnvironment ordered =
        secondSuffix.frame.dependencyEnvironment ordered := by
      exact localsCast_environment secondSuffix.frame same.symm ordered
    change _ ≤ environmentCost (first.dependencyEnvironment ordered ++ second.dependencyEnvironment ordered)
    rw [merge_environmentCost_append]
    simp only [OriginalRichFrame.merge_environmentCost, castEnvironment, Closure.cost]
    have firstLe := firstBound ordered
    have secondLe := secondBound ordered
    simp only [Closure.cost] at firstLe secondLe
    rcases Nat.le_total (environmentCost (firstSuffix.frame.dependencyEnvironment ordered))
      (environmentCost (secondSuffix.frame.dependencyEnvironment ordered)) with h | h
    · rw [Nat.max_eq_right h]
      exact Nat.le_trans secondLe (Nat.le_max_right _ _)
    · rw [Nat.max_eq_left h]
      exact Nat.le_trans firstLe (Nat.le_max_left _ _)
termination_by sizeOf frame.raw
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRichFrame.peelMeasured
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) :
    ∃ suffix : OriginalRichFrameSuffix (context := context) (env := env) (registry := registry)
        (target := target) domain locals left right available,
      ∀ ordered, (Closure.close (domain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost ≤
        environmentCost (frame.dependencyEnvironment ordered) :=
  ⟨frame.peelMeasuredData.val, frame.peelMeasuredData.property⟩

/-- A canonical full suffix, suitable for a source-graph tail constructor. -/
noncomputable def OriginalRichFrame.fullTail
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) :
    OriginalRichFrameSuffix (context := context) (env := env) (registry := registry)
      (target := target) domain locals left right available :=
  frame.peelMeasuredData.val

theorem OriginalRichFrame.fullTail_domain_bound
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) (ordered : sourceEnv.Ordered) :
    (Closure.close (domain.dependencyOrigin ordered)
      (frame.fullTail.frame.dependencyEnvironment ordered)).cost ≤
      environmentCost (frame.dependencyEnvironment ordered) :=
  frame.peelMeasuredData.property ordered

theorem OriginalRichFrame.fullTail_environment_le
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) (ordered : sourceEnv.Ordered) :
    environmentCost (frame.fullTail.frame.dependencyEnvironment ordered) ≤
      environmentCost (frame.dependencyEnvironment ordered) := by
  have bound := frame.fullTail_domain_bound ordered
  have positive := (domain.dependencyOrigin ordered).weight_pos
  have reserve := Nat.mul_le_mul_right
    (1 + environmentCost (frame.fullTail.frame.dependencyEnvironment ordered)) positive
  simp only [Closure.cost] at bound
  omega

def unpushLocals (locals : List Nat) : List Nat := locals.tail.map Nat.pred

@[simp] theorem unpushLocals_push (locals : List Nat) : unpushLocals (Locals.push locals) = locals := by
  simp [unpushLocals, Locals.push, List.map_map, Function.comp_def]

theorem OriginalRichFrame.fullTail_locals
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available) :
    frame.fullTail.tailLocals = unpushLocals locals := by
  exact (unpushLocals_push _).symm.trans (congrArg unpushLocals frame.fullTail.positions)


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
