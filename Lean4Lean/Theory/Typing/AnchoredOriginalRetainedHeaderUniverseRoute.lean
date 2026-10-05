import Lean4Lean.Theory.Typing.AnchoredOriginalClosedTypeRouteData
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteSources

/-! Equivalent universe seeds are connected by an actual original equality
in the retained declaration's earlier source. The terminal endpoint is the
exact header retained by the query, rather than a newly selected declaration
or a normalized replacement. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace RetainedHeaderUniverse

variable {U : Nat} {levels leftLevels rightLevels : List VLevel} {P : VEnv → Prop}

private theorem equality_wellFormed
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (initial : List Closure) :
    (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph original forward ordered below initial).WellFormed := by
  rw [RawGeneratedTypeRoute.WellFormed.eq_def]
  trivial

private theorem equality_frames
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (initial : List Closure) :
    (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph original forward ordered below initial).frames = [] := by
  rw [RawGeneratedTypeRoute.frames.eq_def]

private theorem equality_reserve
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (initial : List Closure) :
    (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph original forward ordered below initial).reserve =
        [.close (original.dependencyOrigin ordered) initial] := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem sameExpression_sources
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (same : leftExpression = rightExpression)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftSource : P left.sourceEnv) (rightSource : P right.sourceEnv) :
    (RawGeneratedTypeRoute.sameExpression left right same lf rf initial frame).AllSources P := by
  cases same
  rw [RawGeneratedTypeRoute.sameExpression, RawGeneratedTypeRoute.AllSources.eq_def]
  exact ⟨leftSource, rightSource, trivial⟩

private theorem generated_trans
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
    {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
    (firstGenerated : first.Generated base caps) (secondGenerated : second.Generated base caps) :
    (first.trans second).Generated base caps := by
  refine ⟨?_, ?_⟩
  · rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨firstGenerated.wellFormed, secondGenerated.wellFormed⟩
  · intro boxed member
    rw [RawGeneratedTypeRoute.frames.eq_def] at member
    exact (List.mem_append.mp member).elim (firstGenerated.frames boxed) (secondGenerated.frames boxed)

private theorem trans_reserve
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
    (first.trans second).reserve = first.reserve ++ second.reserve := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

/-- The original proof is rebuilt only for universe equivalence, using the
retained declaration's own actual formation and its earlier Ordered source. -/
noncomputable def original
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    Derivation origin.source U [] (info.type.instL leftLevels) (info.type.instL rightLevels)
      (.sort (origin.familyHeader leftWF).level) := by
  have typed := (origin.familyHeader leftWF).reference.sound
  have context : origin.source.CtxStrong U [] := by trivial
  have changed := EqUpToLevels.defeq origin.ordered origin.ordered.strong context typed
    (EqUpToLevels.refl context.levelWF typed).1
    (EqUpToLevels.instL_expr info.type leftWF rightWF equivalent)
  exact Classical.choice (Derivation.reify changed)

noncomputable def display
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (common : List VExpr) :
    OriginalNestedDisplay U common (info.type.instL levels)
      (.sort (origin.familyHeader levelsWF).level) where
  sourceEnv := origin.source
  source := []
  sourceExpression := info.type.instL levels
  sourceType := .sort (origin.familyHeader levelsWF).level
  context := .nil
  node := .ref (origin.familyHeader levelsWF).reference
  provenance := .ofLocation .here .nil
  raw := .id
  graph := .empty common
  expression_eq := subst_id.symm
  type_eq := subst_id.symm

noncomputable def frame
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (left right : Subst) :
    OriginalTypeRouteFrame env registry target (display origin levelsWF common).graph left right :=
  closedTypeRouteFrame .nil common env registry target left right

/-- R into the original universe equality, that equality itself, and R out
to the retained header. All three roots and both empty baselines are data. -/
noncomputable def route
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (rightBelow : rightEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    RawGeneratedTypeRoute env registry target left right
      (display leftOrigin leftWF common) (display rightOrigin rightWF common) [] [] :=
  let equality := original rightOrigin leftWF rightWF equivalent
  let graph := closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common
  let equalityFrame := closedTypeRouteFrame .nil common env registry target left right
  .trans
    (.sameExpression (display leftOrigin leftWF common) (graph.typeEqualityDisplay equality true)
      subst_id.symm leftOrigin.ordered rightOrigin.ordered [] equalityFrame)
    (.trans
      (.equality graph equality true rightOrigin.ordered (rightOrigin.sourceBelow.trans rightBelow) [])
      (.sameExpression (graph.typeEqualityDisplay equality false) (display rightOrigin rightWF common)
        subst_id rightOrigin.ordered rightOrigin.ordered []
        (frame rightOrigin rightWF common env registry target left right)))

theorem route_generated
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (rightBelow : rightEnv ≤ env) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) (left right : Subst) :
    (route leftOrigin rightOrigin leftWF rightWF equivalent rightBelow common registry target left right).Generated
      base caps := by
  let equality := original rightOrigin leftWF rightWF equivalent
  let graph := closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common
  have first := RawGeneratedTypeRoute.sameExpression_generated
    (display leftOrigin leftWF common) (graph.typeEqualityDisplay equality true)
    subst_id.symm leftOrigin.ordered rightOrigin.ordered []
    (closedTypeRouteFrame .nil common env registry target left right)
    (closedTypeRouteFrame_capped .nil common caps left right (base := base))
  have last := RawGeneratedTypeRoute.sameExpression_generated
    (graph.typeEqualityDisplay equality false) (display rightOrigin rightWF common)
    subst_id rightOrigin.ordered rightOrigin.ordered []
    (frame rightOrigin rightWF common env registry target left right)
    (closedTypeRouteFrame_capped .nil common caps left right (base := base))
  have middle : (RawGeneratedTypeRoute.equality (registry := registry) (target := target)
      (commonLeft := left) (commonRight := right) graph equality true rightOrigin.ordered
      (rightOrigin.sourceBelow.trans rightBelow) []).Generated base caps := by
    refine ⟨equality_wellFormed _ _ _ _ _ _, ?_⟩
    intro boxed member
    rw [equality_frames] at member
    cases member
  exact generated_trans first (generated_trans middle last)

theorem route_reserve
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (rightBelow : rightEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    let fromHeader := Closure.close ((display leftOrigin leftWF common).node.dependencyOrigin leftOrigin.ordered) []
    let universeClosure := Closure.close ((original rightOrigin leftWF rightWF equivalent).dependencyOrigin rightOrigin.ordered) []
    let toHeader := Closure.close ((display rightOrigin rightWF common).node.dependencyOrigin rightOrigin.ordered) []
    (route leftOrigin rightOrigin leftWF rightWF equivalent rightBelow common registry target left right).reserve =
      [.bundle fromHeader universeClosure, universeClosure, .bundle universeClosure toHeader] := by
  dsimp only
  let equality := original rightOrigin leftWF rightWF equivalent
  let graph := closedCaptureGraph (ContextDerivation.nil (env := rightOrigin.source) (U := U)) common
  have eqReserve := equality_reserve (registry := registry) (target := target)
    (left := left) (right := right) graph equality true rightOrigin.ordered
    (rightOrigin.sourceBelow.trans rightBelow) []
  have lastReserve := RawGeneratedTypeRoute.sameExpression_reserve
    (graph.typeEqualityDisplay equality false) (display rightOrigin rightWF common)
    subst_id rightOrigin.ordered rightOrigin.ordered []
    (frame rightOrigin rightWF common env registry target left right)
  rw [route, trans_reserve, trans_reserve]
  rw [RawGeneratedTypeRoute.sameExpression_reserve, eqReserve, lastReserve]
  simp only [frame, closedTypeRouteFrame_environment, OriginalCaptureMap.typeEqualityDisplay,
    originalTypeRouteSide, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin,
    List.cons_append, List.nil_append]
  rfl

theorem route_sources
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (rightBelow : rightEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst)
    (leftSource : P leftOrigin.source) (rightSource : P rightOrigin.source) :
    (route leftOrigin rightOrigin leftWF rightWF equivalent rightBelow common registry target left right).AllSources P := by
  simp only [route, RawGeneratedTypeRoute.AllSources]
  constructor
  · exact leftSource
  constructor
  · exact rightSource
  constructor
  · exact sameExpression_sources _ _ _ _ _ _ _ leftSource rightSource
  refine ⟨rightSource, rightSource, ⟨rightSource, rightSource, trivial⟩, ?_⟩
  exact sameExpression_sources _ _ _ _ _ _ _ rightSource rightSource

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
