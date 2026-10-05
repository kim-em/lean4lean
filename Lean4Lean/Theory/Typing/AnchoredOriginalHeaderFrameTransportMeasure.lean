import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPairedFrame

/-! Changing the target world or taking a diagonal does not change the
original closures retained by a rich header frame. These equalities connect
future binder calls to the actual caller's well-founded measure. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

private theorem HeaderRichTail.steps_mpr
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : HeaderRichTail header field major env registry target context locals left right available =
      HeaderRichTail header field major env registry target context locals nextLeft nextRight nextAvailable)
    (tail : HeaderRichTail header field major env registry target context locals nextLeft nextRight nextAvailable) :
    (equal.mpr tail).steps = tail.steps := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

theorem HeaderRichTail.steps_leftDiagonal
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    tail.leftDiagonal.steps = tail.steps := by
  induction tail with
  | nil => simp only [leftDiagonal, HeaderRichTail.future, steps]
  | skip tail domain location lineage arguments ih =>
    simp only [leftDiagonal, steps, ih]
  | push tail domain location lineage owner answer arguments needs bounded covered ih =>
    simp only [leftDiagonal, steps, ih]

theorem HeaderRichTail.steps_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    (tail.future henv future).steps = tail.steps := by
  induction tail with
  | nil => simp only [leftDiagonal, HeaderRichTail.future, steps]
  | skip tail domain location lineage arguments ih =>
    simp only [HeaderRichTail.future]
    refine (steps_mpr ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future, lift'_subst]
    · simp only [subst_cons_future, lift'_subst]
    · simp only [Valuation.rename_push, List.map_nil]
    · simpa only [steps] using congrArg (List.cons _) ih
  | push tail domain location lineage owner answer arguments needs bounded covered ih =>
    simp only [HeaderRichTail.future]
    refine (steps_mpr ?_ ?_ ?_ _ _).trans ?_
    · simp only [subst_cons_future, lift'_subst]
    · simp only [subst_cons_future, lift'_subst]
    · simp only [Valuation.rename_push, List.map_nil]
    · simpa only [steps] using congrArg (List.cons _) ih

theorem HeaderRichTail.dependencyEnvironment_leftDiagonal
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    tail.leftDiagonal.dependencyEnvironment hf sf initial = tail.dependencyEnvironment hf sf initial := by
  simp only [dependencyEnvironment, dependencySteps, steps_leftDiagonal]

theorem HeaderRichTail.dependencyEnvironment_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    (tail.future henv future).dependencyEnvironment hf sf initial = tail.dependencyEnvironment hf sf initial := by
  simp only [dependencyEnvironment, dependencySteps, steps_future]

theorem HeaderBinderFrame.dependencyEnvironment_leftDiagonal
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    frame.leftDiagonal.dependencyEnvironment hf sf initial = frame.dependencyEnvironment hf sf initial := by
  induction frame with
  | captured tail => simpa only [leftDiagonal, dependencyEnvironment] using tail.dependencyEnvironment_leftDiagonal hf sf initial
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered ih =>
    simp only [leftDiagonal, dependencyEnvironment, ih]

private theorem HeaderBinderFrame.dependencyEnvironment_mpr
    (leftEq : left = nextLeft) (rightEq : right = nextRight) (availableEq : available = nextAvailable)
    (equal : HeaderBinderFrame header field major env registry target context locals left right available =
      HeaderBinderFrame header field major env registry target context locals nextLeft nextRight nextAvailable)
    (frame : HeaderBinderFrame header field major env registry target context locals nextLeft nextRight nextAvailable)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    (equal.mpr frame).dependencyEnvironment hf sf initial = frame.dependencyEnvironment hf sf initial := by
  cases leftEq
  cases rightEq
  cases availableEq
  rfl

theorem HeaderBinderFrame.dependencyEnvironment_future
    (henv : env.Ordered) (future : FutureInsertion env U target next ρ)
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    (frame.future henv future).dependencyEnvironment hf sf initial = frame.dependencyEnvironment hf sf initial := by
  induction frame with
  | captured tail => simpa only [HeaderBinderFrame.future, dependencyEnvironment] using tail.dependencyEnvironment_future henv future hf sf initial
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered ih =>
    simp only [HeaderBinderFrame.future]
    refine (dependencyEnvironment_mpr ?_ ?_ ?_ _ _ hf sf initial).trans ?_
    · simp only [subst_cons_future]
    · simp only [subst_cons_future]
    · simp only [Valuation.rename_push]
    · simpa only [dependencyEnvironment] using
        congrArg (fun previous => Closure.close (domain.dependencyOrigin hf) previous :: previous) ih

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
