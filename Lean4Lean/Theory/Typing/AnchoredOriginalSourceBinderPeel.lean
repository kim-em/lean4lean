import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBinderPeel
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureRealization

/-! Peeling an actual capped generated body preserves the parent's caps,
including the hidden owner frames of every merged reply. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

structure SourceGeneratedBinderParent
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (child : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      childLocals σ τ available)
    (commonLeft commonRight : Subst) where
  parent : GeneratedBinderParent base graph child commonLeft commonRight
  capped : SourceCaptureGenerated P base (fun index => commonCaps (index + 1))
    commonLeft.tail commonRight.tail graph parent.frame.raw

private def sourcePeelInvariant
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .bind previous _ _ _, frame =>
    frame.Valid → Nonempty (SourceGeneratedBinderParent P base commonCaps previous frame commonLeft commonRight)
  | _, _ => True

private theorem sourcePeelInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : sourcePeelInvariant P base commonCaps commonLeft commonRight graph left)
    (second : sourcePeelInvariant P base commonCaps commonLeft commonRight graph right) :
    sourcePeelInvariant P base commonCaps commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  intro valid
  simp only [RawOriginalRichFrame.Valid] at valid
  obtain ⟨⟨a, aCapped⟩⟩ := first valid.1
  obtain ⟨⟨b, bCapped⟩⟩ := second valid.2
  rcases a with ⟨leftLocals, leftFrame, leftGenerated, leftPositions, leftBound, leftDomainBound⟩
  rcases b with ⟨rightLocals, rightFrame, rightGenerated, rightPositions, rightBound, rightDomainBound⟩
  have same : leftLocals = rightLocals := leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases same
  refine ⟨⟨⟨leftLocals, leftFrame.merge rightFrame, .merge leftGenerated rightGenerated,
    leftPositions, ?_, ?_⟩, .merge aCapped bCapped⟩⟩
  · intro ordered
    rw [OriginalRichFrame.merge_environmentCost]
    change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
    rw [merge_environmentCost_append]
    exact Nat.max_le.mpr ⟨Nat.le_trans (leftBound ordered) (Nat.le_max_left _ _),
      Nat.le_trans (rightBound ordered) (Nat.le_max_right _ _)⟩
  · intro ordered
    rw [OriginalRichFrame.merge_environmentCost]
    change _ ≤ environmentCost (left.dependencyEnvironment ordered ++ right.dependencyEnvironment ordered)
    rw [merge_environmentCost_append, ← generatedBinder_max]
    exact Nat.max_le.mpr ⟨Nat.le_trans (leftDomainBound ordered) (Nat.le_max_left _ _),
      Nat.le_trans (rightDomainBound ordered) (Nat.le_max_right _ _)⟩

private theorem SourceCaptureGenerated.sourcePeelInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame) :
    sourcePeelInvariant P base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact sourcePeelInvariant_merge first second
  | identity => trivial
  | empty => trivial
  | tail => trivial
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered _ =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    exact ⟨⟨⟨_, ⟨_, valid⟩, generated.capped.generated, rfl, fun _ => Nat.le_max_right _ _,
      fun _ => Nat.le_of_eq (generatedBinder_environmentCost _ _).symm⟩, generated⟩⟩
  | reserveCapture => trivial
  | reserveBind generated closures ih =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨parent⟩ := ih valid
    exact ⟨⟨parent.parent.reserve closures, parent.capped⟩⟩
  | capture => trivial
  | historyGroup => trivial
  | weaken => trivial

/-- This retains the cap derivation of each actual parent branch, not merely
a pointwise bound on its visible resource table. -/
theorem SourceCaptureGenerated.peelBinder
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) frame)
    (valid : frame.Valid) :
    Nonempty (SourceGeneratedBinderParent P base commonCaps graph frame commonLeft commonRight) :=
  generated.sourcePeelInvariant valid

/-- An actual body's semantic substitution supplies the old tail substitution.
Generation reconstructs the parent's exact frame and caps through merges. -/
theorem OriginalCaptureRealization.peelSourceBinder
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    (child : OriginalCaptureRealization (.bind graph domain annotation displayed)
      env registry target locals commonLeft commonRight available)
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) child.frame.raw) :
    ∃ parentLocals, ∃ parent : OriginalCaptureRealization graph env registry target
        parentLocals commonLeft.tail commonRight.tail (fun index => available (index + 1)),
      SourceCaptureGenerated P base (fun index => commonCaps (index + 1))
        commonLeft.tail commonRight.tail graph parent.frame.raw ∧
      Locals.push parentLocals = locals ∧
      (∀ ordered : sourceEnv.Ordered,
        environmentCost (parent.frame.dependencyEnvironment ordered) ≤
          environmentCost (child.frame.dependencyEnvironment ordered)) ∧
      ∀ ordered : sourceEnv.Ordered,
        (domain.dependencyOrigin ordered).weight *
          (1 + environmentCost (parent.frame.dependencyEnvironment ordered)) ≤
            environmentCost (child.frame.dependencyEnvironment ordered) := by
  obtain ⟨⟨parent, capped⟩⟩ := generated.peelBinder child.frame.valid
  have substitutions : Ctx.SubstEq env U target
      (raw.lift.comp commonLeft).tail (raw.lift.comp commonRight).tail source := by
    cases child.substitutions with
    | cons tail _ _ => exact tail
  obtain ⟨result, resultCapped, environment⟩ := capped.realize parent.frame substitutions
  refine ⟨parent.locals, result, resultCapped, parent.positions, ?_, ?_⟩
  · intro ordered
    rw [environment ordered]
    exact parent.environment ordered
  · intro ordered
    rw [environment ordered]
    exact parent.domain_bound ordered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
