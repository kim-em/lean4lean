import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBinderPeel
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHeadDepth

/-! Peeling an actual capped generated body preserves the parent's caps,
including the hidden owner frames of every merged reply. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

structure HeadSourceGeneratedBinderParent
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
  heads : ∀ policy, parent.frame.headDepth policy ≤ child.headDepth policy

private def headSourcePeelInvariant
    (P : VEnv → Prop) (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .bind previous _ _ _, frame =>
    frame.Valid → Nonempty (HeadSourceGeneratedBinderParent P base commonCaps previous frame commonLeft commonRight)
  | _, _ => True

private theorem headSourcePeelInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : headSourcePeelInvariant P base commonCaps commonLeft commonRight graph left)
    (second : headSourcePeelInvariant P base commonCaps commonLeft commonRight graph right) :
    headSourcePeelInvariant P base commonCaps commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  intro valid
  simp only [RawOriginalRichFrame.Valid] at valid
  obtain ⟨⟨a, aCapped, aHeads⟩⟩ := first valid.1
  obtain ⟨⟨b, bCapped, bHeads⟩⟩ := second valid.2
  rcases a with ⟨leftLocals, leftFrame, leftGenerated, leftPositions, leftBound, leftDomainBound⟩
  rcases b with ⟨rightLocals, rightFrame, rightGenerated, rightPositions, rightBound, rightDomainBound⟩
  have same : leftLocals = rightLocals := leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases same
  refine ⟨⟨⟨leftLocals, leftFrame.merge rightFrame, .merge leftGenerated rightGenerated,
    leftPositions, ?_, ?_⟩, .merge aCapped bCapped, ?_⟩⟩
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
  · intro policy
    rw [OriginalRichFrame.headDepth_merge]
    simp only [RawOriginalRichFrame.headDepth]
    exact Nat.max_le.mpr ⟨Nat.le_trans (aHeads policy) (Nat.le_max_left _ _),
      Nat.le_trans (bHeads policy) (Nat.le_max_right _ _)⟩

private theorem SourceCaptureGenerated.headSourcePeelInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame) :
    headSourcePeelInvariant P base commonCaps commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact headSourcePeelInvariant_merge first second
  | identity => trivial
  | empty => trivial
  | tail => trivial
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered _ =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    refine ⟨⟨⟨_, ⟨_, valid⟩, generated.capped.generated, rfl, fun _ => Nat.le_max_right _ _,
      fun _ => Nat.le_of_eq (generatedBinder_environmentCost _ _).symm⟩, generated, ?_⟩⟩
    intro policy
    simp only [OriginalRichFrame.headDepth, RawOriginalRichFrame.headDepth]
    exact Nat.le_max_right _ _
  | reserveCapture => trivial
  | reserveBind generated closures ih =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨parent⟩ := ih valid
    refine ⟨⟨parent.parent.reserve closures, parent.capped, ?_⟩⟩
    simpa only [GeneratedBinderParent.reserve, RawOriginalRichFrame.headDepth] using parent.heads
  | capture => trivial
  | historyGroup => trivial
  | weaken => trivial

/-- This retains the cap derivation of each actual parent branch, not merely
a pointwise bound on its visible resource table. -/
theorem SourceCaptureGenerated.peelHeadBinder
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
    Nonempty (HeadSourceGeneratedBinderParent P base commonCaps graph frame commonLeft commonRight) :=
  generated.headSourcePeelInvariant valid


/-- All caller masks are preserved by the SAME selected parent. No control
is separately re-queried and no mask-monotonicity premise is required. -/
theorem HeadSourceGeneratedBinderParent.stratifiedControls
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {child : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      childLocals σ τ available}
    (parent : HeadSourceGeneratedBinderParent P base commonCaps graph child commonLeft commonRight)
    (rank : Name → Nat)
    (bound : EquationStratifiedFuel.WithinAbove cutoff fuel
      (fun control => child.headDepth (stratifiedHeadPolicy rank control))) :
    EquationStratifiedFuel.WithinAbove cutoff fuel
      (fun control => parent.parent.frame.headDepth (stratifiedHeadPolicy rank control)) := by
  intro control above
  exact Nat.le_trans (parent.heads _) (bound control above)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
