import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedReplyMerge

/-! Remove a fresh original binder from an actual generated output frame.
Merged replies retain all parent branches and their exact resource suffix. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem generatedBinder_environmentCost (domain : Origin) (previous : List Closure) :
    environmentCost (.close domain previous :: previous) =
      domain.weight * (1 + environmentCost previous) := by
  have positive := domain.weight_pos
  have bound := Nat.mul_le_mul_right (1 + environmentCost previous) positive
  simp only [Nat.one_mul] at bound
  change max (domain.weight * (1 + environmentCost previous)) (environmentCost previous) = _
  exact Nat.max_eq_left (by omega)

theorem generatedBinder_max (weight a b : Nat) :
    max (weight * (1 + a)) (weight * (1 + b)) = weight * (1 + max a b) := by
  rcases Nat.le_total a b with h | h
  · have h' := Nat.mul_le_mul_left weight (Nat.add_le_add_left h 1)
    rw [Nat.max_eq_right h, Nat.max_eq_right h']
  · have h' := Nat.mul_le_mul_left weight (Nat.add_le_add_left h 1)
    rw [Nat.max_eq_left h, Nat.max_eq_left h']

theorem generatedBinder_cancel (domain : Origin) (output input : Nat)
    (bounded : domain.weight * (1 + output) ≤ domain.weight * (1 + input)) :
    output ≤ input := by
  have h := Nat.le_of_mul_le_mul_left bounded domain.weight_pos
  omega

structure GeneratedBinderParent
    (base : OriginalCaptureBase env U registry target)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (child : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      childLocals σ τ available)
    (commonLeft commonRight : Subst) where
  locals : List Nat
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ.tail τ.tail
    (fun index => available (index + 1))
  generated : ScopedCaptureGenerated base commonLeft.tail commonRight.tail graph frame.raw
  positions : Locals.push locals = childLocals
  environment : ∀ ordered : sourceEnv.Ordered,
    environmentCost (frame.dependencyEnvironment ordered) ≤ environmentCost (child.dependencyEnvironment ordered)
  domain_bound : ∀ ordered : sourceEnv.Ordered,
    (domain.dependencyOrigin ordered).weight * (1 + environmentCost (frame.dependencyEnvironment ordered)) ≤
      environmentCost (child.dependencyEnvironment ordered)

/-- A retained reservation keeps the actual parent and its full resources.
The domain-weighted parent remains bounded by the enlarged child ledger. -/
def GeneratedBinderParent.reserve
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {child : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      childLocals σ τ available}
    (parent : GeneratedBinderParent base graph child commonLeft commonRight)
    (closures : List Closure) :
    GeneratedBinderParent base graph (.reserve child closures) commonLeft commonRight where
  locals := parent.locals
  frame := parent.frame
  generated := parent.generated
  positions := parent.positions
  environment := by
    intro ordered
    change _ ≤ environmentCost (closures ++ child.dependencyEnvironment ordered)
    rw [merge_environmentCost_append]
    exact Nat.le_trans (parent.environment ordered) (Nat.le_max_right _ _)
  domain_bound := by
    intro ordered
    change _ ≤ environmentCost (closures ++ child.dependencyEnvironment ordered)
    rw [merge_environmentCost_append]
    exact Nat.le_trans (parent.domain_bound ordered) (Nat.le_max_right _ _)

private def peelBinderInvariant
    (base : OriginalCaptureBase env U registry target) (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph, frame with
  | .bind previous _ _ _, frame =>
    frame.Valid → Nonempty (GeneratedBinderParent base previous frame commonLeft commonRight)
  | _, _ => True

private theorem peelBinderInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : peelBinderInvariant base commonLeft commonRight graph left)
    (second : peelBinderInvariant base commonLeft commonRight graph right) :
    peelBinderInvariant base commonLeft commonRight graph (.merge left right) := by
  cases graph <;> try trivial
  intro valid
  simp only [RawOriginalRichFrame.Valid] at valid
  obtain ⟨a⟩ := first valid.1
  obtain ⟨b⟩ := second valid.2
  rcases a with ⟨leftLocals, leftFrame, leftGenerated, leftPositions, leftBound, leftDomainBound⟩
  rcases b with ⟨rightLocals, rightFrame, rightGenerated, rightPositions, rightBound, rightDomainBound⟩
  have same : leftLocals = rightLocals := leftGenerated.locals_eq.trans rightGenerated.locals_eq.symm
  cases same
  refine ⟨⟨leftLocals, leftFrame.merge rightFrame, .merge leftGenerated rightGenerated, leftPositions, ?_, ?_⟩⟩
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

private theorem ScopedCaptureGenerated.peelBinderInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph frame) :
    peelBinderInvariant base commonLeft commonRight graph frame := by
  induction generated with
  | merge _ _ first second => exact peelBinderInvariant_merge first second
  | original original => cases original <;> trivial
  | empty => trivial
  | tail => trivial
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered _ =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    exact ⟨⟨_, ⟨_, valid⟩, generated, rfl, fun _ => Nat.le_max_right _ _,
      fun _ => Nat.le_of_eq (generatedBinder_environmentCost _ _).symm⟩⟩
  | capture => trivial
  | group => trivial
  | scopedGroup => trivial
  | reserveCapture => trivial
  | reserveBind generated closures ih =>
    intro valid
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨parent⟩ := ih valid
    exact ⟨parent.reserve closures⟩
  | weaken => trivial

/-- The returned parent is reconstructed from the actual output frame,
including every merged branch. Its availability is exactly the old tail. -/
theorem ScopedCaptureGenerated.peelBinder
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      locals σ τ available}
    (generated : ScopedCaptureGenerated base commonLeft commonRight
      (.bind graph domain annotation displayed) frame)
    (valid : frame.Valid) :
    Nonempty (GeneratedBinderParent base graph frame commonLeft commonRight) :=
  generated.peelBinderInvariant valid

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
