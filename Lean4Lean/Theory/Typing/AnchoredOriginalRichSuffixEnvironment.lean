import Lean4Lean.Theory.Typing.AnchoredOriginalRichFramePeelMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The actual closure ledger after removing a fixed number of source slots.
This includes all branches of a merge, even if no current need uses them. -/
noncomputable def OriginalRichFrame.suffixEnvironment
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (ordered : sourceEnv.Ordered) (depth : Nat) : List Closure :=
  match depth, context with
  | 0, _ => frame.dependencyEnvironment ordered
  | _ + 1, .nil => []
  | depth + 1, .cons _ _ => frame.fullTail.frame.suffixEnvironment ordered depth
termination_by depth

@[simp] theorem OriginalRichFrame.suffixEnvironment_zero
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (ordered : sourceEnv.Ordered) :
    frame.suffixEnvironment ordered 0 = frame.dependencyEnvironment ordered := by simp only [suffixEnvironment]

theorem OriginalRichFrame.suffixEnvironment_tail
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (frame : OriginalRichFrame sourceEnv env U registry target (.cons context domain) locals left right available)
    (ordered : sourceEnv.Ordered) (depth : Nat) :
    frame.fullTail.frame.suffixEnvironment ordered depth = frame.suffixEnvironment ordered (depth + 1) := by simp only [suffixEnvironment]

private theorem suffixEnvironment_castLocals
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    {otherLocals : List Nat} (same : locals = otherLocals) (ordered : sourceEnv.Ordered) (depth : Nat) :
    (same ▸ frame).suffixEnvironment ordered depth = frame.suffixEnvironment ordered depth := by
  cases same
  rfl

theorem OriginalRichFrame.suffixEnvironment_merge
    {context : ContextDerivation sourceEnv U source}
    (first : OriginalRichFrame sourceEnv env U registry target context locals left right firstAvailable)
    (second : OriginalRichFrame sourceEnv env U registry target context locals left right secondAvailable)
    (ordered : sourceEnv.Ordered) (depth : Nat) :
    (first.merge second).suffixEnvironment ordered depth =
      first.suffixEnvironment ordered depth ++ second.suffixEnvironment ordered depth := by
  induction depth generalizing source locals left right firstAvailable secondAvailable with
  | zero => simp only [suffixEnvironment_zero, merge_environment]
  | succ depth ih =>
    cases context with
    | nil => simp only [suffixEnvironment, List.nil_append]
    | cons context domain =>
      cases first with | mk first firstValid =>
      cases second with | mk second secondValid =>
      simp only [suffixEnvironment]
      simp only [OriginalRichFrame.fullTail, OriginalRichFrame.merge]
      rw [OriginalRichFrame.peelMeasuredData]
      rw [ih, suffixEnvironment_castLocals]

theorem OriginalRichFrame.suffixEnvironment_bind
    {context : ContextDerivation sourceEnv U source}
    (tail : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals left true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst left) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (ordered : sourceEnv.Ordered) (depth : Nat) :
    (tail.bind domain certificate resources typed arguments needs bounded covered).suffixEnvironment ordered (depth+1) =
      tail.suffixEnvironment ordered depth := by
  cases tail
  simp only [suffixEnvironment, bind, fullTail]
  rw [peelMeasuredData]
  rfl

theorem OriginalRichFrame.suffixEnvironment_capture
    {context : ContextDerivation sourceEnv U source}
    (tail : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A) (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals left (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals left true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst left) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (ordered : sourceEnv.Ordered) (depth : Nat) :
    (tail.capture domain initial argument location lineage query queryAvailable certificate resources typed arguments
      needs bounded covered).suffixEnvironment ordered (depth+1) = tail.suffixEnvironment ordered depth := by
  cases tail
  simp only [suffixEnvironment, capture, fullTail]
  rw [peelMeasuredData]
  rfl

theorem OriginalRichFrame.suffixEnvironment_group
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (sourceOrdered : sourceEnv.Ordered) (initial : List Closure)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals left available initial rawCapture leftValue rightValue)
    (ordered : headerEnv.Ordered) (depth : Nat) :
    (tail.group domain sourceOrdered initial entries).suffixEnvironment ordered (depth+1) =
      tail.suffixEnvironment ordered depth := by
  cases tail
  simp only [suffixEnvironment, group, fullTail]
  rw [peelMeasuredData]
  rfl


/-- A route reserve belongs to the captured head; deleting that source slot
also deletes its reserve. The suffix retains its own earlier history. -/
theorem OriginalRichFrame.suffixEnvironment_reserve_succ
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (closures : List Closure) (ordered : sourceEnv.Ordered) (depth : Nat) :
    (frame.reserve closures).suffixEnvironment ordered (depth + 1) =
      frame.suffixEnvironment ordered (depth + 1) := by
  cases context with
  | nil => simp only [suffixEnvironment]
  | cons context domain =>
    cases frame
    simp only [suffixEnvironment, OriginalRichFrame.reserve, OriginalRichFrame.fullTail]
    rw [OriginalRichFrame.peelMeasuredData]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
