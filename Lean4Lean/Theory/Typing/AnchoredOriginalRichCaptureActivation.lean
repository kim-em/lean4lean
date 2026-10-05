import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure

/-! Demand-driven capture activation. The output frame is computed from the
actual incoming owner query. An empty capture slot is not required to support
a nonempty query before it is activated. The original owner and declared
domain remain distinct, and the external base valuation is unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def captureNeeds (profile : Profile n) : List Need :=
  [Need.mk n profile] ++ [Need.mk n profile].flatMap Need.singletons

theorem captureNeeds_covered (profile : Profile n) (need : Need)
    (member : need ∈ captureNeeds profile) :
    need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ profile.atoms := by
  rcases List.mem_append.mp member with member | member
  · cases List.mem_singleton.mp member
    exact ⟨Nat.le_refl _, by
      simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self] using (fun _ h => h)⟩
  · obtain ⟨old, oldMember, member⟩ := List.mem_flatMap.mp member
    cases List.mem_singleton.mp oldMember
    obtain ⟨atom, present, equal⟩ := List.mem_map.mp member
    cases equal
    refine ⟨Nat.le_refl _, ?_⟩
    simp only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self]
    intro a member
    cases List.mem_singleton.mp member
    exact present

/-- The capture graph records an equality in source syntax, before target
realization. It is strictly stronger than equal realized target terms. -/
def captureSourceMap (tail : Subst) (expression : VExpr) : Subst := tail.cons expression

@[simp] theorem captureSourceMap_head (tail : Subst) (expression : VExpr) :
    (VExpr.bvar 0).subst (captureSourceMap tail expression) = expression := rfl

noncomputable def HeaderRichTail.activateQuery
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (owner : HeaderOwner field major)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available (input : Profile n)) :
    HeaderRichTail header field major env registry target (.cons context domain) (Locals.push locals)
      (left.cons (owner.expression.subst ownerLeft)) (right.cons (owner.expression.subst ownerRight))
      (available.push (captureNeeds input)) :=
  .push tail domain location lineage owner answer (answer.related henv) (captureNeeds input)
    (fun need member => (captureNeeds_covered input need member).1)
    (fun need member => (captureNeeds_covered input need member).2)

/-- The finite owner answer is used to create the capture demand, not to
assume that demand was available in the incoming empty slot. This covers
Pi-, app-, and projection-shaped owners without relabelling their endpoints. -/
theorem HeaderRichTail.reindexCapturedQuery
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (owner : HeaderOwner field major)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available (input : Profile n))
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) assigned)
    (closed : available.AtomClosed) :
    Nonempty (HeaderBinderFrame header field major env registry target (.cons context domain)
      (Locals.push locals) (left.cons (owner.expression.subst ownerLeft))
      (right.cons (owner.expression.subst ownerRight)) (available.push (captureNeeds input))) ∧
    (available.push (captureNeeds input)).AtomClosed ∧
    Nonempty (RichGradedResult headerEnv env U registry target variableNode (Locals.push locals)
      (right.cons (owner.expression.subst ownerRight)) (available.push (captureNeeds input)) input) := by
  refine ⟨⟨.captured (tail.activateQuery henv domain location lineage owner answer)⟩,
    Valuation.push_atomized_closed closed _, ?_⟩
  exact ⟨{
    rank := n, bound := Nat.le_refl _, raw := input
    footprint := [(0, Need.mk n input)]
    observation := .legacy (.legacy (.var _ _ 0 input))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by
      intro i need member
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ (List.mem_singleton_self _)
    live := answer.value.related.live henv hscoped formed }⟩

/-- The new external footprint is empty: the reconstructed query requests
only the slot whose ORIGINAL owner answer created the output frame. -/
theorem capturedQuery_external :
    BinderPack n input [(0, Need.mk n input)] [] := by
  simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self,
    Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using
    (BinderPack.local (Need.mk n input) (Nat.le_refl n) BinderPack.nil)

noncomputable def HeaderOwner.dependencyEnvironment
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    (ordered : sourceEnv.Ordered) (owner : HeaderOwner field major) (initial : List Closure) : List Closure :=
  match owner with
  | .inl node | .inr node => node.location.dependencyEnvironment ordered initial

noncomputable def HeaderOwner.dependencyClosure
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    (ordered : sourceEnv.Ordered) (owner : HeaderOwner field major) (initial : List Closure) : Closure :=
  .close (owner.node.dependencyOrigin ordered) (owner.dependencyEnvironment ordered initial)

theorem HeaderRichTail.activateQuery_environment
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (owner : HeaderOwner field major)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available (input : Profile n))
    (initial : List Closure) :
    (tail.activateQuery henv domain location lineage owner answer).dependencyEnvironment hf sf initial =
      .bundle (owner.dependencyClosure sf initial)
        (.close (domain.dependencyOrigin hf) (tail.dependencyEnvironment hf sf initial)) ::
          tail.dependencyEnvironment hf sf initial := by
  cases owner <;> rfl

/-- The activated slot pays for both the exact original owner's formation
and its distinct declared-domain formation. The bound uses that same slot,
including every earlier captured dependency. -/
theorem HeaderRichTail.activateQuery_alignment_bound
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (owner : HeaderOwner field major)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available (input : Profile n))
    (initial : List Closure) (lookupOrigin : Origin) :
    (Closure.close (owner.node.typeFormation.node.dependencyOrigin sf)
      (owner.dependencyEnvironment sf initial)).cost +
    (Closure.close (domain.dependencyOrigin hf) (tail.dependencyEnvironment hf sf initial)).cost <
    (Closure.close lookupOrigin
      ((tail.activateQuery henv domain location lineage owner answer).dependencyEnvironment hf sf initial)).cost := by
  rw [tail.activateQuery_environment henv hf sf domain location lineage owner answer initial]
  apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (owner.node.typeFormation_dependency_cost_le sf _) _)
  exact variable_lookup lookupOrigin (show Closure.bundle (owner.dependencyClosure sf initial)
    (.close (domain.dependencyOrigin hf) (tail.dependencyEnvironment hf sf initial)) ∈
      _ :: tail.dependencyEnvironment hf sf initial from List.mem_cons_self)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
