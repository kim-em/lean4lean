import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax

/-! The first genuinely dependent projection link. The next field's original
formation child supplies the earlier projected type; no projection typing is
synthesized. Both requests retain their complete domains, anchors and supports,
and both major queries are actual variable observations with explicit leaves.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

def fieldRequest
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (σ : Subst) (input support : Profile n) : DataRequest (Profile n) :=
  ⟨⟨head.fieldType.subst σ, (VExpr.proj name index major).subst σ, input⟩, support⟩

def fieldRecord (family : FamilyData (Profile n)) (relevant : family.relevant = true)
    (index : Nat) (request : DataRequest (Profile n)) : RecordData (Profile n) :=
  ⟨family, relevant, [(index, request)]⟩

def majorNeed (record : RecordData (Profile n)) : Need :=
  ⟨n + 1, .singleton (.record record)⟩

/-- For `Pack(T : Type)(x : T)`, the second projection's actual formation
child has expression `Pack.T p`. Exposing that child produces the first
projection query and then a certificate for the second field's assigned type.
The two field demands may be empty or inhabited; their exact finite leaves
are retained in either case. -/
theorem dependentField
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {name : Name} {firstIndex secondIndex slot : Nat} {assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name secondIndex (.bvar slot)) assigned}
    (head : ProjectionHead node)
    (dependent : head.fieldType = .proj name firstIndex (.bvar slot))
    (sortLevel : VLevel)
    (firstSort : (projectionHead (head.field.cast dependent rfl)).fieldType = .sort sortLevel)
    (sortLevelRelevant : Relevant sortLevel true)
    {typeDemand valueDemand : Profile n}
    (typeFormed : typeDemand.HasType (.sort true))
    (valueTyped : valueDemand.HasType typeDemand)
    (family : FamilyData (Profile n)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true) :
    let first := projectionHead (head.field.cast dependent rfl)
    let firstRequest := fieldRequest first σ typeDemand (.sort true)
    let secondRequest := fieldRequest head σ valueDemand typeDemand
    let firstRecord := fieldRecord family familyRelevant firstIndex firstRequest
    let secondRecord := fieldRecord family familyRelevant secondIndex secondRequest
    Nonempty (RichCert sourceEnv env U registry target head.field locals σ true typeDemand
      [(slot, majorNeed firstRecord)]) ∧
    Nonempty (RichObs sourceEnv env U registry target node locals σ valueDemand
      ([(slot, majorNeed secondRecord)] ++ [(slot, majorNeed firstRecord)])) := by
  dsimp only
  let first := projectionHead (head.field.cast dependent rfl)
  let firstRequest := fieldRequest first σ typeDemand (.sort true)
  let secondRequest := fieldRequest head σ valueDemand typeDemand
  let firstRecord := fieldRecord family familyRelevant firstIndex firstRequest
  let secondRecord := fieldRecord family familyRelevant secondIndex secondRequest
  have firstFieldCode : RichCert sourceEnv env U registry target first.field locals σ true
      (Profile.sort (n := n) true) [] := by
    apply RichCert.legacy
    have shape : first.fieldType = .sort sortLevel := firstSort
    rw [shape]
    exact .seed (.sort sortLevelRelevant) (Profile.HasType.sort true)
  let firstMajor : RichObs sourceEnv env U registry target (.ref (.right first.major)) locals σ
      (.singleton (n := n + 1) (.record firstRecord)) [(slot, majorNeed firstRecord)] :=
    .legacy (.legacy (.var locals σ slot _))
  have firstQuery : RichObs sourceEnv env U registry target (head.field.cast dependent rfl)
      locals σ typeDemand [(slot, majorNeed firstRecord)] := by
    simpa only [List.append_nil, firstRequest, fieldRequest] using
      RichObs.projection first (by exact familyName) (List.mem_singleton_self _)
        firstMajor firstFieldCode typeFormed (.refl _)
  let actualFieldCode : RichCert sourceEnv env U registry target head.field locals σ true typeDemand
      [(slot, majorNeed firstRecord)] :=
    RichCert.ofCast dependent rfl (.observe firstQuery typeFormed)
  let secondMajor : RichObs sourceEnv env U registry target (.ref (.right head.major)) locals σ
      (.singleton (n := n + 1) (.record secondRecord)) [(slot, majorNeed secondRecord)] :=
    .legacy (.legacy (.var locals σ slot _))
  exact ⟨⟨actualFieldCode⟩, ⟨RichObs.projection head familyName (List.mem_singleton_self _)
    secondMajor actualFieldCode valueTyped (.refl _)⟩⟩

/-- The primitive's formation and major are strict original children even
when finite source exposure/conversion precedes the primitive. -/
theorem projectionChildCosts
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (initial : List Closure) :
    (Closure.close head.field.origin initial).cost < (Closure.close node.origin initial).cost ∧
      (Closure.close head.major.origin initial).cost < (Closure.close node.origin initial).cost := by
  have parent := Nat.mul_le_mul_right (1 + environmentCost initial) head.route.weight_le
  constructor
  · exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child
        (children := [head.field.origin, head.major.origin]) (by simp)) initial) parent
  · exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child
        (children := [head.field.origin, head.major.origin]) (by simp)) initial) parent

/-- The first projection in the dependent link is recovered inside the
second field's existing formation reserve. No cost for an invented projection
derivation and no same-parent recursive call is required. -/
theorem dependentField_schedule
    {node : EndpointState sourceEnv U source (.proj name secondIndex (.bvar slot)) assigned}
    (head : ProjectionHead node)
    (dependent : head.fieldType = .proj name firstIndex (.bvar slot))
    (initial : List Closure) :
    let first := projectionHead (head.field.cast dependent rfl)
    schedule .fundamental (Closure.close first.field.origin initial).cost <
      schedule .fundamental (Closure.close node.origin initial).cost ∧
    schedule .fundamental (Closure.close first.major.origin initial).cost <
      schedule .fundamental (Closure.close node.origin initial).cost := by
  dsimp only
  have inside := projectionChildCosts (projectionHead (head.field.cast dependent rfl)) initial
  simp only [EndpointState.origin_cast] at inside
  have outer := (projectionChildCosts head initial).1
  exact ⟨schedule_strict (Nat.lt_trans inside.1 outer) _ _,
    schedule_strict (Nat.lt_trans inside.2 outer) _ _⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
