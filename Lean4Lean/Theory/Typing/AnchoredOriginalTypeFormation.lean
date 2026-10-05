import Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints

/-! Assigned-type formation views selected from actual original premises.
The finite Pi and sort nodes are explicit syntax; all non-synthetic leaves
retain original endpoint references. In particular no derived `isType'`
proof is reified as a new original source premise.
-/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- A finite formation view at the exact assigned source type. -/
structure TypeFormation (env : VEnv) (U : Nat) (source : List VExpr) (type : VExpr) where
  level : VLevel
  levelWF : level.WF U
  node : EndpointState env U source type (.sort level)

/-- Select the original formation child, or construct the finite sort/Pi
view directly from the original domain and codomain children. The `extra`
case follows its ambient child, preserving the current source context. -/
def Derivation.typeFormation (original : Derivation env U source left right type) :
    TypeFormation env U source type :=
  match original with
  | .bvar _ levelWF formation => ⟨_, levelWF, .ref (.left formation)⟩
  | .symm original => original.typeFormation
  | .trans first _ => first.typeFormation
  | .sortDF levelWF _ _ =>
      ⟨.succ (.succ _), levelWF, .sort (level := .succ _) levelWF⟩
  | .constDF _ _ _ _ _ levelWF _ ambient => ⟨_, levelWF, .ref (.left ambient)⟩
  | .elimDF _ _ _ _ _ _ levelWF formation => ⟨_, levelWF, .ref (.left formation)⟩
  | .appDF _ levelWF _ _ _ _ result => ⟨_, levelWF, .ref (.left result)⟩
  | .projDF _ _ _ _ _ _ levelWF field _ _ _ _ => ⟨_, levelWF, .ref (.left field)⟩
  | .lamDF domainWF bodyWF domain codomain _ _ _ =>
      ⟨.imax _ _, ⟨domainWF, bodyWF⟩,
        .pi domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain))⟩
  | .forallEDF domainWF bodyWF _ _ _ =>
      ⟨.succ (.imax _ _), ⟨domainWF, bodyWF⟩,
        .sort (level := .imax _ _) ⟨domainWF, bodyWF⟩⟩
  | .defeqDF levelWF types _ => ⟨_, levelWF, .ref (.right types)⟩
  | .beta _ levelWF _ _ _ _ result _ => ⟨_, levelWF, .ref (.left result)⟩
  | .eta domainWF bodyWF domain codomain _ _ _ _ =>
      ⟨.imax _ _, ⟨domainWF, bodyWF⟩,
        .pi domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain))⟩
  | .proofIrrel proposition _ _ => ⟨.zero, trivial, .ref (.left proposition)⟩
  | .extra _ _ _ _ _ _ _ ambientLeft _ => ambientLeft.typeFormation
  | .elimIota _ _ _ _ _ levelWF formation _ _ => ⟨_, levelWF, .ref (.left formation)⟩
  | .projIota _ projection _ _ => projection.typeFormation
  | .structEta _ _ _ major _ => major.typeFormation
  | .unitLike _ _ _ _ left _ => left.typeFormation

theorem TypeFormation.sound (formation : TypeFormation env U source type) :
    env.IsDefEqStrong U source type type (.sort formation.level) := formation.node.sound

/-- Type formation is charged to the same actual original derivation that
supplied the assigned type. Every retained endpoint side keeps its original
reserve, including the right side selected by an explicit conversion. -/
theorem Derivation.typeFormation_weight_le
    (original : Derivation env U source left right type) :
    original.typeFormation.node.origin.weight ≤ original.origin.weight := by
  induction original <;>
    simp only [typeFormation, origin, EndpointState.origin, EndpointRef.origin,
      applicationOrigin, lambdaOrigin, betaLeftOrigin, etaLeftOrigin,
      etaBodyOrigin, Origin.weight, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.mul_one,
      Nat.one_mul] at * <;> omega

/-- Both endpoint sides have the same original assigned type; choosing its
formation does not diagonalize either endpoint proof. -/
def EndpointRef.typeFormation : EndpointRef env U source expression type →
    TypeFormation env U source type
  | .left original | .right original => original.typeFormation

theorem EndpointRef.typeFormation_weight_le
    (reference : EndpointRef env U source expression type) :
    reference.typeFormation.node.origin.weight ≤ reference.origin.weight := by
  cases reference with
  | left original => exact original.typeFormation_weight_le
  | right original => exact original.typeFormation_weight_le

theorem EndpointRef.typeFormation_cost_le
    (reference : EndpointRef env U source expression type) (captured : List Closure) :
    (Closure.close reference.typeFormation.node.origin captured).cost ≤
      (Closure.close reference.origin captured).cost :=
  Nat.mul_le_mul_right (1 + environmentCost captured) reference.typeFormation_weight_le

/-- At every non-sort, non-Pi assigned type, the computed formation view
is an actual original endpoint reference. -/
theorem Derivation.typeFormation_reference
    (original : Derivation env U source left right type)
    (notSort : ∀ level, type ≠ .sort level)
    (notPi : ∀ domain body, type ≠ .forallE domain body) :
    ∃ reference, original.typeFormation.node = EndpointState.ref reference := by
  induction original with
  | symm original ih => exact ih notSort notPi
  | trans first _ ih _ => exact ih notSort notPi
  | sortDF => exact False.elim (notSort _ rfl)
  | lamDF => exact False.elim (notPi _ _ rfl)
  | forallEDF => exact False.elim (notSort _ rfl)
  | eta => exact False.elim (notPi _ _ rfl)
  | extra _ _ _ _ _ _ _ _ _ _ _ _ ih _ => exact ih notSort notPi
  | projIota _ _ _ _ ih _ => exact ih notSort notPi
  | structEta _ _ _ _ _ ih _ => exact ih notSort notPi
  | unitLike _ _ _ _ _ _ ih _ => exact ih notSort notPi
  | _ => exact ⟨_, rfl⟩

/-- This reference is the exact leaf of the computed formation view, not
an independently supplied derivation of the same raw family expression. -/
structure FamilyFormationRef
    (original : Derivation env U source left right (mkApps (.const name levels) arguments)) where
  reference : EndpointRef env U source (mkApps (.const name levels) arguments)
    (.sort original.typeFormation.level)
  exactNode : original.typeFormation.node = .ref reference

noncomputable def Derivation.familyFormationRef
    (original : Derivation env U source left right (mkApps (.const name levels) arguments)) :
    FamilyFormationRef original :=
  let existsRef := original.typeFormation_reference
    (fun _ => mkApps_ne_sort (fn := .const name levels) (by intro _ equal; cases equal) arguments)
    (fun _ _ => mkApps_ne_forallE (fn := .const name levels) (by intro _ _ equal; cases equal) arguments)
  ⟨Classical.choose existsRef, Classical.choose_spec existsRef⟩

theorem FamilyFormationRef.levelWF
    {original : Derivation env U source left right (mkApps (.const name levels) arguments)}
    (_formation : FamilyFormationRef original) : original.typeFormation.level.WF U :=
  original.typeFormation.levelWF

theorem FamilyFormationRef.weight_le
    {original : Derivation env U source left right (mkApps (.const name levels) arguments)}
    (formation : FamilyFormationRef original) :
    formation.reference.origin.weight ≤ original.origin.weight := by
  have bound := original.typeFormation_weight_le
  simpa only [formation.exactNode, EndpointState.origin] using bound

theorem FamilyFormationRef.cost_le
    {original : Derivation env U source left right (mkApps (.const name levels) arguments)}
    (formation : FamilyFormationRef original) (captured : List Closure) :
    (Closure.close formation.reference.origin captured).cost ≤
      (Closure.close original.origin captured).cost :=
  Nat.mul_le_mul_right (1 + environmentCost captured) formation.weight_le

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

def EndpointConversion.targetFormation (plan : EndpointConversion env U source A B) :
    TypeFormation env U source B :=
  match plan with
  | .forward levelWF original => ⟨_, levelWF, .ref (.right original)⟩
  | .backward levelWF original => ⟨_, levelWF, .ref (.left original)⟩
  | .piDomain domainWF bodyWF domain body _ =>
      ⟨.imax _ _, ⟨domainWF, bodyWF⟩, .pi domainWF bodyWF (.ref (.left domain)) (.ref (.left body))⟩

/-- No derived raw formation judgment is reified. Each synthetic formation
node is built from the existing original endpoint's retained children. -/
def EndpointState.typeFormation (node : EndpointState env U source expression assigned) :
    TypeFormation env U source assigned :=
  match node with
  | .ref reference => reference.typeFormation
  | .sort levelWF => ⟨.succ (.succ _), levelWF, .sort (level := VLevel.succ _) levelWF⟩
  | .bvar _ levelWF formation => ⟨_, levelWF, formation⟩
  | .app _ bodyWF _ _ _ _ result => ⟨_, bodyWF, result⟩
  | .lam domainWF bodyWF domain codomain _ =>
      ⟨.imax _ _, ⟨domainWF, bodyWF⟩, .pi domainWF bodyWF domain codomain⟩
  | .pi domainWF bodyWF _ _ =>
      ⟨.succ (.imax _ _), ⟨domainWF, bodyWF⟩, .sort (level := .imax _ _) ⟨domainWF, bodyWF⟩⟩
  | .proj _ _ _ _ _ _ fieldWF field _ _ _ => ⟨_, fieldWF, field⟩
  | .convert plan _ => plan.targetFormation

theorem EndpointConversion.targetFormation_weight_le
    (plan : EndpointConversion env U source A B) :
    plan.targetFormation.node.origin.weight ≤ plan.origin.weight := by
  cases plan <;>
    simp only [targetFormation, EndpointState.origin, EndpointRef.origin, origin,
      Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.mul_one] <;> omega

theorem EndpointState.typeFormation_weight_le
    (node : EndpointState env U source expression assigned) :
    node.typeFormation.node.origin.weight ≤ node.origin.weight := by
  cases node with
  | ref reference => exact reference.typeFormation_weight_le
  | convert plan term =>
    have bound := plan.targetFormation_weight_le
    simp only [typeFormation, origin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  | _ =>
    simp only [typeFormation, origin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_mul, Nat.mul_add,
      Nat.mul_one] <;> omega

theorem EndpointState.typeFormation_cost_le
    (node : EndpointState env U source expression assigned) (captured : List Closure) :
    (Closure.close node.typeFormation.node.origin captured).cost ≤
      (Closure.close node.origin captured).cost :=
  Nat.mul_le_mul_right (1 + environmentCost captured) node.typeFormation_weight_le

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
