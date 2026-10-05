import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionQuery

/-! Every exposed projection field formation is an actual original reference.
This permits capture factoring with its original root, without reifying soundness. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

private def IsReference (node : EndpointState env U Γ expression type) : Prop :=
  ∃ reference, node = .ref reference

/-- References remain lazy; exposing one separately reestablishes this
invariant from its actual original derivation. -/
def EndpointState.OriginalProjectionFields : EndpointState env U Γ expression type → Prop
  | .ref _ | .sort _ => True
  | .bvar _ _ formation => formation.OriginalProjectionFields
  | .app _ _ domain codomain fn arg result =>
      IsReference domain ∧ domain.OriginalProjectionFields ∧ codomain.OriginalProjectionFields ∧
        fn.OriginalProjectionFields ∧ arg.OriginalProjectionFields ∧ result.OriginalProjectionFields
  | .lam _ _ domain codomain body =>
      IsReference domain ∧ domain.OriginalProjectionFields ∧ codomain.OriginalProjectionFields ∧ body.OriginalProjectionFields
  | .pi _ _ domain body =>
      IsReference domain ∧ domain.OriginalProjectionFields ∧ body.OriginalProjectionFields
  | .proj _ _ _ _ _ _ _ field _ _ _ => IsReference field ∧ field.OriginalProjectionFields
  | .convert _ term => term.OriginalProjectionFields

@[simp] theorem EndpointState.originalProjectionFields_cast
    (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U Γ expression type) :
    (node.cast expressionEq typeEq).OriginalProjectionFields ↔ node.OriginalProjectionFields := by
  cases expressionEq
  cases typeEq
  rfl

theorem Derivation.expose_originalProjectionFields (original : Derivation env U Γ left right type) :
    original.expose.1.OriginalProjectionFields ∧ original.expose.2.OriginalProjectionFields := by
  induction original with
  | symm original ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩
  | beta _ _ _ _ _ _ _ instantiated _ _ _ _ _ ih =>
    exact ⟨⟨⟨_, rfl⟩, trivial, trivial, ⟨⟨_, rfl⟩, trivial, trivial, trivial⟩, trivial, trivial⟩, ih.1⟩
  | eta hu hv domain codomain liftedCodomain term liftedTerm liftedDomain _ _ _ ih _ _ =>
    refine ⟨⟨⟨_, rfl⟩, trivial, trivial, ?_⟩, ih.1⟩
    change (EndpointState.cast rfl (inst_liftN_bvar _ 0) _).OriginalProjectionFields
    rw [EndpointState.originalProjectionFields_cast]
    exact ⟨⟨_, rfl⟩, trivial, trivial, trivial, trivial, by
      rw [EndpointState.originalProjectionFields_cast]; trivial⟩
  | proofIrrel _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra _ _ _ _ _ _ _ left right _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | elimIota _ _ _ _ _ _ _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | projIota _ projection _ field ihProjection ihField => exact ⟨ihProjection.1, ihField.1⟩
  | structEta _ _ _ major constructor ihMajor ihConstructor => exact ⟨ihConstructor.1, ihMajor.1⟩
  | unitLike _ _ _ _ left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | _ => simp [Derivation.expose, EndpointState.OriginalProjectionFields, IsReference]

theorem EndpointRef.expose_originalProjectionFields (reference : EndpointRef env U Γ expression type) :
    reference.expose.OriginalProjectionFields := by
  cases reference with
  | left original => exact original.expose_originalProjectionFields.1
  | right original => exact original.expose_originalProjectionFields.2

theorem Derivation.typeFormation_OriginalProjectionFields
    (original : Derivation env U Γ left right type) :
    original.typeFormation.node.OriginalProjectionFields := by
  induction original <;> simp_all [Derivation.typeFormation, EndpointState.OriginalProjectionFields, IsReference]

theorem EndpointRef.typeFormation_OriginalProjectionFields
    (reference : EndpointRef env U Γ expression type) :
    reference.typeFormation.node.OriginalProjectionFields := by
  cases reference with
  | left original => exact original.typeFormation_OriginalProjectionFields
  | right original => exact original.typeFormation_OriginalProjectionFields

theorem EndpointConversion.targetFormation_OriginalProjectionFields
    (plan : EndpointConversion env U Γ A B) :
    plan.targetFormation.node.OriginalProjectionFields := by
  cases plan <;> simp [EndpointConversion.targetFormation, EndpointState.OriginalProjectionFields, IsReference]

theorem EndpointState.typeFormation_OriginalProjectionFields
    (node : EndpointState env U Γ expression type) (original : node.OriginalProjectionFields) :
    node.typeFormation.node.OriginalProjectionFields := by
  cases node with
  | ref reference => exact reference.typeFormation_OriginalProjectionFields
  | convert plan term => exact plan.targetFormation_OriginalProjectionFields
  | _ => simp_all [EndpointState.typeFormation, EndpointState.OriginalProjectionFields]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

theorem Located.originalProjectionFields (location : Located root node) : node.OriginalProjectionFields := by
  induction location with
  | here => trivial
  | expose => exact EndpointRef.expose_originalProjectionFields _
  | convertTerm _ ih => exact ih
  | appPiFormation _ ih => exact ⟨ih.1, ih.2.1, ih.2.2.1⟩
  | appDomain _ ih => exact ih.2.1
  | appCodomain _ ih => exact ih.2.2.1
  | appFunction _ ih => exact ih.2.2.2.1
  | appArgument _ ih => exact ih.2.2.2.2.1
  | appResult _ ih => exact ih.2.2.2.2.2
  | lamDomain _ ih | piDomain _ ih => exact ih.2.1
  | lamCodomain _ ih => exact ih.2.2.1
  | lamBody _ ih => exact ih.2.2.2
  | piBody _ ih => exact ih.2.2
  | projField _ ih => exact ih.2
  | projMajor _ _ => trivial
  | assignedFormation _ ih => exact EndpointState.typeFormation_OriginalProjectionFields _ ih


end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
