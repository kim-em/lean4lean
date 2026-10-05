import Lean4Lean.Theory.Typing.AnchoredOriginalRichDirectPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalQueryCompatibility

/-! Synthetic Pi-domain conversion is introduced only on an original lambda
endpoint. The invariant is hereditary and survives every actual Located
edge, including assigned formations. It does not assert this for arbitrary
manually constructed EndpointStates. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

def EndpointState.OriginalDirect : EndpointState env U Γ expression type → Prop
  | .ref _ | .sort _ => True
  | .bvar _ _ formation => formation.OriginalDirect
  | .app _ _ domain codomain fn arg result =>
      domain.OriginalDirect ∧ codomain.OriginalDirect ∧ fn.OriginalDirect ∧ arg.OriginalDirect ∧ result.OriginalDirect
  | .lam _ _ domain codomain body => domain.OriginalDirect ∧ codomain.OriginalDirect ∧ body.OriginalDirect
  | .pi _ _ domain body => domain.OriginalDirect ∧ body.OriginalDirect
  | .proj _ _ _ _ _ _ _ field _ _ _ => field.OriginalDirect
  | .convert (.piDomain ..) term => (∃ A body, expression = .lam A body) ∧ term.OriginalDirect
  | .convert (.forward ..) term => term.OriginalDirect
  | .convert (.backward ..) term => term.OriginalDirect

@[simp] theorem EndpointState.originalDirect_cast
    (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U Γ expression type) :
    (node.cast expressionEq typeEq).OriginalDirect ↔ node.OriginalDirect := by
  cases expressionEq; cases typeEq; rfl

theorem Derivation.expose_originalDirect (original : Derivation env U Γ left right type) :
    original.expose.1.OriginalDirect ∧ original.expose.2.OriginalDirect := by
  induction original with
  | symm original ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩
  | beta _ _ _ _ _ _ _ instantiated _ _ _ _ _ ih =>
    exact ⟨⟨trivial, trivial, ⟨trivial, trivial, trivial⟩, trivial, trivial⟩, ih.1⟩
  | eta hu hv domain codomain liftedCodomain term liftedTerm liftedDomain _ _ _ ih _ _ =>
    refine ⟨⟨trivial, trivial, ?_⟩, ih.1⟩
    change (EndpointState.cast rfl (inst_liftN_bvar _ 0) _).OriginalDirect
    rw [EndpointState.originalDirect_cast]
    exact ⟨trivial, trivial, trivial, trivial, by rw [EndpointState.originalDirect_cast]; trivial⟩
  | proofIrrel _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra _ _ _ _ _ _ _ left right _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | elimIota _ _ _ _ _ _ _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | projIota _ projection _ field ihProjection ihField => exact ⟨ihProjection.1, ihField.1⟩
  | structEta _ _ _ major constructor ihMajor ihConstructor => exact ⟨ihConstructor.1, ihMajor.1⟩
  | unitLike _ _ _ _ left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | _ => simp [Derivation.expose, EndpointState.OriginalDirect]

theorem EndpointRef.expose_originalDirect (reference : EndpointRef env U Γ expression type) :
    reference.expose.OriginalDirect := by
  cases reference with
  | left original => exact original.expose_originalDirect.1
  | right original => exact original.expose_originalDirect.2

theorem Derivation.typeFormation_originalDirect (original : Derivation env U Γ left right type) :
    original.typeFormation.node.OriginalDirect := by
  induction original <;> simp_all [Derivation.typeFormation, EndpointState.OriginalDirect]

theorem EndpointState.typeFormation_originalDirect (node : EndpointState env U Γ expression type)
    (original : node.OriginalDirect) : node.typeFormation.node.OriginalDirect := by
  cases node with
  | ref reference => cases reference <;> exact Derivation.typeFormation_originalDirect _
  | convert plan term => cases plan <;> simp [EndpointState.typeFormation, EndpointConversion.targetFormation, EndpointState.OriginalDirect]
  | _ => simp_all [EndpointState.typeFormation, EndpointState.OriginalDirect]

theorem EndpointState.OriginalDirect.direct
    {node : EndpointState env U Γ expression type}
    (original : node.OriginalDirect) (notLam : ∀ A body, expression ≠ .lam A body) : node.DirectPrefix := by
  induction node with
  | convert plan term ih =>
    cases plan with
    | forward => simpa only [EndpointState.DirectPrefix] using ih (by simpa only [OriginalDirect] using original) notLam
    | backward => simpa only [EndpointState.DirectPrefix] using ih (by simpa only [OriginalDirect] using original) notLam
    | piDomain => obtain ⟨⟨A, body, equal⟩, _⟩ := original; exact (notLam A body equal).elim
  | _ => trivial

theorem EndpointState.OriginalDirect.of_convert
    {plan : EndpointConversion env U Γ A B} {term : EndpointState env U Γ expression A}
    (original : (EndpointState.convert plan term).OriginalDirect) : term.OriginalDirect := by
  cases plan <;> simp_all only [EndpointState.OriginalDirect]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

theorem Located.originalDirect (location : Located root node) : node.OriginalDirect := by
  induction location with
  | here => trivial
  | expose => exact EndpointRef.expose_originalDirect _
  | convertTerm _ ih => exact EndpointState.OriginalDirect.of_convert ih
  | appPiFormation _ ih => exact ⟨ih.1, ih.2.1⟩
  | appDomain _ ih => exact ih.1
  | appCodomain _ ih => exact ih.2.1
  | appFunction _ ih => exact ih.2.2.1
  | appArgument _ ih => exact ih.2.2.2.1
  | appResult _ ih => exact ih.2.2.2.2
  | lamDomain _ ih | piDomain _ ih => exact ih.1
  | lamCodomain _ ih => exact ih.2.1
  | lamBody _ ih => exact ih.2.2
  | piBody _ ih => exact ih.2
  | projField _ ih => exact ih
  | projMajor _ _ => trivial
  | assignedFormation _ ih => exact EndpointState.typeFormation_originalDirect _ ih

theorem ConstantPrefix.directLocated
    {node : EndpointState env U source (.const name levels) assigned}
    (location : Located root node) (packet : ConstantPrefix node) :
    Nonempty (DirectPrefixRoute env U source (.const name levels) node (.ref packet.reference)) :=
  packet.route.direct (fun _ _ equal => by cases equal)
    (location.originalDirect.direct (fun _ _ equal => by cases equal))

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
