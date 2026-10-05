import Lean4Lean.Theory.Typing.AnchoredOriginalRichTypeFormationMeasure

/-! Lazy exposure either retains the very same assigned-type formation
occurrence, or pays for both distinct original formation occurrences from
proper original children. This avoids a same-cost reindex at reference nodes. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

theorem Derivation.exposedFormation_dependency_weight_le (formed : env.Ordered)
    (original : Derivation env U source left right type) :
    (original.expose.1.typeFormation.node.dependencyOrigin formed).weight ≤ (original.dependencyOrigin formed).weight ∧
    (original.expose.2.typeFormation.node.dependencyOrigin formed).weight ≤ (original.dependencyOrigin formed).weight :=
  ⟨Nat.le_trans (original.expose.1.typeFormation_dependency_weight_le formed)
      (original.expose_dependency_weight_le formed).1,
   Nat.le_trans (original.expose.2.typeFormation_dependency_weight_le formed)
      (original.expose_dependency_weight_le formed).2⟩

private theorem rule_pair_weight (first second : Origin) :
    first.weight + second.weight < (Origin.rule [first, second]).weight := by
  simp [Origin.weight]

/-- Equality here is equality of the finite formation view, including its
actual node, not raw expression equality or proof irrelevance of derivations. -/
theorem Derivation.exposure_formation_reserve (formed : env.Ordered)
    (original : Derivation env U source left right type) :
    (original.expose.1.typeFormation = original.typeFormation ∨
      (original.expose.1.typeFormation.node.dependencyOrigin formed).weight +
        (original.typeFormation.node.dependencyOrigin formed).weight < (original.dependencyOrigin formed).weight) ∧
    (original.expose.2.typeFormation = original.typeFormation ∨
      (original.expose.2.typeFormation.node.dependencyOrigin formed).weight +
        (original.typeFormation.node.dependencyOrigin formed).weight < (original.dependencyOrigin formed).weight) := by
  induction original with
  | bvar | sortDF | constDF | elimDF | appDF | projDF | lamDF | forallEDF | defeqDF =>
    exact ⟨Or.inl rfl, Or.inl rfl⟩
  | symm original ih =>
    constructor
    · rcases ih.2 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        have strict := Origin.rule_child (child := original.dependencyOrigin formed)
          (children := [original.dependencyOrigin formed]) (by simp)
        conv => rhs; rw [dependencyOrigin.eq_def]
        exact Nat.lt_trans bound strict
    · rcases ih.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        have strict := Origin.rule_child (child := original.dependencyOrigin formed)
          (children := [original.dependencyOrigin formed]) (by simp)
        conv => rhs; rw [dependencyOrigin.eq_def]
        exact Nat.lt_trans bound strict
  | trans first second firstIH secondIH =>
    constructor
    · rcases firstIH.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        have strict := Origin.rule_child (child := first.dependencyOrigin formed)
          (children := [first.dependencyOrigin formed, second.dependencyOrigin formed]) (by simp)
        conv => rhs; rw [dependencyOrigin.eq_def]
        exact Nat.lt_trans bound strict
    · right
      have leftBound := first.typeFormation_dependency_weight_le formed
      have rightBound := (second.exposedFormation_dependency_weight_le formed).2
      simp only [expose, typeFormation]
      conv => rhs; rw [dependencyOrigin.eq_def]
      exact Nat.lt_of_le_of_lt (Nat.add_le_add rightBound leftBound) (by
        simpa only [Nat.add_comm] using rule_pair_weight (first.dependencyOrigin formed) (second.dependencyOrigin formed))
  | beta hu hv domain codomain body argument result instantiated _ _ _ _ _ instantiatedIH =>
    refine ⟨Or.inl rfl, Or.inr ?_⟩
    have rightBound := (instantiated.exposedFormation_dependency_weight_le formed).1
    simp only [expose, typeFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin]
    conv => rhs; rw [dependencyOrigin.eq_def]
    simp only [Origin.weight, dependencyBetaLeftOrigin, capturedApplicationOrigin, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  | eta hu hv domain codomain liftedCodomain term liftedTerm liftedDomain _ _ _ termIH _ _ =>
    refine ⟨Or.inl rfl, Or.inr ?_⟩
    have rightBound := (term.exposedFormation_dependency_weight_le formed).1
    simp only [expose, typeFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin]
    conv => rhs; rw [dependencyOrigin.eq_def]
    simp only [Origin.weight, dependencyEtaLeftOrigin, dependencyEtaBodyOrigin, capturedApplicationOrigin,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  | proofIrrel proposition left right _ leftIH rightIH =>
    have leftBound := (left.exposedFormation_dependency_weight_le formed).1
    have rightBound := (right.exposedFormation_dependency_weight_le formed).1
    constructor <;> right <;>
      simp only [expose, typeFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin] <;>
      (conv => rhs; rw [dependencyOrigin.eq_def]) <;>
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] <;> omega
  | extra a b c d formation left right ambientLeft ambientRight _ _ _ leftIH rightIH =>
    constructor
    · rcases leftIH.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        conv => rhs; rw [dependencyOrigin.eq_def]
        simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    · right
      have leftBound := ambientLeft.typeFormation_dependency_weight_le formed
      have rightBound := (ambientRight.exposedFormation_dependency_weight_le formed).1
      simp only [expose, typeFormation]
      conv => rhs; rw [dependencyOrigin.eq_def]
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  | elimIota a b c d e levelWF formation left right _ leftIH rightIH =>
    have leftBound := (left.exposedFormation_dependency_weight_le formed).1
    have rightBound := (right.exposedFormation_dependency_weight_le formed).1
    constructor <;> right <;>
      simp only [expose, typeFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin] <;>
      (conv => rhs; rw [dependencyOrigin.eq_def]) <;>
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] <;> omega
  | projIota selected projection fieldWF field projectionIH fieldIH =>
    constructor
    · rcases projectionIH.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        conv => rhs; rw [dependencyOrigin.eq_def]
        simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    · right
      have leftBound := projection.typeFormation_dependency_weight_le formed
      have rightBound := (field.exposedFormation_dependency_weight_le formed).1
      simp only [expose, typeFormation]
      conv => rhs; rw [dependencyOrigin.eq_def]
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  | structEta selected parameters closed major constructor majorIH constructorIH =>
    constructor
    · right
      have leftBound := major.typeFormation_dependency_weight_le formed
      have rightBound := (constructor.exposedFormation_dependency_weight_le formed).1
      simp only [expose, typeFormation]
      conv => rhs; rw [dependencyOrigin.eq_def]
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
    · rcases majorIH.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        conv => rhs; rw [dependencyOrigin.eq_def]
        simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | unitLike a b c d left right leftIH rightIH =>
    constructor
    · rcases leftIH.1 with same | bound
      · exact Or.inl same
      · right
        simp only [expose, typeFormation]
        conv => rhs; rw [dependencyOrigin.eq_def]
        simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    · right
      have leftBound := left.typeFormation_dependency_weight_le formed
      have rightBound := (right.exposedFormation_dependency_weight_le formed).1
      simp only [expose, typeFormation]
      conv => rhs; rw [dependencyOrigin.eq_def]
      simp only [Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega

theorem EndpointRef.exposure_formation_reserve (formed : env.Ordered)
    (reference : EndpointRef env U source expression type) :
    reference.expose.typeFormation = reference.typeFormation ∨
      (reference.expose.typeFormation.node.dependencyOrigin formed).weight +
        (reference.typeFormation.node.dependencyOrigin formed).weight <
          (reference.dependencyOrigin formed).weight := by
  cases reference with
  | left original => exact (original.exposure_formation_reserve formed).1
  | right original => exact (original.exposure_formation_reserve formed).2

theorem EndpointRef.exposure_formation_cost_reserve (formed : env.Ordered)
    (reference : EndpointRef env U source expression type) (captured : List Closure) :
    reference.expose.typeFormation = reference.typeFormation ∨
      (Closure.close (reference.expose.typeFormation.node.dependencyOrigin formed) captured).cost +
        (Closure.close (reference.typeFormation.node.dependencyOrigin formed) captured).cost <
          (Closure.close (reference.dependencyOrigin formed) captured).cost := by
  rcases reference.exposure_formation_reserve formed with same | strict
  · exact Or.inl same
  · right
    simpa only [Closure.cost, Nat.add_mul] using
      Nat.mul_lt_mul_of_pos_right strict (show 0 < 1 + environmentCost captured by omega)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
