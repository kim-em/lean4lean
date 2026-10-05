import Lean4Lean.Theory.Typing.AnchoredOriginalDeclarationDependencies

/-! Isolated enriched origin interpretation of actual endpoint states and
source contexts. Original syntax and production closure fields stay intact. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
set_option backward.isDefEq.respectTransparency false

noncomputable def EndpointRef.dependencyOrigin (formed : env.Ordered) :
    EndpointRef env U source expression type → Origin
  | .left original | .right original => original.dependencyOrigin formed

noncomputable def EndpointConversion.dependencyOrigin (formed : env.Ordered) :
    EndpointConversion env U source A B → Origin
  | .forward _ original | .backward _ original => original.dependencyOrigin formed
  | .piDomain _ _ domain body other => .binder (domain.dependencyOrigin formed)
      [other.dependencyOrigin formed, body.dependencyOrigin formed] []

noncomputable def EndpointState.dependencyOrigin (formed : env.Ordered) :
    EndpointState env U source expression type → Origin
  | .ref reference => reference.dependencyOrigin formed
  | .sort _ => .rule []
  | .bvar _ _ formation => .rule [formation.dependencyOrigin formed]
  | .app _ _ domain codomain function argument result =>
      capturedApplicationOrigin (domain.dependencyOrigin formed) (codomain.dependencyOrigin formed)
        (function.dependencyOrigin formed) (argument.dependencyOrigin formed) (result.dependencyOrigin formed)
  | .lam _ _ domain codomain body => .binder (domain.dependencyOrigin formed)
      [codomain.dependencyOrigin formed, body.dependencyOrigin formed] []
  | .pi _ _ domain body => .binder (domain.dependencyOrigin formed) [body.dependencyOrigin formed] []
  | .proj (info := info) (index := index) registered levelsWF _ _ _ _ _ field major _ _ =>
      let header := selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF
      let roots := projectionParameterDependencies formed registered levelsWF
      let parameters := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum
      let h := header.original.dependencyOrigin header.ordered
      let f := field.dependencyOrigin formed
      let m := major.dependencyOrigin formed
      .rule [f, m, reserveOrigin (projectionDependencyReserve registered index h.weight f.weight m.weight +
        parameterDependencyReserve (info.nparams + index) h.weight parameters f.weight m.weight +
        routedParameterDependencyReserve (info.nparams + max info.nindices index)
          h.weight parameters f.weight m.weight)]
  | .convert plan term => .rule [term.dependencyOrigin formed, plan.dependencyOrigin formed]

@[simp] theorem EndpointState.dependencyOrigin_cast (formed : env.Ordered)
    (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U source expression type) :
    (node.cast expressionEq typeEq).dependencyOrigin formed = node.dependencyOrigin formed := by
  cases expressionEq; cases typeEq; rfl

noncomputable def ContextDerivation.dependencyClosures (formed : env.Ordered) :
    ContextDerivation env U source → List Closure
  | .nil => []
  | .cons tail domain => .close (domain.dependencyOrigin formed) (tail.dependencyClosures formed) ::
      tail.dependencyClosures formed

theorem Derivation.expose_dependency_weight_le (formed : env.Ordered)
    (original : Derivation env U source left right type) :
    (original.expose.1.dependencyOrigin formed).weight ≤ (original.dependencyOrigin formed).weight ∧
    (original.expose.2.dependencyOrigin formed).weight ≤ (original.dependencyOrigin formed).weight := by
  induction original <;> constructor <;>
    simp only [expose, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin,
      EndpointConversion.dependencyOrigin] at *
  all_goals first | exact Nat.le_refl _ | skip
  all_goals conv => rhs; rw [dependencyOrigin.eq_def]
  all_goals simp only [etaBody, EndpointState.dependencyOrigin_cast,
    EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, dependencyBetaLeftOrigin,
    dependencyEtaLeftOrigin, dependencyEtaBodyOrigin, capturedApplicationOrigin, lambdaOrigin,
    Origin.weight, projectionDependencyReserve, reserveOrigin_weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
  all_goals try omega
  all_goals
    rename_i name info levels params index sourceMajor fieldType source fieldLevel major indexArgs major'
      registered wf lc pc ic selected fw field left right closed allowed ihf ihl ihr
    have leftReserve := projectionFamilyReserve_mono (count := info.nparams + info.nindices)
      (Nat.le_refl (field.dependencyOrigin formed).weight)
      (Nat.le_add_right (left.dependencyOrigin formed).weight (right.dependencyOrigin formed).weight)
    have rightReserve := projectionFamilyReserve_mono (count := info.nparams + info.nindices)
      (Nat.le_refl (field.dependencyOrigin formed).weight)
      (Nat.le_add_left (right.dependencyOrigin formed).weight (left.dependencyOrigin formed).weight)
    have leftParameters := parameterDependencyReserve_mono
      (headerBound := Nat.le_refl ((selectOriginalHeader formed (formed.projectionConstructor registered) wf).original.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) wf).ordered).weight)
      (equalityBound := Nat.le_refl ((projectionParameterDependencies formed registered wf).map
        fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
      (fieldBound := Nat.le_refl (field.dependencyOrigin formed).weight)
      (majorBound := Nat.le_add_right (left.dependencyOrigin formed).weight (right.dependencyOrigin formed).weight)
      (count := info.nparams + index)
    have rightParameters := parameterDependencyReserve_mono
      (headerBound := Nat.le_refl ((selectOriginalHeader formed (formed.projectionConstructor registered) wf).original.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) wf).ordered).weight)
      (equalityBound := Nat.le_refl ((projectionParameterDependencies formed registered wf).map
        fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
      (fieldBound := Nat.le_refl (field.dependencyOrigin formed).weight)
      (majorBound := Nat.le_add_left (right.dependencyOrigin formed).weight (left.dependencyOrigin formed).weight)
      (count := info.nparams + index)
    have leftRoutes := routedParameterDependencyReserve_mono
      (headerBound := Nat.le_refl ((selectOriginalHeader formed (formed.projectionConstructor registered) wf).original.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) wf).ordered).weight)
      (equalityBound := Nat.le_refl ((projectionParameterDependencies formed registered wf).map
        fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
      (fieldBound := Nat.le_refl (field.dependencyOrigin formed).weight)
      (majorBound := Nat.le_add_right (left.dependencyOrigin formed).weight (right.dependencyOrigin formed).weight)
      (count := info.nparams + max info.nindices index)
    have rightRoutes := routedParameterDependencyReserve_mono
      (headerBound := Nat.le_refl ((selectOriginalHeader formed (formed.projectionConstructor registered) wf).original.dependencyOrigin
        (selectOriginalHeader formed (formed.projectionConstructor registered) wf).ordered).weight)
      (equalityBound := Nat.le_refl ((projectionParameterDependencies formed registered wf).map
        fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
      (fieldBound := Nat.le_refl (field.dependencyOrigin formed).weight)
      (majorBound := Nat.le_add_left (right.dependencyOrigin formed).weight (left.dependencyOrigin formed).weight)
      (count := info.nparams + max info.nindices index)
    omega

theorem EndpointRef.expose_dependency_weight_le (formed : env.Ordered)
    (reference : EndpointRef env U source expression type) :
    (reference.expose.dependencyOrigin formed).weight ≤ (reference.dependencyOrigin formed).weight := by
  cases reference with
  | left original => exact original.expose_dependency_weight_le formed |>.1
  | right original => exact original.expose_dependency_weight_le formed |>.2

theorem Derivation.typeFormation_dependency_weight_le (formed : env.Ordered)
    (original : Derivation env U source left right type) :
    (original.typeFormation.node.dependencyOrigin formed).weight ≤ (original.dependencyOrigin formed).weight := by
  induction original <;>
    simp only [typeFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin] at *
  all_goals conv => rhs; rw [dependencyOrigin.eq_def]
  all_goals simp only [dependencyBetaLeftOrigin, dependencyEtaLeftOrigin, dependencyEtaBodyOrigin,
    capturedApplicationOrigin, lambdaOrigin, Origin.weight, projectionDependencyReserve, reserveOrigin_weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
  all_goals omega

theorem EndpointRef.typeFormation_dependency_weight_le (formed : env.Ordered)
    (reference : EndpointRef env U source expression type) :
    (reference.typeFormation.node.dependencyOrigin formed).weight ≤ (reference.dependencyOrigin formed).weight := by
  cases reference with
  | left original => exact original.typeFormation_dependency_weight_le formed
  | right original => exact original.typeFormation_dependency_weight_le formed

theorem EndpointConversion.targetFormation_dependency_weight_le (formed : env.Ordered)
    (plan : EndpointConversion env U source A B) :
    (plan.targetFormation.node.dependencyOrigin formed).weight ≤ (plan.dependencyOrigin formed).weight := by
  cases plan <;>
    simp only [targetFormation, EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin,
      dependencyOrigin, Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.add_mul, Nat.mul_add, Nat.mul_one] <;> omega

theorem EndpointState.typeFormation_dependency_weight_le (formed : env.Ordered)
    (node : EndpointState env U source expression assigned) :
    (node.typeFormation.node.dependencyOrigin formed).weight ≤ (node.dependencyOrigin formed).weight := by
  cases node with
  | ref reference => exact reference.typeFormation_dependency_weight_le formed
  | convert plan term =>
    have bound := plan.targetFormation_dependency_weight_le formed
    simp only [typeFormation, dependencyOrigin, Origin.weight, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  | _ =>
    simp only [typeFormation, dependencyOrigin, capturedApplicationOrigin, Origin.weight,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_mul, Nat.mul_add, Nat.mul_one] <;> omega

theorem EndpointState.typeFormation_dependency_cost_le (formed : env.Ordered)
    (node : EndpointState env U source expression assigned) (captured : List Closure) :
    (Closure.close (node.typeFormation.node.dependencyOrigin formed) captured).cost ≤
      (Closure.close (node.dependencyOrigin formed) captured).cost :=
  Nat.mul_le_mul_right (1 + environmentCost captured) (node.typeFormation_dependency_weight_le formed)

/-- The application retains this finite formation view strictly below its
own captured-argument reserve. Its children are the original app children. -/
theorem EndpointState.appPiFormation_dependency_cost_lt
    (formed : env.Ordered) (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState env U source A (.sort u))
    (body : EndpointState env U (A :: source) B (.sort v))
    (function : EndpointState env U source f (.forallE A B))
    (argument : EndpointState env U source a A)
    (result : EndpointState env U source (B.inst a) (.sort v))
    (captured : List Closure) :
    (Closure.close ((EndpointState.pi hu hv domain body).dependencyOrigin formed) captured).cost <
      (Closure.close ((EndpointState.app hu hv domain body function argument result).dependencyOrigin formed) captured).cost := by
  apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  have positive := (function.dependencyOrigin formed).weight_pos
  simp only [EndpointState.dependencyOrigin, applicationOrigin, Origin.weight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

noncomputable def Located.dependencyEnvironment {env : VEnv}
    {root : EndpointRef env U source expression type}
    {selected : EndpointState env U context selectedExpression selectedType} (formed : env.Ordered)
    (location : Located root selected) (initial : List Closure) : List Closure :=
  match location with
  | .here => initial
  | .expose parent | .convertTerm parent | .appFunction parent | .appArgument parent |
      .appDomain parent | .appResult parent | .appPiFormation parent | .lamDomain parent | .piDomain parent |
      .projField parent | .projMajor parent | .assignedFormation parent =>
      parent.dependencyEnvironment formed initial
  | .lamBody (domain := domain) parent | .lamCodomain (domain := domain) parent |
      .appCodomain (domain := domain) parent | .piBody (domain := domain) parent =>
      .close (domain.dependencyOrigin formed) (parent.dependencyEnvironment formed initial) ::
        parent.dependencyEnvironment formed initial

theorem Located.dependency_cost_le {env : VEnv}
    {root : EndpointRef env U source expression type}
    {selected : EndpointState env U context selectedExpression selectedType} (formed : env.Ordered)
    (location : Located root selected) (initial : List Closure) :
    (Closure.close (selected.dependencyOrigin formed) (location.dependencyEnvironment formed initial)).cost ≤
      (Closure.close (root.dependencyOrigin formed) initial).cost := by
  induction location with
  | here => exact Nat.le_refl _
  | expose parent ih =>
    exact Nat.le_trans
      (Nat.mul_le_mul_right (1 + environmentCost (parent.dependencyEnvironment formed initial))
        (EndpointRef.expose_dependency_weight_le formed _)) ih
  | appPiFormation parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (EndpointState.appPiFormation_dependency_cost_lt formed _ _ _ _ _ _ _
      (parent.dependencyEnvironment formed initial))) ih
  | assignedFormation parent ih =>
    exact Nat.le_trans (EndpointState.typeFormation_dependency_cost_le formed _ _) ih
  | convertTerm parent ih | projField parent ih | projMajor parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (original_child_same_environment
      (Origin.rule_child (by simp [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin])) (parent.dependencyEnvironment formed initial))) ih
  | appFunction parent ih | appArgument parent ih | appResult parent ih =>
    apply Nat.le_trans (Nat.le_trans ?_ (application_cost_le_captured _ _ _ _ _ _)) ih
    exact Nat.le_of_lt (binder_other_cost (by simp) (parent.dependencyEnvironment formed initial))
  | appDomain parent ih =>
    apply Nat.le_trans (Nat.le_trans ?_ (application_cost_le_captured _ _ _ _ _ _)) ih
    exact Nat.le_of_lt (binder_domain_cost _ _ _ (parent.dependencyEnvironment formed initial))
  | appCodomain parent ih =>
    apply Nat.le_trans (Nat.le_trans ?_ (application_cost_le_captured _ _ _ _ _ _)) ih
    exact Nat.le_of_lt (binder_body_cost (by simp) (parent.dependencyEnvironment formed initial))
  | lamDomain parent ih | piDomain parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_domain_cost _ _ _ (parent.dependencyEnvironment formed initial))) ih
  | lamBody parent ih | lamCodomain parent ih | piBody parent ih =>
    exact Nat.le_trans (Nat.le_of_lt (binder_body_cost (by simp) (parent.dependencyEnvironment formed initial))) ih

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
