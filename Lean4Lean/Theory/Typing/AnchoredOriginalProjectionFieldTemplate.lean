import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionQuery
import Lean4Lean.Theory.Typing.AnchoredConstantSyntax
import Lean4Lean.Theory.Typing.ProjectionIndexBound

/-! The shared declaration template of two actual projection fields. Its
raw domain is selected before universe instantiation. Each side keeps its
own universes, parameters and hidden source major. Only syntactic scope is
asserted for the sparse capture list; no typing of every prior projection
or of the residual declaration context is manufactured. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
open private projectionParams_shape projectionFields_bound from
  Lean4Lean.Theory.Typing.ProjectionIndexBound
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- A complete raw constructor telescope with its actual selected field.
The constructor shape and successful projection selection determine the
index bound. No formation of an instantiated prefix is part of this data. -/
structure ProjectionFieldTemplate (info : VProjectionInfo) (index : Nat) where
  domains : List VExpr
  result : VExpr
  constructor_eq : info.ctorType = wrapForalls domains result
  length_eq : domains.length = info.nparams + info.numFields
  selected_bound : info.nparams + index < domains.length

namespace ProjectionFieldTemplate

def domain (template : ProjectionFieldTemplate info index) : VExpr :=
  template.domains[info.nparams + index]'template.selected_bound

theorem closed (template : ProjectionFieldTemplate info index)
    (constructorClosed : info.ctorType.Closed) :
    template.domain.ClosedN (info.nparams + index) :=
  (ConstantTelescope.mk template.domains template.result template.constructor_eq).domain_scope
    constructorClosed (List.getElem?_eq_getElem template.selected_bound)

def changeInfo (template : ProjectionFieldTemplate info index) (equal : info = other) :
    ProjectionFieldTemplate other index where
  domains := template.domains
  result := template.result
  constructor_eq := by simpa only [← equal] using template.constructor_eq
  length_eq := by simpa only [← equal] using template.length_eq
  selected_bound := by simpa only [← equal] using template.selected_bound

theorem changeInfo_domain (template : ProjectionFieldTemplate info index) (equal : info = other) :
    (template.changeInfo equal).domain = template.domain := by
  cases equal
  rfl

end ProjectionFieldTemplate

namespace ProjectionHead
variable {node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned}

/-- The actual source operands, in declaration order. In particular the
prior projections use the stored source major of this very original rule. -/
def templateCaptures (head : ProjectionHead node) : List VExpr :=
  head.parameters ++ (List.range index).map (fun prior => .proj name prior head.sourceMajor)

theorem templateCaptures_length (head : ProjectionHead node) :
    head.templateCaptures.length = head.info.nparams + index := by
  simp only [templateCaptures, List.length_append, List.length_map, List.length_range,
    head.parameterCount]

/-- Existence is derived from the original environment's registered raw
constructor shape and the successful field selection of this head. -/
theorem fieldTemplate_exists (head : ProjectionHead node) (ordered : sourceEnv.Ordered) :
    Nonempty (ProjectionFieldTemplate head.info index) := by
  obtain ⟨decl, type, ctor, _, _, _, _, _, parameterCount, _, _, _, ctorType,
    _, _, _, raw, _⟩ := ordered.projectionShape head.registered
  obtain ⟨domains, result, shape, parametersFit, _, resultHead, arity⟩ := raw.forallArity
  have result_eq : result = mkApps (.const type.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← resultHead]
    exact (mkApps_getAppFnArgs_eq result).symm
  have selected := head.selected
  unfold VProjectionInfo.fieldType at selected
  split at selected <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨tail, parameters, fields⟩ := selected
  rw [← ctorType, shape, result_eq, instL_wrapForalls, instL_mkApps] at parameters
  obtain ⟨remaining, arguments, rfl, remainingLength⟩ := projectionParams_shape parameters
  have fieldBound := projectionFields_bound fields
  simp only [Nat.zero_add] at fieldBound
  simp only [List.length_map] at remainingLength
  have length_eq : domains.length = head.info.nparams + head.info.numFields := by
    rw [VProjectionInfo.numFields, ← ctorType, arity]
    omega
  refine ⟨⟨domains, result, ctorType.symm.trans shape, length_eq, ?_⟩⟩
  have count := head.parameterCount
  omega

noncomputable def fieldTemplate (head : ProjectionHead node) (ordered : sourceEnv.Ordered) :
    ProjectionFieldTemplate head.info index := Classical.choice (head.fieldTemplate_exists ordered)

/-- The rich field retains its actual original endpoint. This equality
merely describes its expression using the selected raw declaration domain. -/
theorem fieldTemplate_eq (head : ProjectionHead node)
    (template : ProjectionFieldTemplate head.info index) :
    head.fieldType = (template.domain.instL head.levels).instOuter head.templateCaptures := by
  exact Option.some.inj (head.selected.symm.trans
    (head.info.fieldType_eq_instOuter template.constructor_eq head.levelCount
      head.parameterCount template.selected_bound))

theorem fieldTemplate_closed (head : ProjectionHead node)
    (template : ProjectionFieldTemplate head.info index) :
    (template.domain.instL head.levels).ClosedN head.templateCaptures.length := by
  rw [head.templateCaptures_length]
  exact (template.closed head.closed).instL

/-- Substitution form for the local template interpreter. The raw capture
substitution is not asserted to be a typed substitution for a full header. -/
theorem fieldTemplate_subst (head : ProjectionHead node)
    (template : ProjectionFieldTemplate head.info index) :
    head.fieldType = (template.domain.instL head.levels).subst (Subst.ofList head.templateCaptures) := by
  rw [head.fieldTemplate_eq template, instOuter_eq_subst]

end ProjectionHead

/-- Two actual heads share the same pre-universe constructor domain through
ambient registration uniqueness. Their independently instantiated domains
and sparse operand lists are kept separate. -/
structure SharedProjectionFieldTemplate
    (leftHead : ProjectionHead (left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType))
    (rightHead : ProjectionHead (right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType)) where
  info_eq : leftHead.info = rightHead.info
  template : ProjectionFieldTemplate leftHead.info index

namespace SharedProjectionFieldTemplate

variable {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
  {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
  {leftHead : ProjectionHead left} {rightHead : ProjectionHead right}

def domain (shared : SharedProjectionFieldTemplate leftHead rightHead) : VExpr := shared.template.domain

def rightTemplate (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    ProjectionFieldTemplate rightHead.info index := shared.template.changeInfo shared.info_eq

theorem left_eq (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    leftHead.fieldType = (shared.domain.instL leftHead.levels).instOuter leftHead.templateCaptures :=
  leftHead.fieldTemplate_eq shared.template

theorem right_eq (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    rightHead.fieldType = (shared.domain.instL rightHead.levels).instOuter rightHead.templateCaptures := by
  have equal := rightHead.fieldTemplate_eq shared.rightTemplate
  simpa only [rightTemplate, ProjectionFieldTemplate.changeInfo_domain, domain] using equal

theorem closed (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    shared.domain.ClosedN (leftHead.info.nparams + index) := shared.template.closed leftHead.closed

theorem left_closed (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    (shared.domain.instL leftHead.levels).ClosedN leftHead.templateCaptures.length :=
  leftHead.fieldTemplate_closed shared.template

theorem right_closed (shared : SharedProjectionFieldTemplate leftHead rightHead) :
    (shared.domain.instL rightHead.levels).ClosedN rightHead.templateCaptures.length := by
  have scope := rightHead.fieldTemplate_closed shared.rightTemplate
  simpa only [rightTemplate, ProjectionFieldTemplate.changeInfo_domain, domain] using scope

end SharedProjectionFieldTemplate

/-- Concrete paired extraction uses actual registrations in one ambient
ordered environment. It assumes neither equality of the universe packets
nor typing of unused prior projections. -/
noncomputable def ProjectionHead.sharedFieldTemplate
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (leftOrdered : leftEnv.Ordered) (henv : env.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env) :
    SharedProjectionFieldTemplate leftHead rightHead where
  info_eq := henv.projections_unique (leftBelow.projections leftHead.registered)
    (rightBelow.projections rightHead.registered)
  template := leftHead.fieldTemplate leftOrdered

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
