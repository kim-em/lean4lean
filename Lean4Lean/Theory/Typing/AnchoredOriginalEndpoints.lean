import Lean4Lean.Theory.Typing.AnchoredOriginalDerivation

/-! Lazy endpoint exposure of the actual original derivation tree. References
retain their original side and assigned type. Synthetic beta/eta syntax and
right-endpoint conversions contain those references, rather than pretending
that an extracted or weakened typing derivation was an original premise.

Exposure is computed from the referenced tree. Its children remain references,
so shared formation premises are not expanded into a duplicate proof tree.
The resulting structural exposure is raw-sound and its finite original
ledger fits within the original derivation reserve.
-/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- Every equality leaf is an original equality premise. The Pi-domain plan
is the finite conversion required by the right endpoint of lamDF; its three
premises are retained independently and remain original references. -/
inductive EndpointConversion (env : VEnv) (U : Nat) :
    List VExpr → VExpr → VExpr → Type where
  | forward (levelWF : level.WF U)
      (original : Derivation env U Γ A B (.sort level)) :
      EndpointConversion env U Γ A B
  | backward (levelWF : level.WF U)
      (original : Derivation env U Γ A B (.sort level)) :
      EndpointConversion env U Γ B A
  | piDomain (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : Derivation env U Γ A A' (.sort u))
      (body : Derivation env U (A :: Γ) B B (.sort v))
      (otherBody : Derivation env U (A' :: Γ) B B (.sort v)) :
      EndpointConversion env U Γ (.forallE A' B) (.forallE A B)

theorem EndpointConversion.sound (plan : EndpointConversion env U Γ A B) :
    ∃ level, level.WF U ∧ env.IsDefEqStrong U Γ A B (.sort level) := by
  cases plan with
  | forward levelWF original => exact ⟨_, levelWF, original.forget⟩
  | backward levelWF original => exact ⟨_, levelWF, original.forget.symm⟩
  | piDomain domainWF bodyWF domain body otherBody =>
    exact ⟨.imax _ _, ⟨domainWF, bodyWF⟩,
      .forallEDF domainWF bodyWF domain.forget.symm otherBody.forget body.forget⟩

/-- Reversing an original equality keeps its original reserve. The synthetic
Pi comparison retains both original body contexts explicitly. -/
def EndpointConversion.origin : EndpointConversion env U Γ A B → Origin
  | .forward _ original | .backward _ original => original.origin
  | .piDomain _ _ domain body otherBody =>
      .binder domain.origin [otherBody.origin, body.origin] []

/-- Finite exposure states. `ref` is a lazy pointer to an actual original
endpoint, not an opaque boundary: `EndpointRef.expose` below handles every
original rule. Other states are just the finite syntax introduced by exposure.
Their raw soundness is never fed back as an original semantic premise. -/
inductive EndpointState (env : VEnv) (U : Nat) :
    List VExpr → VExpr → VExpr → Type where
  | ref (reference : EndpointRef env U Γ expression type) :
      EndpointState env U Γ expression type
  | sort (levelWF : level.WF U) :
      EndpointState env U Γ (.sort level) (.sort level.succ)
  | bvar (lookup : Lookup Γ index A) (levelWF : level.WF U)
      (formation : EndpointState env U Γ A (.sort level)) :
      EndpointState env U Γ (.bvar index) A
  | app (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : EndpointState env U Γ A (.sort u))
      (codomain : EndpointState env U (A :: Γ) B (.sort v))
      (function : EndpointState env U Γ f (.forallE A B))
      (argument : EndpointState env U Γ a A)
      (result : EndpointState env U Γ (B.inst a) (.sort v)) :
      EndpointState env U Γ (.app f a) (B.inst a)
  | lam (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : EndpointState env U Γ A (.sort u))
      (codomain : EndpointState env U (A :: Γ) B (.sort v))
      (body : EndpointState env U (A :: Γ) expression B) :
      EndpointState env U Γ (.lam A expression) (.forallE A B)
  | pi (domainWF : u.WF U) (bodyWF : v.WF U)
      (domain : EndpointState env U Γ A (.sort u))
      (body : EndpointState env U (A :: Γ) B (.sort v)) :
      EndpointState env U Γ (.forallE A B) (.sort (.imax u v))
  | proj
      (registered : env.projections name info)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (levelCount : levels.length = info.uvars)
      (parameterCount : parameters.length = info.nparams)
      (indexCount : indices.length = info.nindices)
      (selected : info.fieldType name levels parameters index sourceMajor = some fieldType)
      (fieldWF : fieldLevel.WF U)
      (field : EndpointState env U Γ fieldType (.sort fieldLevel))
      (major : Derivation env U Γ sourceMajor expression
        (mkApps (.const name levels) (parameters ++ indices)))
      (closed : info.ctorType.Closed)
      (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) :
      EndpointState env U Γ (.proj name index expression) fieldType
  | convert (plan : EndpointConversion env U Γ A B)
      (term : EndpointState env U Γ expression A) :
      EndpointState env U Γ expression B

theorem EndpointState.sound (node : EndpointState env U Γ expression type) :
    env.IsDefEqStrong U Γ expression expression type := by
  induction node with
  | ref reference => exact reference.sound
  | sort levelWF => exact .sortDF levelWF levelWF rfl
  | bvar lookup levelWF _ ih => exact .bvar lookup levelWF ih
  | app hu hv _ _ _ _ _ ihA ihB ihF ihArg ihResult =>
    exact .appDF hu hv ihA ihB ihF ihArg ihResult
  | lam hu hv _ _ _ ihA ihB ihBody => exact .lamDF hu hv ihA ihB ihB ihBody ihBody
  | pi hu hv _ _ ihA ihB => exact .forallEDF hu hv ihA ihB ihB
  | proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field major closed relevance ih =>
    exact .projDF registered levelsWF levelCount parameterCount indexCount selected fieldWF
      ih major.forget major.forget closed relevance
  | convert plan _ ih =>
    obtain ⟨_, levelWF, equality⟩ := plan.sound
    exact .defeqDF levelWF equality ih

/-- Every binder reserves its original domain-type closure. References used
twice in a synthetic view are counted twice; conversions retain both the
term and equality ledgers rather than relying on proof identity. -/
def EndpointState.origin : EndpointState env U Γ expression type → Origin
  | .ref reference => reference.origin
  | .sort _ => .rule []
  | .bvar _ _ formation => .rule [formation.origin]
  | .app _ _ domain codomain function argument result =>
      .binder domain.origin [codomain.origin]
        [function.origin, argument.origin, result.origin]
  | .lam _ _ domain codomain body => .binder domain.origin [codomain.origin, body.origin] []
  | .pi _ _ domain body => .binder domain.origin [body.origin] []
  | .proj _ _ _ _ _ _ _ field major _ _ => .rule [field.origin, major.origin]
  | .convert plan term => .rule [term.origin, plan.origin]

/-- Index equalities preserve the finite endpoint ledger. -/
def EndpointState.cast (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U Γ expression type) : EndpointState env U Γ expression' type' :=
  expressionEq ▸ typeEq ▸ node

@[simp] theorem EndpointState.origin_cast
    (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U Γ expression type) :
    (node.cast expressionEq typeEq).origin = node.origin := by
  cases expressionEq
  cases typeEq
  rfl

/-- Only syntax with no source expression children can remain an original
reference after one exposure. Variables expose their original formation child. -/
def EndpointAtomic : VExpr → Prop
  | .sort .. | .const .. | .elim .. => True
  | _ => False

/-- Primitive atomic endpoints retain the WHOLE original rule. In particular
the right constDF/elimDF reference retains its original ambient header-type
equality; a consumer must read that child when passing to the natural type at
the displayed levels. It may not silently identify that type with the stored
assigned type. No composite original derivation is an exposed atomic leaf. -/
def Derivation.PrimitiveHead : Derivation env U Γ left right type → Prop
  | .sortDF .. | .constDF .. | .elimDF .. => True
  | _ => False

def EndpointRef.Primitive : EndpointRef env U Γ expression type → Prop
  | .left original | .right original => original.PrimitiveHead

theorem EndpointRef.primitive_atomic (reference : EndpointRef env U Γ expression type)
    (primitive : reference.Primitive) : EndpointAtomic expression := by
  cases reference <;> rename_i original <;> cases original <;>
    simp_all only [Primitive, Derivation.PrimitiveHead, EndpointAtomic]

def EndpointState.Exposed : EndpointState env U Γ expression type → Prop
  | .ref reference => reference.Primitive
  | _ => True

private def etaBody
    {env : VEnv} {U : Nat} {Γ : List VExpr} {A B expression : VExpr}
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (codomain : Derivation env U (A :: Γ) B B (.sort v))
    (liftedCodomain : Derivation env U (A.lift :: A :: Γ)
      (B.liftN 1 1) (B.liftN 1 1) (.sort v))
    (liftedTerm : Derivation env U (A :: Γ) expression.lift expression.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation env U (A :: Γ) A.lift A.lift (.sort u)) :
    EndpointState env U (A :: Γ) (.app expression.lift (.bvar 0)) B :=
  .cast rfl (inst_liftN_bvar B 0)
    (.app domainWF bodyWF (.ref (.left liftedDomain))
      (.ref (.left liftedCodomain)) (.ref (.left liftedTerm))
      (.bvar .zero domainWF (.ref (.left liftedDomain)))
      (.cast (inst_liftN_bvar B 0).symm rfl (.ref (.left codomain))))

private theorem etaBody_origin
    {env : VEnv} {U : Nat} {Γ : List VExpr} {A B expression : VExpr}
    (domainWF : u.WF U) (bodyWF : v.WF U)
    (codomain : Derivation env U (A :: Γ) B B (.sort v))
    (liftedCodomain : Derivation env U (A.lift :: A :: Γ)
      (B.liftN 1 1) (B.liftN 1 1) (.sort v))
    (liftedTerm : Derivation env U (A :: Γ) expression.lift expression.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation env U (A :: Γ) A.lift A.lift (.sort u)) :
    (etaBody domainWF bodyWF codomain liftedCodomain liftedTerm liftedDomain).origin =
      etaBodyOrigin codomain.origin liftedCodomain.origin liftedTerm.origin liftedDomain.origin := by
  simp only [etaBody, EndpointState.origin_cast, EndpointState.origin, EndpointRef.origin, etaBodyOrigin]

/-- Expose both endpoints together by recursion on the original data tree.
No endpoint-typing proof is reified or used as a fresh recursive input. -/
def Derivation.expose (original : Derivation env U Γ left right type) :
    EndpointState env U Γ left type × EndpointState env U Γ right type :=
  match original with
  | .bvar lookup hu formation =>
      let observedVariable := EndpointState.bvar lookup hu (.ref (.left formation))
      (observedVariable, observedVariable)
  | .symm original => (original.expose.2, original.expose.1)
  | .trans first second => (first.expose.1, second.expose.2)
  | primitive@(.sortDF ..) => (.ref (.left primitive), .ref (.right primitive))
  | primitive@(.constDF ..) => (.ref (.left primitive), .ref (.right primitive))
  | primitive@(.elimDF ..) => (.ref (.left primitive), .ref (.right primitive))
  | .appDF hu hv domain codomain function argument result =>
      (.app hu hv (.ref (.left domain)) (.ref (.left codomain))
        (.ref (.left function)) (.ref (.left argument)) (.ref (.left result)),
       .convert (.backward hv result)
        (.app hu hv (.ref (.left domain)) (.ref (.left codomain))
          (.ref (.right function)) (.ref (.right argument)) (.ref (.right result))))
  | .projDF registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field leftMajor rightMajor closed relevance =>
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref (.left field)) leftMajor closed relevance,
       .proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
        (.ref (.left field)) rightMajor closed relevance)
  | .lamDF hu hv domain codomain otherCodomain body otherBody =>
      (.lam hu hv (.ref (.left domain)) (.ref (.left codomain)) (.ref (.left body)),
       .convert (.piDomain hu hv domain codomain otherCodomain)
        (.lam hu hv (.ref (.right domain)) (.ref (.left otherCodomain)) (.ref (.right otherBody))))
  | .forallEDF hu hv domain body otherBody =>
      (.pi hu hv (.ref (.left domain)) (.ref (.left body)),
       .pi hu hv (.ref (.right domain)) (.ref (.right otherBody)))
  | .defeqDF hu types terms =>
      (.convert (.forward hu types) (.ref (.left terms)),
       .convert (.forward hu types) (.ref (.right terms)))
  | .beta hu hv domain codomain body argument result instantiated =>
      (.app hu hv (.ref (.left domain)) (.ref (.left codomain))
        (.lam hu hv (.ref (.left domain)) (.ref (.left codomain)) (.ref (.left body)))
        (.ref (.left argument)) (.ref (.left result)),
       instantiated.expose.1)
  | .eta hu hv domain codomain liftedCodomain term liftedTerm liftedDomain =>
      (.lam hu hv (.ref (.left domain)) (.ref (.left codomain))
        (etaBody hu hv codomain liftedCodomain liftedTerm liftedDomain),
       term.expose.1)
  | .proofIrrel _ left right => (left.expose.1, right.expose.1)
  | .extra _ _ _ _ _ _ _ left right => (left.expose.1, right.expose.1)
  | .elimIota _ _ _ _ _ _ _ left right => (left.expose.1, right.expose.1)
  | .projIota _ projection _ field => (projection.expose.1, field.expose.1)
  | .structEta _ _ _ major constructor => (constructor.expose.1, major.expose.1)
  | .unitLike _ _ _ _ left right => (left.expose.1, right.expose.1)

theorem Derivation.expose_exposed (original : Derivation env U Γ left right type) :
    original.expose.1.Exposed ∧ original.expose.2.Exposed := by
  induction original with
  | symm original ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩
  | beta _ _ _ _ _ _ _ instantiated _ _ _ _ _ ih => exact ⟨trivial, ih.1⟩
  | eta _ _ _ _ _ term _ _ _ _ _ ih _ _ => exact ⟨trivial, ih.1⟩
  | proofIrrel _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra _ _ _ _ _ _ _ left right _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | elimIota _ _ _ _ _ _ _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | projIota _ projection _ field ihProjection ihField => exact ⟨ihProjection.1, ihField.1⟩
  | structEta _ _ _ major constructor ihMajor ihConstructor => exact ⟨ihConstructor.1, ihMajor.1⟩
  | unitLike _ _ _ _ left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | _ => exact ⟨trivial, trivial⟩

/-- Structural exposure never exceeds the reserve of its actual original
source tree, including each original equality retained by a conversion. -/
theorem Derivation.expose_weight_le (original : Derivation env U Γ left right type) :
    original.expose.1.origin.weight ≤ original.origin.weight ∧
      original.expose.2.origin.weight ≤ original.origin.weight := by
  induction original <;>
    simp only [expose, origin, EndpointState.origin, EndpointRef.origin,
      EndpointConversion.origin, etaBody_origin, applicationOrigin, lambdaOrigin,
      betaLeftOrigin, etaLeftOrigin, etaBodyOrigin, Origin.weight, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_mul,
      Nat.mul_add, Nat.mul_one, Nat.one_mul] at * <;> omega

def EndpointRef.expose : EndpointRef env U Γ expression type → EndpointState env U Γ expression type
  | .left original => original.expose.1
  | .right original => original.expose.2

theorem EndpointRef.expose_exposed (reference : EndpointRef env U Γ expression type) :
    reference.expose.Exposed := by
  cases reference with
  | left original => exact original.expose_exposed.1
  | right original => exact original.expose_exposed.2

theorem EndpointRef.expose_weight_le (reference : EndpointRef env U Γ expression type) :
    reference.expose.origin.weight ≤ reference.origin.weight := by
  cases reference with
  | left original => exact original.expose_weight_le.1
  | right original => exact original.expose_weight_le.2

/-- A root-indexed exposure contains the uniquely computed state. Consumers
can retain this equality while traversing original references and finite
synthetic nodes, rather than accepting an arbitrary decorated view. -/
structure EndpointExposure (reference : EndpointRef env U Γ expression type) where
  node : EndpointState env U Γ expression type
  exactState : node = reference.expose

def EndpointRef.exposure (reference : EndpointRef env U Γ expression type) :
    EndpointExposure reference := ⟨reference.expose, rfl⟩

theorem EndpointExposure.exposed
    {reference : EndpointRef env U Γ expression type} (exposure : EndpointExposure reference) :
    exposure.node.Exposed := exposure.exactState ▸ reference.expose_exposed

theorem EndpointExposure.sound
    {reference : EndpointRef env U Γ expression type} (exposure : EndpointExposure reference) :
    env.IsDefEqStrong U Γ expression expression type := exposure.node.sound

theorem EndpointExposure.weight_le
    {reference : EndpointRef env U Γ expression type} (exposure : EndpointExposure reference) :
    exposure.node.origin.weight ≤ reference.origin.weight := by
  rw [exposure.exactState]
  exact reference.expose_weight_le

/-- Exposure inherits exactly the caller's captured source environment. -/
theorem EndpointExposure.cost_le
    {reference : EndpointRef env U Γ expression type} (exposure : EndpointExposure reference)
    (captured : List Closure) :
    (Closure.close exposure.node.origin captured).cost ≤
      (Closure.close reference.origin captured).cost :=
  Nat.mul_le_mul_right (1 + environmentCost captured) exposure.weight_le

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
