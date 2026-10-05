import Lean4Lean.Theory.Typing.AnchoredEliminatorMetadata
import Lean4Lean.Theory.Typing.AnchoredOriginalConstantCase
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReturn

/-! Abstract eliminators have one literal header only under the metadata
uniqueness supplied by fresh staged registration. Ordered environments alone
do not provide that invariant. All semantic calls below are retained original
ambient equalities or original conversion-prefix children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure EliminatorHeader (env : VEnv) (block : Name) (index : Nat) where
  schema : InductiveSignature.CaseSchema
  registered : env.eliminators block schema
  owner : Fin schema.signature.families.size
  owner_eq : owner.val = index
  type : VExpr
  selected : schema.genericType owner = some type
  closed : type.Closed

def EliminatorHeader.mono (header : EliminatorHeader source block index) (below : source ≤ env) :
    EliminatorHeader env block index :=
  { header with registered := below.eliminators header.registered }

theorem EliminatorHeader.type_eq (unique : env.EliminatorsUnique)
    (left right : EliminatorHeader env block index) : left.type = right.type := by
  rcases left with ⟨leftSchema, leftRegistered, leftOwner, leftIndex, leftType, leftSelected, leftClosed⟩
  rcases right with ⟨rightSchema, rightRegistered, rightOwner, rightIndex, rightType, rightSelected, rightClosed⟩
  have same := unique leftRegistered rightRegistered
  cases same
  have ownerSame : leftOwner = rightOwner := Fin.ext (leftIndex.trans rightIndex.symm)
  cases ownerSame
  exact Option.some.inj (leftSelected.symm.trans rightSelected)

inductive EliminatorCall :
    (reference : EndpointRef sourceEnv U source expression assigned) →
    {context : List VExpr} → {left right type : VExpr} →
      Derivation sourceEnv U context left right type → Type where
  | left : EliminatorCall (.left (.elimDF registered selected closed permission
      levelsWF levelsEqual levelWF ambient)) ambient
  | right : EliminatorCall (.right (.elimDF registered selected closed permission
      levelsWF levelsEqual levelWF ambient)) ambient

def EliminatorCall.contextDerivation
    {context : List VExpr} {left right type : VExpr}
    {reference : EndpointRef sourceEnv U source expression assigned}
    {original : Derivation sourceEnv U context left right type}
    (call : EliminatorCall reference original) (initial : ContextDerivation sourceEnv U source) :
    ContextDerivation sourceEnv U context := by
  cases call <;> exact initial

theorem EliminatorCall.contextDerivation_closures
    {context : List VExpr} {left right type : VExpr}
    {reference : EndpointRef sourceEnv U source expression assigned}
    {original : Derivation sourceEnv U context left right type}
    (call : EliminatorCall reference original) (initial : ContextDerivation sourceEnv U source) :
    (call.contextDerivation initial).closures = initial.closures := by
  cases call <;> rfl

theorem EliminatorCall.cost_lt (call : EliminatorCall reference original) (initial : List Closure) :
    (Closure.close original.origin initial).cost <
      (Closure.close reference.origin initial).cost := by
  cases call <;> exact original_child_same_environment (Origin.rule_child (by simp)) initial

def EliminatorCall.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : EliminatorCall reference original),
    DerivationFundamental env registry (call.contextDerivation initial) original

theorem EndpointRef.eliminatorHeader
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .elim block index levels) (primitive : reference.Primitive) :
    Nonempty (EliminatorHeader sourceEnv block index) := by
  cases reference <;> rename_i original <;>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
  all_goals try contradiction
  all_goals try cases expressionEq
  all_goals exact ⟨⟨_, by assumption, _, rfl, _, by assumption, by assumption⟩⟩

theorem EndpointRef.eliminatorTargetPath
    {sourceEnv env : VEnv} {U : Nat}
    (henv : env.Ordered) (unique : env.EliminatorsUnique) (below : sourceEnv ≤ env)
    {source target : List VExpr} {σ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (header : EliminatorHeader env block index)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .elim block index levels) (primitive : reference.Primitive) :
    TypeConversion env U target (assigned.subst σ) ((header.type.instL levels).subst σ) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual]
      exact .refl
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual]
      exact .single (((Derivation.forget (by assumption)).defeq.mono below).substDF henv
        substitutions.wf hTarget substitutions)

theorem EndpointRef.replayEliminator
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (unique : env.EliminatorsUnique) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    (header : EliminatorHeader env block index)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .elim block index levels) (primitive : reference.Primitive)
    (calls : EliminatorCall.Fundamentals env registry reference initial)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target locals σ σ available assigned
      (header.type.instL levels) profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual]
      have child := (calls .left).left henv hscoped
      exact certificate.transfer_graded henv hscoped hTarget closed
        (child target locals σ σ available closed hTarget substitutions
          (TailPairedFits.diagonal initial fits)).1 resources
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual]
      exact certificate.transfer_graded henv hscoped hTarget closed
        (calls .right target locals σ σ available closed hTarget substitutions
          (TailPairedFits.diagonal initial fits)).1 resources

theorem EndpointRef.restoreEliminator
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (unique : env.EliminatorsUnique) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    (header : EliminatorHeader env block index)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .elim block index levels) (primitive : reference.Primitive)
    (calls : EliminatorCall.Fundamentals env registry reference initial)
    {profile : Profile n} {inputType : VExpr}
    (incoming : CodeTransferResult env U registry target locals leftSubst σ available
      inputType (header.type.instL levels) profile) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst σ available inputType assigned profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual] at incoming
      exact ⟨incoming⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case elimDF.refl =>
      let actual : EliminatorHeader env _ _ :=
        ⟨_, below.eliminators (by assumption), _, rfl, _, by assumption, by assumption⟩
      rw [header.type_eq unique actual] at incoming
      obtain ⟨answer⟩ := incoming.certificate.transfer_graded henv hscoped hTarget closed
        (calls .right target locals σ σ available closed hTarget substitutions
          (TailPairedFits.diagonal initial fits)).2.1 incoming.available
      exact ⟨⟨answer.footprint, answer.certificate, answer.available,
        incoming.related.trans henv answer.related⟩⟩

structure EliminatorPrefix
    (first : EndpointState sourceEnv U source (.elim block index levels) assigned) where
  type : VExpr
  reference : EndpointRef sourceEnv U source (.elim block index levels) type
  route : PrefixRoute sourceEnv U source (.elim block index levels) first (.ref reference)
  primitive : reference.Primitive
  header : EliminatorHeader sourceEnv block index

noncomputable def eliminatorPrefix
    (first : EndpointState sourceEnv U source (.elim block index levels) assigned) :
    EliminatorPrefix first := by
  obtain ⟨type, node, route, head⟩ := prefixHead first
  cases node with
  | ref reference =>
    exact ⟨type, reference, route, head,
      Classical.choice (EndpointRef.eliminatorHeader reference rfl head)⟩
  | convert => exact False.elim head

structure EliminatorDisplayPrefix
    (display : EndpointDisplay env U displayed (.elim block index levels) assigned) where
  source_eq : display.sourceExpression = .elim block index levels
  selected : EliminatorPrefix (display.node.cast source_eq rfl)

noncomputable def EndpointDisplay.eliminatorPrefix
    (display : EndpointDisplay env U displayed (.elim block index levels) assigned) :
    EliminatorDisplayPrefix display := by
  have same : display.sourceExpression = .elim block index levels :=
    VExpr.lift'_inj.mp display.expression_eq.symm
  exact ⟨same, OriginalEndpointFactor.eliminatorPrefix (display.node.cast same rfl)⟩

structure EliminatorDisplayPrefix.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {display : EndpointDisplay sourceEnv U displayed (.elim block index levels) assigned}
    (packet : EliminatorDisplayPrefix display) : Prop where
  conversions : PrefixCall.Fundamentals env registry packet.selected.route display.context
  ambient : EliminatorCall.Fundamentals env registry packet.selected.reference display.context

theorem EliminatorDisplayPrefix.conversion_schedule
    {display : EndpointDisplay sourceEnv U displayed (.elim block index levels) assigned}
    (packet : EliminatorDisplayPrefix display)
    (call : PrefixCall packet.selected.route original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  have smaller := call.cost_lt display.context.closures
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

theorem EliminatorDisplayPrefix.ambient_schedule
    {display : EndpointDisplay sourceEnv U displayed (.elim block index levels) assigned}
    (packet : EliminatorDisplayPrefix display)
    (call : EliminatorCall packet.selected.reference original) (otherCost : Nat) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation display.context).closures).cost <
      schedule .coherence (display.cost + otherCost) := by
  apply schedule_strict
  rw [EliminatorCall.contextDerivation_closures]
  have localBound := call.cost_lt display.context.closures
  have prefixBound := Nat.mul_le_mul_right (1 + environmentCost display.context.closures)
    packet.selected.route.weight_le
  have smaller := Nat.lt_of_lt_of_le localBound prefixBound
  simp only [EndpointState.origin_cast] at smaller
  exact Nat.lt_of_lt_of_le smaller (Nat.le_add_right _ _)

/-- Schema uniqueness is a separate metadata invariant; neither Ordered nor
source observations are used to infer it. It fixes the actual owner header
before transporting the finite source certificate between the two displays. -/
theorem EliminatorDisplayPrefix.compare
    {left : EndpointDisplay leftEnv U displayed (.elim block index levels) leftAssigned}
    {right : EndpointDisplay rightEnv U displayed (.elim block index levels) rightAssigned}
    (leftPacket : EliminatorDisplayPrefix left) (rightPacket : EliminatorDisplayPrefix right)
    (henv : env.Ordered) (hscoped : registry.Scoped) (unique : env.EliminatorsUnique)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : leftPacket.Fundamentals env registry)
    (rightCalls : rightPacket.Fundamentals env registry) :
    DisplayCoherence env U registry left right := by
  intro target common available leftLocals rightLocals closed hTarget leftFrame rightFrame
  have leftClosed := left.sourceValuation_closed closed
  have rightClosed := right.sourceValuation_closed closed
  let header := leftPacket.selected.header.mono leftBelow
  have headerClosed : (header.type.instL levels).Closed := header.closed.instL
  have leftPath := EndpointRef.eliminatorTargetPath henv unique leftBelow hTarget
    leftFrame.substitutions header leftPacket.selected.reference rfl leftPacket.selected.primitive
  have rightPath := EndpointRef.eliminatorTargetPath henv unique rightBelow hTarget
    rightFrame.substitutions header rightPacket.selected.reference rfl rightPacket.selected.primitive
  rw [headerClosed.subst_eq .zero] at leftPath rightPath
  have path := PrefixRoute.comparePath henv leftBelow rightBelow hTarget
    leftFrame.substitutions rightFrame.substitutions leftPacket.selected.route rightPacket.selected.route
    (leftPath.trans rightPath.symm)
  refine ⟨?_, ?_⟩
  · simpa only [left.realizedType common, right.realizedType common] using path
  · intro n profile footprint certificate resources
    apply PrefixRoute.compareHeadsOriginal henv hscoped leftBelow rightBelow
      left.context right.context leftClosed rightClosed hTarget
      leftFrame.substitutions rightFrame.substitutions leftFrame.fits rightFrame.fits
      leftPacket.selected.route rightPacket.selected.route leftCalls.conversions rightCalls.conversions
      (certificate := certificate) (resources := resources)
    intro required natural incoming
    obtain ⟨leftAnswer⟩ := EndpointRef.replayEliminator henv hscoped unique leftBelow
      left.context leftClosed hTarget leftFrame.substitutions leftFrame.fits header
      leftPacket.selected.reference rfl leftPacket.selected.primitive leftCalls.ambient natural incoming
    obtain ⟨footprint, ⟨transported⟩, resources⟩ := OriginalFactorCut.CodeCert.betweenDisplays
      leftAnswer.certificate left.map right.map common rfl rfl
      (show (header.type.instL levels).lift' left.map = (header.type.instL levels).lift' right.map from by
        rw [headerClosed.lift'_eq .zero, headerClosed.lift'_eq .zero])
      [] rightLocals leftAnswer.available (fun _ => rfl) (fun _ => rfl)
    have crossing : CodeTransferResult env U registry target rightLocals
        (left.sourceSubst common) (right.sourceSubst common) (right.sourceValuation available)
        leftPacket.selected.type (header.type.instL levels) profile := {
      footprint := footprint, certificate := transported, available := resources
      related := by
        simpa only [headerClosed.subst_eq (σ := left.sourceSubst common) .zero,
          headerClosed.subst_eq (σ := right.sourceSubst common) .zero] using leftAnswer.related }
    exact EndpointRef.restoreEliminator henv hscoped unique rightBelow right.context rightClosed hTarget
      rightFrame.substitutions rightFrame.fits header rightPacket.selected.reference rfl
      rightPacket.selected.primitive rightCalls.ambient crossing

theorem EndpointDisplay.eliminatorCoherence
    (left : EndpointDisplay leftEnv U displayed (.elim block index levels) leftAssigned)
    (right : EndpointDisplay rightEnv U displayed (.elim block index levels) rightAssigned)
    (henv : env.Ordered) (hscoped : registry.Scoped) (unique : env.EliminatorsUnique)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftCalls : left.eliminatorPrefix.Fundamentals env registry)
    (rightCalls : right.eliminatorPrefix.Fundamentals env registry) :
    DisplayCoherence env U registry left right :=
  left.eliminatorPrefix.compare right.eliminatorPrefix henv hscoped unique leftBelow rightBelow leftCalls rightCalls

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
