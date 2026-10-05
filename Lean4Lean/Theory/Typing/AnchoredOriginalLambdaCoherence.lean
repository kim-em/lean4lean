import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplayTransport
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedPiRows
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

/-! The lambda comparison keeps each body's own original domain closure.
Displaying both bodies under the common annotation does not replace either
captured source context or add a cross-endpoint domain cost. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def LamView.bodyDisplay
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation env U rootSource)
    (insertion : Ctx.Lift' map source displayed) :
    EndpointDisplay env U (A.lift' map :: displayed)
      (expression.lift' map.cons) (view.bodyType.lift' map.cons) where
  source := A :: source
  sourceExpression := expression
  sourceType := view.bodyType
  context := (Located.lamBody view.location).contextDerivation initial
  node := view.body
  provenance := .ofLocation (.lamBody view.location) initial
  map := map.cons
  insertion := insertion.cons
  expression_eq := rfl
  type_eq := rfl

/-- Exact common syntax is a display equality, never a replacement of the
original body or of the domain proof stored in its captured source context. -/
noncomputable def LamView.bodyDisplayAs
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation env U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (annotation_eq : annotation = A.lift' map)
    (expression_eq : displayedBody = expression.lift' map.cons) :
    EndpointDisplay env U (annotation :: displayed)
      displayedBody (view.bodyType.lift' map.cons) where
  source := A :: source
  sourceExpression := expression
  sourceType := view.bodyType
  context := (Located.lamBody view.location).contextDerivation initial
  node := view.body
  provenance := .ofLocation (.lamBody view.location) initial
  map := map.cons
  insertion := by rw [annotation_eq]; exact insertion.cons
  expression_eq := expression_eq
  type_eq := rfl

/-- The raw part of two-typing coherence is independent of the finite query.
Both endpoints retain their exact original closures; only their displays
and target realization are shared. This is a contract, not its proof. -/
def RawCodeCoherence (env : VEnv) (U : Nat) (target : List VExpr) (σ : Subst)
    {leftEnv rightEnv : VEnv} {displayed : List VExpr}
    {expression leftType rightType : VExpr}
    (_left : EndpointDisplay leftEnv U displayed expression leftType)
    (_right : EndpointDisplay rightEnv U displayed expression rightType) : Prop :=
  TypeConversion env U target (leftType.subst σ) (rightType.subst σ)

theorem LamView.bodyDisplay_cost_lt
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.lam A expression) assigned}
    {start : Located root node} (view : LamView start)
    (initial : ContextDerivation env U rootSource)
    (insertion : Ctx.Lift' map source displayed) :
    (view.bodyDisplay initial insertion).cost <
      (Closure.close node.origin (start.environment initial.closures)).cost := by
  change (Closure.close view.body.origin
    ((Located.lamBody view.location).contextDerivation initial).closures).cost < _
  rw [Located.contextDerivation_closures]
  exact Nat.lt_of_lt_of_le
    (binder_body_cost (domain := view.domain.origin)
      (bodies := [view.codomain.origin, view.body.origin]) (children := [])
      (body := view.body.origin) (by simp) (view.location.environment initial.closures))
    (view.cost_le initial.closures)

/-- Each recursive side captures its own domain formation even when their
literal annotations agree only after different source insertions. -/
theorem lambda_body_pair_schedule
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.lam A expression) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.lam C otherExpression) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : LamView leftStart) (rightView : LamView rightStart)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed) :
    schedule .coherence
      ((leftView.bodyDisplay leftInitial leftInsertion).cost +
        (rightView.bodyDisplay rightInitial rightInsertion).cost) <
    schedule .coherence
      ((Closure.close leftNode.origin (leftStart.environment leftInitial.closures)).cost +
        (Closure.close rightNode.origin (rightStart.environment rightInitial.closures)).cost) := by
  apply schedule_strict
  exact Nat.add_lt_add (leftView.bodyDisplay_cost_lt leftInitial leftInsertion)
    (rightView.bodyDisplay_cost_lt rightInitial rightInsertion)

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.VEnv
open VExpr

/-- Natural lambda type comparison uses the body path at a fresh target
binder. Every edge keeps its own universe; no sort uniqueness is required. -/
theorem TypeConversion.forallSameDomain
    (domain : env.HasType U Γ A (.sort level))
    (bodies : TypeConversion env U (A :: Γ) B D) :
    TypeConversion env U Γ (.forallE A B) (.forallE A D) := by
  induction bodies with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (.forallEDF domain edge)

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- Consume the raw answer for the fixed original body pair at the fresh
neutral binder. This call does not depend on a retained Pi row or its anchor. -/
theorem lambda_natural_raw
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.lam A expression) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.lam C otherExpression) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : LamView leftStart) (rightView : LamView rightStart)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftAnnotation : annotation = A.lift' leftMap)
    (rightAnnotation : annotation = C.lift' rightMap)
    (leftExpression : displayedBody = expression.lift' leftMap.cons)
    (rightExpression : displayedBody = otherExpression.lift' rightMap.cons)
    (domain : env.HasType U target (annotation.subst σ) (.sort level))
    (bodyAnswer : RawCodeCoherence env U (annotation.subst σ :: target) σ.lift
      (leftView.bodyDisplayAs leftInitial leftInsertion leftAnnotation leftExpression)
      (rightView.bodyDisplayAs rightInitial rightInsertion rightAnnotation rightExpression)) :
    TypeConversion env U target
      ((VExpr.forallE annotation (leftView.bodyType.lift' leftMap.cons)).subst σ)
      ((VExpr.forallE annotation (rightView.bodyType.lift' rightMap.cons)).subst σ) :=
  TypeConversion.forallSameDomain domain bodyAnswer

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource
open VExpr VEnv

/-- The frozen Pi prototype also constrains the body when its row list is
empty. The raw body answer, rather than a chosen finite row, moves that path. -/
theorem PiGuard.reindexBodies
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (domains : A.subst σ = C.subst τ)
    (bodies : TypeConversion env U (A.subst σ :: target)
      (B.subst σ.lift) (D.subst τ.lift)) :
    PiGuard env U target τ C D prototypeDomain prototypeBody where
  domainPath := by rw [← domains]; exact guard.domainPath
  bodyPath := by rw [← domains]; exact bodies.symm.trans guard.bodyPath

end Lean4Lean.AnchoredSource

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Finite replies to exactly the body requests already stored in an incoming
Pi row tree. The original body's coherence call changes the assigned type
from B to D at the same frozen anchor. Empty inputs are retained as rows. -/
inductive LambdaRowAnswers
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (leftLocals rightLocals : List Nat)
    (σ τ : Subst) (rightAvailable : Valuation) (A B D : VExpr) :
    {n : Nat} → {ambient : Profile n} → {table : List (Key n × Profile n)} →
    {footprint : Footprint} →
    PiRows env U registry target leftLocals σ A B ambient table footprint → Type where
  | nil : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D .nil
  | cons
      {key : Key n} {output packed ambient : Profile n}
      {bodyFootprint externalFootprint tailFootprint : Footprint}
      {table : List (Key n × Profile n)}
      {guard : LambdaGuard env U registry target σ A key ambient}
      {body : CodeCert env U registry target (Locals.push leftLocals)
        (σ.cons key.anchor) B output bodyFootprint}
      {pack : BinderPack n packed bodyFootprint externalFootprint}
      {covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms}
      {tail : PiRows env U registry target leftLocals σ A B ambient table tailFootprint}
      (answer : CodeTransferResult env U registry target (Locals.push rightLocals)
        (σ.cons key.anchor) (τ.cons key.anchor)
        (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
          rightAvailable) B D output)
      (rest : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D tail) :
      LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D
        (.cons guard body pack covered tail)

/-- Replay uses literal target-domain agreement and each fixed smaller body
answer. Repacking is computed from the returned footprint, never supplied by
the caller. No row, including an empty-input row, is removed. -/
theorem LambdaRowAnswers.replay
    (domains : A.subst σ = C.subst τ)
    {rows : PiRows env U registry target leftLocals σ A B ambient table footprint}
    (answers : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D rows) :
    Nonempty (RowsResult env U registry target rightLocals τ rightAvailable C D ambient table) := by
  induction answers with
  | nil => exact ⟨⟨[], .nil, fun _ _ impossible => nomatch impossible⟩⟩
  | @cons key output packed ambient bodyFootprint externalFootprint tailFootprint table
      guard body pack covered tail answer rest ih =>
    have guard' : LambdaGuard env U registry target τ C key ambient := {
      inputTyped := guard.inputTyped
      formed := guard.formed
      path := by rw [← domains]; exact guard.path
      domains := by rw [← domains]; exact guard.domains
      anchor := guard.anchor }
    obtain ⟨newPacked, outside, newPack, newCovered, outsideAvailable⟩ :=
      Footprint.pack_available answer.available
        (fun need hm => (pack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    obtain ⟨remaining⟩ := ih
    exact ⟨⟨outside ++ remaining.footprint,
      .cons guard' answer.certificate newPack newCovered remaining.bodies,
      fun i need hm => (List.mem_append.mp hm).elim
        (outsideAvailable i need) (remaining.resources i need)⟩⟩

/-- The same finite replies retain cross-type semantics at every original
anchor, independently of the fresh-neutral answer used for raw prototypes. -/
theorem LambdaRowAnswers.anchorRelated
    {rows : PiRows env U registry target leftLocals σ A B ambient table footprint}
    (answers : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D rows)
    (member : (key, output) ∈ table) :
    TypeRelated env U registry target (B.subst (σ.cons key.anchor))
      (D.subst (τ.cons key.anchor)) output := by
  induction answers with
  | nil => cases member
  | cons answer rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact answer.related
    · exact ih member

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Read a diagonal row at any admitted pair from an actual literal Pi
capability. This follows its concrete exposure, not raw Pi injectivity. -/
theorem TypeRelated.literalPiDiagonalRow
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (member : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key x y) :
    TypeRelated env U registry target (B.inst x) (B.inst y) result := by
  have base := whole target .refl (.refl hTarget)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody ambient rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  have arguments := route.admitted henv admitted
  have bodies := witness.rowBodies key result member
    witness.context .refl (.refl (route.targetWF henv hTarget))
    (x.lift' witness.map) (y.lift' witness.map) (by
      simpa only [Lift.comp, Admitted] using arguments)
  apply route.codeBack henv hscoped
  simpa only [TypeRelated, Lift.comp, lift'_refl, Profile.rename_refl,
    lift'_depth_zero (l := Lift.refl.cons) rfl,
    witness.leftExposure.literalPi_components.2, lift'_inst_hi] using bodies.1

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Binary Pi semantics needs only the two formation diagonals, a raw body
path at the fresh binder, and the finite cross answers at stored anchors. -/
theorem TypeRelated.literalPiPairFromAnchors
    {n : Nat} {ambient : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (hA : env.IsType U target A)
    (hB : env.IsType U (A :: target) B) (hD : env.IsType U (A :: target) D)
    (bodies : TypeConversion env U (A :: target) B D)
    (prototypeA : TypeConversion env U target A prototypeDomain)
    (prototypeB : TypeConversion env U (A :: target) B prototypeBody)
    (domainRelated : TypeRelated env U registry target A A ambient)
    (domainFormed : ambient.HasType (.sort true))
    (rowDomains : ∀ key result, (key, result) ∈ rows →
      key.input.HasType ambient ∧ result.HasType (.sort true) ∧
        TypeConversion env U target key.domain A ∧
        TypeRelated env U registry target key.domain A ambient)
    (left : TypeRelated env U registry target (.forallE A B) (.forallE A B)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (right : TypeRelated env U registry target (.forallE A D) (.forallE A D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (anchors : ∀ key result, (key, result) ∈ rows →
      TypeRelated env U registry target (B.inst key.anchor) (D.inst key.anchor) result) :
    TypeRelated env U registry target (.forallE A B) (.forallE A D)
      (Profile.pi prototypeDomain prototypeBody ambient rows) := by
  apply TypeRelated.literalPiPair henv hTarget hA hA hB hD .refl bodies
    prototypeA prototypeB domainRelated
  · intro key result member
    obtain ⟨typed, _, path, related⟩ := rowDomains key result member
    exact ⟨ambient, typed, domainFormed, Profile.le_refl _, path, related⟩
  · intro key result member Δ ρ future x y admitted
    have left' := left.future henv future
    have right' := right.future henv future
    change TypeRelated env U registry Δ
      (.forallE (A.lift' ρ) (B.lift' ρ.cons))
      (.forallE (A.lift' ρ) (B.lift' ρ.cons))
      (Profile.pi (prototypeDomain.lift' ρ) (prototypeBody.lift' ρ.cons)
        (ambient.rename ρ) (rows.map fun p => (p.1.rename ρ, p.2.rename ρ))) at left'
    change TypeRelated env U registry Δ
      (.forallE (A.lift' ρ) (D.lift' ρ.cons))
      (.forallE (A.lift' ρ) (D.lift' ρ.cons))
      (Profile.pi (prototypeDomain.lift' ρ) (prototypeBody.lift' ρ.cons)
        (ambient.rename ρ) (rows.map fun p => (p.1.rename ρ, p.2.rename ρ))) at right'
    have member' := List.mem_map_of_mem (f := fun p : Key _ × Profile _ =>
      (p.1.rename ρ, p.2.rename ρ)) member
    have hΔ := future.targetWF henv
    have lx := left'.literalPiDiagonalRow henv hscoped hΔ member' admitted
    have rx := right'.literalPiDiagonalRow henv hscoped hΔ member' admitted
    have fromAnchor : Admitted env U registry Δ (key.rename ρ)
        (key.anchor.lift' ρ) x := by
      obtain ⟨path, _, support, typed, formed, code, first, _⟩ := admitted
      exact ⟨path.hasType.1, path, support, typed, formed, code, Related.left_diagonal first, first⟩
    have la := left'.literalPiDiagonalRow henv hscoped hΔ member' fromAnchor
    have ra := right'.literalPiDiagonalRow henv hscoped hΔ member' fromAnchor
    have bridge := (anchors key result member).future henv future
    have outputWF : (result.rename ρ).WF :=
      Profile.rename_wf_iff.mpr (rowDomains key result member).2.1.wf_value
    refine ⟨lx, rx, (la.symm henv outputWF).trans henv ?_⟩
    apply TypeRelated.trans henv _ ra
    simpa only [lift'_inst_hi] using bridge

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem LambdaRowAnswers.rowFacts
    {rows : PiRows env U registry target leftLocals σ A B ambient table footprint}
    (answers : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D rows)
    (member : (key, output) ∈ table) :
    key.input.HasType ambient ∧ output.HasType (.sort true) ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) ambient := by
  induction answers with
  | nil => cases member
  | @cons key output packed ambient bodyFootprint externalFootprint tailFootprint table
      guard body pack covered tail answer rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact ⟨guard.inputTyped, body.formed, guard.path, guard.domains⟩
    · exact ih member

/-- The primitive natural lambda type query. Domain transport is computed
from the common display; the only cross-body answers are the finite row tree
and the independent raw answer. Formation diagonals are fixed F results. -/
theorem LambdaRowAnswers.comparePi
    {commonAvailable : Valuation}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    {ambient : Profile n} {table : List (Key n × Profile n)}
    (domain : CodeCert env U registry target leftLocals σ A ambient domainFootprint)
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    {rows : PiRows env U registry target leftLocals σ A B ambient table rowFootprint}
    (answers : LambdaRowAnswers env U registry target leftLocals rightLocals σ τ rightAvailable A B D rows)
    (formed : (Profile.pi prototypeDomain prototypeBody ambient table).HasType (.sort true))
    (leftMap rightMap : Lift) (common : Subst)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (sameDomain : A.lift' leftMap = C.lift' rightMap)
    (commonLocals : List Nat)
    (resources : domainFootprint.Available leftAvailable)
    (leftAvailableEq : ∀ i, leftAvailable i = commonAvailable (leftMap.liftVar i))
    (rightAvailableEq : ∀ i, rightAvailable i = commonAvailable (rightMap.liftVar i))
    (hA : env.IsType U target (A.subst σ))
    (hB : env.IsType U (A.subst σ :: target) (B.subst σ.lift))
    (hD : env.IsType U (C.subst τ :: target) (D.subst τ.lift))
    (rawBodies : TypeConversion env U (A.subst σ :: target) (B.subst σ.lift) (D.subst τ.lift))
    (domainRelated : TypeRelated env U registry target (A.subst σ) (A.subst σ) ambient)
    (leftFormation : TypeRelated env U registry target
      ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst σ)
      (Profile.pi prototypeDomain prototypeBody ambient table))
    (rightFormation : TypeRelated env U registry target
      ((VExpr.forallE C D).subst τ) ((VExpr.forallE C D).subst τ)
      (Profile.pi prototypeDomain prototypeBody ambient table)) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE A B) (.forallE C D) (Profile.pi prototypeDomain prototypeBody ambient table)) := by
  have domains := OriginalFactorCut.realized_between_displays sameDomain leftRealization rightRealization
  obtain ⟨required, ⟨rightDomain⟩, rightResources⟩ := OriginalFactorCut.CodeCert.betweenDisplays domain
    leftMap rightMap common leftRealization rightRealization sameDomain commonLocals rightLocals
    resources leftAvailableEq rightAvailableEq
  obtain ⟨rightRows⟩ := answers.replay domains
  have rightGuard := guard.reindexBodies domains rawBodies
  refine ⟨⟨required ++ rightRows.footprint, .seed (.pi rightDomain rightGuard rightRows.bodies) formed,
    (fun i need member => (List.mem_append.mp member).elim
      (rightResources i need) (rightRows.resources i need)), ?_⟩⟩
  change TypeRelated env U registry target
    (.forallE (A.subst σ) (B.subst σ.lift)) (.forallE (C.subst τ) (D.subst τ.lift)) _
  change TypeRelated env U registry target
    (.forallE (C.subst τ) (D.subst τ.lift)) (.forallE (C.subst τ) (D.subst τ.lift)) _ at rightFormation
  rw [← domains] at hD rightFormation ⊢
  apply TypeRelated.literalPiPairFromAnchors henv hscoped hTarget hA hB hD rawBodies
    guard.domainPath guard.bodyPath domainRelated domain.formed
    (fun key result member => answers.rowFacts member) leftFormation rightFormation
  intro key result member
  simpa only [inst_lift_cons] using answers.anchorRelated member

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
