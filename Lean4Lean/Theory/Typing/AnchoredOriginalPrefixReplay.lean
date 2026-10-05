import Lean4Lean.Theory.Typing.AnchoredOriginalFamilySpine
import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainExtraction
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedPiRule

/-! Backward replay at an actual original constant prefix. Exposure retains
finite conversion plans and their original equality children. Recursive
semantic calls are indexed by these concrete occurrences, with the inherited
source environment charged to the actual original endpoint reserve.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- The source expression stays unchanged while original references and
finite conversion nodes are exposed. -/
inductive PrefixRoute (sourceEnv : VEnv) (U : Nat) (source : List VExpr) (expression : VExpr) :
    {A B : VExpr} → EndpointState sourceEnv U source expression A →
      EndpointState sourceEnv U source expression B → Type where
  | done (node) : PrefixRoute sourceEnv U source expression node node
  | expose (reference : EndpointRef sourceEnv U source expression A)
      (rest : PrefixRoute sourceEnv U source expression reference.expose last) :
      PrefixRoute sourceEnv U source expression (.ref reference) last
  | convert (plan : EndpointConversion sourceEnv U source A B)
      (term : EndpointState sourceEnv U source expression A)
      (rest : PrefixRoute sourceEnv U source expression term last) :
      PrefixRoute sourceEnv U source expression (.convert plan term) last

def PrefixRoute.locate (route : PrefixRoute sourceEnv U source expression first last)
    (start : Located root first) : Located root last :=
  match route with
  | .done _ => start
  | .expose _ rest => rest.locate (.expose start)
  | .convert _ _ rest => rest.locate (.convertTerm start)

theorem PrefixRoute.weight_le (route : PrefixRoute sourceEnv U source expression first last) :
    last.origin.weight ≤ first.origin.weight := by
  induction route with
  | done => exact Nat.le_refl _
  | expose reference rest ih => exact Nat.le_trans ih reference.expose_weight_le
  | convert plan term rest ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (Origin.rule_child (by simp)))

structure PrefixHead (first : EndpointState sourceEnv U source expression assigned) where
  type : VExpr
  node : EndpointState sourceEnv U source expression type
  route : PrefixRoute sourceEnv U source expression first node
  head : Head node

private theorem prefixHead_exists (budget : Nat) :
    ∀ {type} (first : EndpointState sourceEnv U source expression type),
      first.origin.weight ≤ budget → Nonempty (PrefixHead first) := by
  induction budget using Nat.strongRecOn with
  | ind budget ih =>
    intro type first bounded
    cases first with
    | ref reference =>
      have exposed := reference.expose_exposed
      have exposureBound := reference.expose_weight_le
      cases equal : reference.expose with
      | convert plan term =>
        have smaller : term.origin.weight < budget := by
          have child := Origin.rule_child (child := term.origin)
            (children := [term.origin, plan.origin]) (by simp)
          simp only [equal, EndpointState.origin] at exposureBound
          exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le child exposureBound) bounded
        obtain ⟨next⟩ := ih term.origin.weight smaller term (Nat.le_refl _)
        have route : PrefixRoute sourceEnv U source expression reference.expose next.node :=
          equal ▸ PrefixRoute.convert plan term next.route
        exact ⟨⟨_, next.node, .expose reference route, next.head⟩⟩
      | ref primitive =>
        exact ⟨⟨_, reference.expose, .expose reference (.done _),
          by simpa only [equal, Head, EndpointState.Exposed] using exposed⟩⟩
      | _ => exact ⟨⟨_, reference.expose, .expose reference (.done _), by simp only [equal, Head]⟩⟩
    | convert plan term =>
      have smaller : term.origin.weight < budget :=
        Nat.lt_of_lt_of_le (Origin.rule_child (by simp)) bounded
      obtain ⟨next⟩ := ih term.origin.weight smaller term (Nat.le_refl _)
      exact ⟨⟨_, next.node, .convert plan term next.route, next.head⟩⟩
    | _ => exact ⟨⟨_, _, .done _, trivial⟩⟩

noncomputable def prefixHead (first : EndpointState sourceEnv U source expression assigned) :
    PrefixHead first := Classical.choice (prefixHead_exists first.origin.weight first (Nat.le_refl _))

/-- Every equality call is a retained original child of the finite plan. -/
inductive ConversionCall : (plan : EndpointConversion sourceEnv U source A B) →
    {context : List VExpr} → {left right type : VExpr} →
      Derivation sourceEnv U context left right type → Type where
  | forward : ConversionCall (.forward levelWF original) original
  | backward : ConversionCall (.backward levelWF original) original
  | piDomain : ConversionCall (.piDomain hu hv domain body otherBody) domain
  | piBody : ConversionCall (.piDomain hu hv domain body otherBody) body
  | piOtherBody : ConversionCall (.piDomain hu hv domain body otherBody) otherBody

def ConversionCall.environment
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {A B : VExpr}
    {plan : EndpointConversion sourceEnv U source A B}
    {context : List VExpr} {left right type : VExpr}
    {original : Derivation sourceEnv U context left right type}
    (call : ConversionCall plan original) (initial : List Closure) : List Closure := by
  cases call with
  | forward | backward | piDomain => exact initial
  | @piBody u hu v hv A A' domain B body otherBody => exact .close domain.origin initial :: initial
  | @piOtherBody u hu v hv A A' domain B body otherBody => exact .close domain.origin initial :: initial

theorem ConversionCall.cost_le (call : ConversionCall plan original) (initial : List Closure) :
    (Closure.close original.origin (call.environment initial)).cost ≤
      (Closure.close plan.origin initial).cost := by
  cases call with
  | forward | backward => exact Nat.le_refl _
  | piDomain => exact Nat.le_of_lt (binder_domain_cost _ _ _ initial)
  | piBody | piOtherBody => exact Nat.le_of_lt (binder_body_cost (by simp) initial)

inductive PrefixCall {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {expression : VExpr} :
    {A B : VExpr} → {first : EndpointState sourceEnv U source expression A} →
    {last : EndpointState sourceEnv U source expression B} →
    (route : PrefixRoute sourceEnv U source expression first last) →
    {context : List VExpr} → {left right type : VExpr} →
      Derivation sourceEnv U context left right type → Type where
  | expose {reference : EndpointRef sourceEnv U source expression A}
      {last : EndpointState sourceEnv U source expression B}
      {rest : PrefixRoute sourceEnv U source expression reference.expose last}
      (call : PrefixCall rest original) : PrefixCall (.expose reference rest) original
  | conversion {plan : EndpointConversion sourceEnv U source A B}
      {term : EndpointState sourceEnv U source expression A}
      {last : EndpointState sourceEnv U source expression C}
      {rest : PrefixRoute sourceEnv U source expression term last}
      (call : ConversionCall plan original) : PrefixCall (.convert plan term rest) original
  | tail {plan : EndpointConversion sourceEnv U source A B}
      {term : EndpointState sourceEnv U source expression A}
      {last : EndpointState sourceEnv U source expression C}
      {rest : PrefixRoute sourceEnv U source expression term last}
      (call : PrefixCall rest original) : PrefixCall (.convert plan term rest) original

def PrefixCall.environment (call : PrefixCall route original) (initial : List Closure) : List Closure :=
  match call with
  | .expose call | .tail call => call.environment initial
  | .conversion call => call.environment initial

theorem PrefixCall.cost_lt
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression endType}
    {route : PrefixRoute sourceEnv U source expression first last}
    (call : PrefixCall route original) (initial : List Closure) :
    (Closure.close original.origin (call.environment initial)).cost <
      (Closure.close first.origin initial).cost := by
  induction call with
  | expose call ih =>
    exact Nat.lt_of_lt_of_le ih
      (Nat.mul_le_mul_right (1 + environmentCost initial) (EndpointRef.expose_weight_le _))
  | conversion call =>
    exact Nat.lt_of_le_of_lt (call.cost_le initial)
      (original_child_same_environment (Origin.rule_child (by simp)) initial)
  | tail call ih =>
    exact Nat.lt_trans ih (original_child_same_environment (Origin.rule_child (by simp)) initial)

/-- Induction hypotheses are requested only at the plan's actual original
children, including the two explicitly retained Pi-body contexts. -/
def ConversionCall.Joints (env : VEnv) (registry : CanonicalHead.Registry)
    (plan : EndpointConversion sourceEnv U source A B) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type},
    ConversionCall plan original → GradedJoint env U registry context left right type

def PrefixCall.Joints (env : VEnv) (registry : CanonicalHead.Registry)
    (route : PrefixRoute sourceEnv U source expression first last) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type},
    PrefixCall route original → GradedJoint env U registry context left right type

theorem conversionBackwardJoint
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (plan : EndpointConversion sourceEnv U source A B)
    (calls : ConversionCall.Joints env registry plan) :
    ∃ level, GradedJoint env U registry source B A (.sort level) := by
  cases plan with
  | forward levelWF original => exact ⟨_, (calls .forward).symm⟩
  | backward levelWF original => exact ⟨_, calls .backward⟩
  | piDomain hu hv domain body otherBody =>
    exact ⟨_, GradedJoint.forallEDF henv hscoped (calls .piDomain) (calls .piBody)
      (calls .piOtherBody) (domain.forget.defeq.mono below)
      (body.forget.defeq.mono below) (otherBody.forget.defeq.mono below)⟩

/-- Certificate-only continuation: no diagonal target code is assumed for
an identity route. The continuation may raise the query grade for an earlier
application prefix. -/
theorem PrefixRoute.withCertificate
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Joints env registry route)
    {profile : Profile n} {Result : Type}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty Result)
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) : Nonempty Result := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, original⟩ := conversionBackwardJoint henv hscoped below plan
      (fun call => calls (.conversion call))
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (original target locals σ σ available closed hTarget substitutions fits).1 resources
    exact ih (fun call => calls (.tail call)) finish changed.certificate changed.available

/-- When the final continuation preserves the query, compose the target
code evidence of each actual original conversion. -/
theorem PrefixRoute.replay
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Joints env registry route)
    {profile : Profile n} {outputType : VExpr}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty
        (CodeTransferResult env U registry target locals σ σ available natural outputType profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target locals σ σ available assigned outputType profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, original⟩ := conversionBackwardJoint henv hscoped below plan
      (fun call => calls (.conversion call))
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (original target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨{ result with related := changed.related.trans henv result.related }⟩

/-- The raw target path is available even for an empty support query. Only
retained original equality premises and their finite Pi plan are used. -/
theorem PrefixRoute.targetPath
    {sourceEnv env : VEnv} {U : Nat} (henv : env.Ordered) (below : sourceEnv ≤ env)
    {source target : List VExpr} {σ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last) :
    TypeConversion env U target (assigned.subst σ) (natural.subst σ) := by
  induction route with
  | done => exact .refl
  | expose reference rest ih => exact ih
  | convert plan term rest ih =>
    obtain ⟨level, _, equal⟩ := plan.sound
    exact (TypeConversion.single ((equal.symm.defeq.mono below).substDF henv
      substitutions.wf hTarget substitutions)).trans ih

/-- The only semantic call at a literal constant is its retained ambient
header equality. The closed equality is kept in the original rule reserve,
but no new semantic premise is requested for it. -/
inductive ConstantCall :
    (reference : EndpointRef sourceEnv U source expression assigned) →
    {context : List VExpr} → {left right type : VExpr} →
      Derivation sourceEnv U context left right type → Type where
  | left : ConstantCall (.left (.constDF lookup levelsWF otherLevelsWF levelCount
      levelEquality levelWF closed ambient)) ambient
  | right : ConstantCall (.right (.constDF lookup levelsWF otherLevelsWF levelCount
      levelEquality levelWF closed ambient)) ambient

theorem ConstantCall.cost_lt (call : ConstantCall reference original) (initial : List Closure) :
    (Closure.close original.origin initial).cost <
      (Closure.close reference.origin initial).cost := by
  cases call <;> exact original_child_same_environment (Origin.rule_child (by simp)) initial

def ConstantCall.Joints (env : VEnv) (registry : CanonicalHead.Registry)
    (reference : EndpointRef sourceEnv U source expression assigned) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type},
    ConstantCall reference original → GradedJoint env U registry context left right type

/-- The output names the actual source declaration and its type at the
levels displayed by the original constant endpoint. -/
structure ConstantReplayResult
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (assigned : VExpr) (profile : Profile n) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  transfer : CodeTransferResult env U registry target locals σ σ available assigned
    (info.type.instL levels) profile
  targetPath : TypeConversion env U target (assigned.subst σ)
    ((info.type.instL levels).subst σ)

theorem EndpointRef.replayConstant
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {name : Name} {levels : List VLevel} {assigned : VExpr}
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) (calls : ConstantCall.Joints env registry reference)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      have joint := (calls .left).left henv hscoped
      obtain ⟨answer⟩ := certificate.transfer_graded henv hscoped hTarget closed
        (joint target locals σ σ available closed hTarget substitutions fits).1 resources
      exact ⟨⟨_, by assumption, answer, .refl⟩⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      have joint := calls .right
      obtain ⟨answer⟩ := certificate.transfer_graded henv hscoped hTarget closed
        (joint target locals σ σ available closed hTarget substitutions fits).1 resources
      exact ⟨⟨_, by assumption, answer, .single ((ambient.forget.defeq.mono below).substDF henv
        substitutions.wf hTarget substitutions)⟩⟩

/-- Computed exposure of a syntactic constant. No primitive-rule hypothesis
is required from a consumer. -/
structure ConstantPrefix {name : Name} {levels : List VLevel}
    (first : EndpointState sourceEnv U source (.const name levels) assigned) where
  type : VExpr
  reference : EndpointRef sourceEnv U source (.const name levels) type
  route : PrefixRoute sourceEnv U source (.const name levels) first (.ref reference)
  primitive : reference.Primitive

noncomputable def constantPrefix {name : Name} {levels : List VLevel}
    (first : EndpointState sourceEnv U source (.const name levels) assigned) :
    ConstantPrefix first := by
  obtain ⟨type, node, route, head⟩ := prefixHead first
  cases node with
  | ref reference => exact ⟨type, reference, route, head⟩
  | convert => exact False.elim head

inductive ConstantPrefixCall {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) :
    {context : List VExpr} → {left right type : VExpr} →
      Derivation sourceEnv U context left right type → Type where
  | conversion (call : PrefixCall packet.route original) : ConstantPrefixCall packet original
  | ambient (call : ConstantCall packet.reference original) : ConstantPrefixCall packet original

def ConstantPrefixCall.environment (call : ConstantPrefixCall packet original)
    (initial : List Closure) : List Closure :=
  match call with
  | .conversion call => call.environment initial
  | .ambient _ => initial

theorem ConstantPrefixCall.cost_lt
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    {packet : ConstantPrefix first}
    (call : ConstantPrefixCall packet original) (initial : List Closure) :
    (Closure.close original.origin (call.environment initial)).cost <
      (Closure.close first.origin initial).cost := by
  cases call with
  | conversion call => exact call.cost_lt initial
  | ambient call =>
    exact Nat.lt_of_lt_of_le (call.cost_lt initial)
      (Nat.mul_le_mul_right (1 + environmentCost initial) packet.route.weight_le)

theorem ConstantPrefixCall.cost_lt_root
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    {packet : ConstantPrefix first} (start : Located root first)
    (call : ConstantPrefixCall packet original) (initial : List Closure) :
    (Closure.close original.origin (call.environment (start.environment initial))).cost <
      (Closure.close root.origin initial).cost :=
  Nat.lt_of_lt_of_le (call.cost_lt (start.environment initial)) (start.cost_le initial)

def ConstantPrefixCall.Joints (env : VEnv) (registry : CanonicalHead.Registry)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type},
    ConstantPrefixCall packet original → GradedJoint env U registry context left right type

private theorem PrefixRoute.replayHeader
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Joints env registry route)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty
        (ConstantReplayResult sourceEnv env U registry target locals σ available name levels natural profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, original⟩ := conversionBackwardJoint henv hscoped below plan
      (fun call => calls (.conversion call))
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (original target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    obtain ⟨rawLevel, _, equal⟩ := plan.sound
    have path := TypeConversion.single ((equal.symm.defeq.mono below).substDF henv
      substitutions.wf hTarget substitutions)
    exact ⟨{ result with
      transfer := { result.transfer with related := changed.related.trans henv result.transfer.related }
      targetPath := path.trans result.targetPath }⟩

/-- Complete backward transport from an actual syntactic constant endpoint
to its displayed declaration header. All semantic calls are the packet's
finite, strictly smaller original children. -/
theorem ConstantPrefix.replay
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first)
    (calls : ConstantPrefixCall.Joints env registry packet)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  exact packet.route.replayHeader henv hscoped below closed hTarget substitutions fits
    (fun call => calls (.conversion call))
    (fun current present => EndpointRef.replayConstant henv hscoped below closed hTarget
      substitutions fits packet.reference rfl packet.primitive (fun call => calls (.ambient call)) current present)
    certificate resources

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
