import Lean4Lean.Theory.Typing.AnchoredOriginalTailLambda
import Lean4Lean.Theory.Typing.AnchoredOriginalTailPrefix
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceVariableRule

/-! Structural semantics for actual finite endpoint states. Binder rules
retain an actual original domain reference. Soundness proofs supply raw
target typing only and are never reified into recursive original premises. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalTail.StateFundamental.toTailJoint
    {node : EndpointState sourceEnv U source expression type}
    (fundamental : StateFundamental env registry context node) :
    TailJoint env registry context expression expression type := by
  intro target locals σ τ available closed hTarget substitutions frame
  have answer := fundamental target locals σ τ available closed hTarget substitutions frame
  exact ⟨answer.1, answer.1, answer.2, answer.2⟩

theorem OriginalTail.StateFundamental.sort
    {level : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source) (levelWF : level.WF U) :
    StateFundamental env registry context (.sort levelWF) := by
  intro target locals σ τ available _closed hTarget _substitutions _frame
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.sort level) (.sort level) (.sort level.succ) :=
    GradedTransfer.sortDF (assigned := level.succ) henv hscoped levelWF levelWF levelWF rfl
      (Relevant.succ _) hTarget
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

theorem OriginalTail.StateFundamental.app
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (domainIH : EndpointFundamental env registry context domain)
    (codomainIH : StateFundamental env registry (.cons context domain) codomain)
    (functionIH : StateFundamental env registry context function)
    (argumentIH : StateFundamental env registry context argument)
    (resultIH : StateFundamental env registry context result) :
    StateFundamental env registry context (.app hu hv (.ref domain) codomain function argument result) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have functionChild : GradedTransfer env U registry target locals σ τ available f f (.forallE A B) :=
    (functionIH target locals σ τ available closed hTarget substitutions frame).1
  have argumentChild : GradedTransfer env U registry target locals σ τ available a a A :=
    (argumentIH target locals σ τ available closed hTarget substitutions frame).1
  have resultChild : GradedTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort v) :=
    (resultIH target locals σ σ available closed hTarget substitutions.left frame.left).1
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.app f a) (.app f a) (B.inst a) :=
    GradedTransfer.appOriginal henv hscoped hle context domain codomain domainIH codomainIH
      functionChild argumentChild resultChild (argument.sound.defeq.mono hle)
      closed hTarget substitutions frame
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

theorem OriginalTail.StateFundamental.lam
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) expression B)
    (domainIH : EndpointFundamental env registry context domain)
    (codomainIH : StateFundamental env registry (.cons context domain) codomain)
    (bodyIH : StateFundamental env registry (.cons context domain) body) :
    StateFundamental env registry context (.lam hu hv (.ref domain) codomain body) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.lam A expression) (.lam A expression) (.forallE A B) :=
    GradedTransfer.lamDFOriginal henv hscoped context domain domainIH.toTailJoint bodyIH.toTailJoint codomainIH.toTailJoint
      (domain.sound.defeq.mono hle) (codomain.sound.defeq.mono hle)
      (body.sound.defeq.mono hle) (body.sound.defeq.mono hle)
      closed hTarget substitutions frame
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

theorem OriginalTail.StateFundamental.pi
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (domainIH : EndpointFundamental env registry context domain)
    (bodyIH : StateFundamental env registry (.cons context domain) body) :
    StateFundamental env registry context (.pi hu hv (.ref domain) body) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.forallE A B) (.forallE A B) (.sort (.imax u v)) := by
    intro n demand footprint observation resources
    exact Obs.piOriginal henv hscoped context domain domainIH.toTailJoint bodyIH.toTailJoint
      (domain.sound.defeq.mono hle) (body.sound.defeq.mono hle) (body.sound.defeq.mono hle)
      closed hTarget substitutions frame observation resources
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

theorem OriginalTail.StateFundamental.convert
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (context : ContextDerivation sourceEnv U source)
    (plan : EndpointConversion sourceEnv U source A B)
    (node : EndpointState sourceEnv U source expression A)
    (calls : OriginalEndpointFactor.ConversionCall.Fundamentals env registry plan context)
    (nodeIH : StateFundamental env registry context node) :
    StateFundamental env registry context (.convert plan node) := by
  intro target locals σ τ available closed hTarget substitutions frame
  obtain ⟨level, _, typeChild⟩ := OriginalEndpointFactor.conversionTailTransfers henv hscoped hle
    plan context calls closed hTarget substitutions.left frame.left
  have transfer : GradedTransfer env U registry target locals σ τ available expression expression B :=
    GradedTransfer.convertAnswer henv hscoped closed hTarget typeChild
      (nodeIH target locals σ τ available closed hTarget substitutions frame).1
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

theorem Obs.bvarWithFormation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {index : Nat} {A : VExpr} {demand : Profile n} {footprint : Footprint}
    (lookup : Lookup source index A)
    (producer : GradedTransfer env U registry target locals σ σ available A A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.bvar index) (.bvar index) A demand) := by
  match observation with
  | .var _ _ _ demand =>
    obtain ⟨entry⟩ := fits.forward.entry index ⟨n, demand⟩
      (resources index _ List.mem_cons_self) A lookup
    obtain ⟨type⟩ := entry.certificate.transfer_graded henv hscoped hTarget closed
      producer entry.available
    exact ⟨{
      rank := n
      bound := Nat.le_refl n
      rawDemand := demand
      resultFootprint := [(index, ⟨n, demand⟩)]
      observation := .var locals τ index demand
      adapter := by rw [raiseProfile_self]; exact .refl _
      resultAvailable := resources
      support := entry.support
      typeFootprint := entry.footprint
      certificate := entry.certificate
      typeAvailable := entry.available
      typed := by simpa only [raiseProfile_self] using entry.typed
      rawTyped := entry.typed
      typeCode := type.related
      related := by simpa only [raiseProfile_self, subst_bvar] using entry.related
      rawRelated := (entry.related.symm henv).left_diagonal }⟩
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    obtain ⟨a⟩ := left.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view child change =>
    obtain ⟨a⟩ := child.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad child =>
    obtain ⟨a⟩ := child.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨a⟩ := child.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    obtain ⟨a⟩ := child.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions fits resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem OriginalTail.StateFundamental.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source A (.sort level))
    (formationIH : StateFundamental env registry context formation) :
    StateFundamental env registry context (.bvar lookup levelWF formation) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have producer : GradedTransfer env U registry target locals σ σ available A A (.sort level) :=
    (formationIH target locals σ σ available closed hTarget substitutions.left frame.left).1
  have transfer : GradedTransfer env U registry target locals σ τ available (.bvar index) (.bvar index) A := by
    intro n demand footprint observation resources
    exact observation.bvarWithFormation henv hscoped lookup producer closed hTarget substitutions
      (frame.toPairedFits henv hTarget) resources
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩


theorem OriginalTail.state_app_schedule
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v)) :
    let parent := schedule .fundamental (Closure.close
      (EndpointState.app hu hv (.ref domain) codomain function argument result).origin context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close codomain.origin (ContextDerivation.cons context domain).closures).cost < parent ∧
    schedule .fundamental (Closure.close function.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close argument.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close result.origin context.closures).cost < parent := by
  exact ⟨schedule_strict (binder_domain_cost _ _ _ _) _ _,
    schedule_strict (binder_body_cost (by simp) _) _ _,
    schedule_strict (binder_other_cost (by simp) _) _ _,
    schedule_strict (binder_other_cost (by simp) _) _ _,
    schedule_strict (binder_other_cost (by simp) _) _ _⟩

theorem OriginalTail.state_lam_schedule
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (body : EndpointState sourceEnv U (A :: source) expression B) :
    let parent := schedule .fundamental (Closure.close
      (EndpointState.lam hu hv (.ref domain) codomain body).origin context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close codomain.origin (ContextDerivation.cons context domain).closures).cost < parent ∧
    schedule .fundamental (Closure.close body.origin (ContextDerivation.cons context domain).closures).cost < parent := by
  exact ⟨schedule_strict (binder_domain_cost _ _ _ _) _ _,
    schedule_strict (binder_body_cost (by simp) _) _ _,
    schedule_strict (binder_body_cost (by simp) _) _ _⟩

theorem OriginalTail.state_pi_schedule
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v)) :
    let parent := schedule .fundamental (Closure.close
      (EndpointState.pi hu hv (.ref domain) body).origin context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close body.origin (ContextDerivation.cons context domain).closures).cost < parent := by
  exact ⟨schedule_strict (binder_domain_cost _ _ _ _) _ _,
    schedule_strict (binder_body_cost (by simp) _) _ _⟩

theorem OriginalTail.state_bvar_schedule
    (context : ContextDerivation sourceEnv U source)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source A (.sort level)) :
    schedule .fundamental (Closure.close formation.origin context.closures).cost <
      schedule .fundamental (Closure.close (EndpointState.bvar lookup levelWF formation).origin context.closures).cost :=
  schedule_strict (original_child_same_environment (Origin.rule_child (by simp)) _) _ _

theorem OriginalTail.state_convert_schedule
    (context : ContextDerivation sourceEnv U source)
    (plan : EndpointConversion sourceEnv U source A B)
    (node : EndpointState sourceEnv U source expression A) :
    schedule .fundamental (Closure.close node.origin context.closures).cost <
      schedule .fundamental (Closure.close (EndpointState.convert plan node).origin context.closures).cost ∧
    ∀ {childSource left right type} {original : Derivation sourceEnv U childSource left right type}
      (call : OriginalEndpointFactor.ConversionCall plan original),
      schedule .fundamental (Closure.close original.origin (call.contextDerivation context).closures).cost <
        schedule .fundamental (Closure.close (EndpointState.convert plan node).origin context.closures).cost := by
  constructor
  · exact schedule_strict (original_child_same_environment (Origin.rule_child (by simp)) _) _ _
  · intro childSource left right type original call
    apply schedule_strict
    rw [OriginalEndpointFactor.ConversionCall.contextDerivation_closures]
    exact Nat.lt_of_le_of_lt (call.cost_le context.closures)
      (original_child_same_environment (Origin.rule_child (by simp)) context.closures)

end Lean4Lean.AnchoredSource.Adapted
