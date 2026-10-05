import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue
import Lean4Lean.Theory.Typing.AnchoredStageBudgets

/-! Fixed caller controls constrain both actual outputs of rich computational
F. These bounds concern the very same returned witnesses, including projected
metadata and definition children at their original earlier source environments.
The global rich F/R induction must preserve this stronger result. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure RichBudgetedComputationalValue
    (budgets : Budgeted.Budgets)
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {value assigned : VExpr}
    (owner : EndpointState sourceEnv U source value assigned)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (input : Profile n)
    extends RichComputationalValue sourceEnv env U registry target owner locals σ τ available input where
  observationBound : Budgeted.Within budgets rightQuery.observation.nativeDepth
  certificateBound : Budgeted.Within budgets certificate.nativeDepth

structure RichBudgetedCodeTransferResult
    (budgets : Budgeted.Budgets)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression : VExpr} {leftLevel rightLevel : VLevel}
    (left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel))
    (right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel))
    (rightLocals : List Nat) (σ τ : Subst) (available : Valuation)
    (relevant : Bool) (profile : Profile n)
    extends RichCodeTransferResult env U registry target left right rightLocals σ τ available relevant profile where
  certificateBound : Budgeted.Within budgets certificate.nativeDepth

/-- Formation F inherits every caller control from its actual computational
answer; generalized code extraction introduces no new declaration unfolding. -/
theorem RichBudgetedComputationalValue.code
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichBudgetedComputationalValue budgets sourceEnv env U registry target node locals σ τ available profile)
    (sorted : profile.HasType (.sort relevant)) :
    Nonempty (RichBudgetedCodeTransferResult budgets env U registry target node node locals σ τ available relevant profile) := by
  obtain ⟨footprint, certificate, resources, depth⟩ := answer.rightQuery.code_nativeDepth henv sorted
  refine ⟨{
    footprint := footprint, certificate := certificate, resources := resources
    related := answer.related.code_of_sortable henv hscoped formed sorted
    certificateBound := ?_ }⟩
  intro current fuel member
  exact Nat.le_trans (depth current) (answer.observationBound current fuel member)

theorem RichBudgetedComputationalValue.apply
    {n : Nat} {output : Atom n} {key : Key n} {rawInput : Profile n}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (left : RichSupportedValue sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ σ available (.singleton output))
    (leftBound : Budgeted.Within budgets left.certificate.nativeDepth)
    (functionAnswer : RichBudgetedComputationalValue budgets sourceEnv env U registry target function locals σ τ available
      (Profile.fn (key : Key n) output))
    (argumentAnswer : RichBudgetedComputationalValue budgets sourceEnv env U registry target argument locals σ τ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target (a.subst σ) (a.subst τ) (A.subst σ))
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    Nonempty (RichBudgetedComputationalValue budgets sourceEnv env U registry target
      (.app hu hv domain body function argument result) locals σ τ available (.singleton output)) := by
  obtain ⟨answer, observationDepth, certificateDepth⟩ := RichComputationalValue.apply_nativeDepth
    henv hscoped formed closed domain body result hu hv left functionAnswer.toRichComputationalValue
    argumentAnswer.toRichComputationalValue arguments raw admitted
  refine ⟨{ answer with observationBound := ?_, certificateBound := ?_ }⟩
  · intro current fuel member
    change answer.rightQuery.observation.nativeDepth current ≤ fuel
    rw [observationDepth current]
    exact Nat.max_le.mpr ⟨functionAnswer.observationBound current fuel member,
      argumentAnswer.observationBound current fuel member⟩
  · intro current fuel member
    change answer.certificate.nativeDepth current ≤ fuel
    rw [certificateDepth current]
    exact leftBound current fuel member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
