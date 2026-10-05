import Lean4Lean.Theory.Typing.AnchoredNativeChosenReplay
import Lean4Lean.Theory.Typing.AnchoredNativePlanConsumption
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope

/-! Source resources follow the same finite capture program as typed replay.
Each copied data demand reuses the caller's actual argument observer. Proof
fields have empty demands and require no new source valuation entry. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private prefix_choose from Lean4Lean.Theory.Typing.AnchoredNativeChosenReplay
set_option backward.isDefEq.respectTransparency false

/-- A finite valuation with an actual source observer for every stored need. -/
def NativeGradedSubstitution (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (replacement : Subst) (prior : Valuation) : Prop :=
  ∀ index need, need ∈ prior index →
    Nonempty (GradedResult env U registry target locals σ available (replacement index) need.profile)

theorem NativeGradedValuation.substitution
    (observed : NativeGradedValuation env U registry target locals σ available arguments prior) :
    NativeGradedSubstitution env U registry target locals σ available (nativeCaptureSubst arguments) prior := by
  intro index need member
  obtain ⟨bound, result⟩ := observed index need member
  simpa only [nativeCaptureSubst, dif_pos bound] using result

theorem NativeGradedSubstitution.supply
    (observed : NativeGradedSubstitution env U registry target locals σ available replacement prior)
    (resources : footprint.Available prior) :
    Nonempty (GradedSupply env U registry target locals σ replacement available footprint) := by
  induction footprint with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨value⟩ := observed entry.1 entry.2 (resources _ _ List.mem_cons_self)
    obtain ⟨tail⟩ := ih (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    exact ⟨.cons value tail⟩

/-- The source replacement is computed by the capture plan itself. Its
finite observers come only from the original argument observations and the
stored index/proof resource coverage. -/
theorem NativeSupportedReplay.sourceValues
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    {sourceArguments : List VExpr}
    (length : sourceArguments.length = argumentSource.length)
    (observed : NativeGradedValuation env U registry target callerLocals σ callerAvailable
      sourceArguments argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (witnesses : Subst) :
    NativeGradedSubstitution env U registry target callerLocals σ callerAvailable
      (plan.choose (nativeCaptureSubst sourceArguments) witnesses) available := by
  induction replay generalizing witnesses with
  | nil => exact fun _ _ member => nomatch member
  | @commonPrefix later declared plan source literal count added captures =>
    subst plan
    rw [prefix_choose, nativePrefixPlan_captures _ _ sourceArguments
      (by rw [length, source, List.length_append])]
    intro index need member
    simpa only [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar] using
      observed.substitution (index + later.length) need member
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    intro index need member
    cases index with
    | zero =>
      obtain ⟨argument⟩ := observed.substitution position ⟨n, input⟩ needed
      exact ⟨argument.localDemand need (bounded need member) (covered need member)⟩
    | succ index => exact ih witnesses.tail index need member
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      localNeeds n bounded empty ih =>
    intro index need member
    cases index with
    | zero =>
      have bound := bounded need member
      have noAtoms : need.atGrade n = .empty :=
        List.eq_nil_iff_forall_not_mem.mpr (empty need member)
      have raised : raiseProfile n bound need.profile = .empty := by
        simpa only [Need.atGrade, dif_pos bound] using noAtoms
      refine ⟨{
        rank := n
        bound := bound
        raw := .empty
        footprint := []
        observation := .empty
        adapter := by rw [raised]; exact .refl _
        resources := fun _ _ hm => nomatch hm
        live := .empty }⟩
    | succ index => exact ih witnesses.tail index need member

/-- Literal data agreement restores a supplied source replacement. The
unused infinite tail is irrelevant because every routed need lies in the
actual declared capture telescope. -/
theorem NativeSupportedReplay.sourceValues_agree
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    {sourceArguments : List VExpr}
    (length : sourceArguments.length = argumentSource.length)
    (observed : NativeGradedValuation env U registry target callerLocals σ callerAvailable
      sourceArguments argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (witnesses : Subst) (agree : plan.IndexAgreement (nativeCaptureSubst sourceArguments) witnesses)
    {footprint : Footprint} (scope : Footprint.Scoped declared.length footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedSupply env U registry target callerLocals σ witnesses callerAvailable footprint) := by
  have values := replay.sourceValues length observed witnesses
  induction footprint with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨value⟩ := values entry.1 entry.2 (resources _ _ List.mem_cons_self)
    rw [plan.choose_agrees agree _ (scope _ _ List.mem_cons_self)] at value
    obtain ⟨tail⟩ := ih (fun i need hm => scope i need (List.mem_cons_of_mem _ hm))
      (fun i need hm => resources i need (List.mem_cons_of_mem _ hm))
    exact ⟨.cons value tail⟩

/-- Transfer the stored RHS at the caller's witnessed captures and substitute
its finite variable demands back into the original caller valuation. The
source observer is returned at its actual grade with a composed finite adapter. -/
theorem NativeSupportedReplay.chosenSourceTerminal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    {callerLocals : List Nat} {σ : Subst} {callerAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U)) (callerClosed : callerAvailable.AtomClosed)
    {sourceArguments : List VExpr}
    (length : sourceArguments.length = argumentSource.length)
    (observed : NativeGradedValuation env U registry target callerLocals σ callerAvailable
      sourceArguments argumentAvailable)
    (rawArguments : Ctx.SubstEq env U target arguments
      (nativeCaptureSubst (sourceArguments.map (·.subst σ))) argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals arguments
      (nativeCaptureSubst (sourceArguments.map (·.subst σ))) argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (replacement : Subst)
    (witnessesTyped : Ctx.SubstEq env U target (replacement.comp σ) (replacement.comp σ) declared)
    (sourceAgreement : plan.IndexAgreement (nativeCaptureSubst sourceArguments) replacement)
    (targetAgreement : plan.IndexAgreement
      (nativeCaptureSubst (sourceArguments.map (·.subst σ))) (replacement.comp σ))
    (closed : available.AtomClosed)
    {rhs assigned : VExpr} (original : sourceEnv.IsDefEqStrong U declared rhs rhs assigned)
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedResult env U registry target callerLocals σ callerAvailable
      (rhs.subst replacement) demand) := by
  obtain ⟨transferred⟩ := replay.chosenTerminal henv hscoped hle earlier hTarget
    (sourceArguments.map (·.subst σ)) (by simpa only [List.length_map] using length)
    rawArguments argumentFits (replacement.comp σ) witnessesTyped targetAgreement closed original body resources
  have rhsScope := (original.defeq.mono hle).closedN henv (CtxWF.closed henv witnessesTyped.wf)
  obtain ⟨supply⟩ := replay.sourceValues_agree length observed replacement sourceAgreement
    (transferred.observation.scoped rhsScope) transferred.resultAvailable
  obtain ⟨reified⟩ := transferred.observation.substitute henv hscoped hTarget replacement σ rfl
    callerLocals callerAvailable callerClosed supply
  refine ⟨{
    rank := reified.rank
    bound := Nat.le_trans transferred.bound reified.bound
    raw := reified.raw
    footprint := reified.footprint
    observation := reified.observation
    adapter := ?_
    resources := reified.resources
    live := reified.live }⟩
  simpa only [raiseProfile_trans] using reified.adapter.comp
    (transferred.adapter.raise henv hscoped hTarget reified.bound)

end Lean4Lean.AnchoredSource.Adapted
