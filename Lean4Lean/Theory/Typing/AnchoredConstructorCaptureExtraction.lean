import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureInterpretation
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupply
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRealization

/-! Reify the exact terminal constructor captures as actual caller syntax.
Frozen anchors are first transferred through the original declaration lookup;
only then is the witnessed source substitution applied. Every request keeps
its original domain, input, support and declaration alignment. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure ConstructorSourceCapture (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target source : List VExpr) (locals : List Nat) (realization seed replacement : Subst)
    (available : Valuation) (index : Nat) (request : DataRequest (Profile n)) where
  declaredType : VExpr
  lookup : Lookup source index declaredType
  observation : GradedResult env U registry target locals realization available
    (replacement index) request.input
  alignment : DomainChain env U registry target request.input request.domain (declaredType.subst seed)
  anchor : RankedData.RequestAdmission env U (relations env U registry n) target request
    (seed index) (seed index)
  pair : env.IsDefEq U target (seed index) ((replacement index).subst realization) request.domain

inductive ConstructorSourceCaptures (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target source : List VExpr) (locals : List Nat) (realization seed replacement : Subst)
    (available : Valuation) : {n : Nat} → List VExpr → List (DataRequest (Profile n)) → Type where
  | nil : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available (n := n) [] []
  | cons (head : ConstructorSourceCapture env U registry target source locals realization seed
      replacement available index request)
      (tail : ConstructorSourceCaptures env U registry target source locals realization seed
        replacement available expressions requests) :
      ConstructorSourceCaptures env U registry target source locals realization seed replacement
        available (.bvar index :: expressions) (request :: requests)

/-- The terminal ledger retains every position, including requests with
empty computational input. -/
theorem ConstructorSourceCaptures.length
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests) : expressions.length = requests.length := by
  induction captures with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem ConstructorSourceCaptures.get
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))}
    {position index : Nat} {request : DataRequest (Profile n)}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests)
    (expressionAt : expressions[position]? = some (.bvar index))
    (requestAt : requests[position]? = some request) :
    Nonempty (ConstructorSourceCapture env U registry target source locals realization seed replacement
      available index request) := by
  induction captures generalizing position with
  | nil => simp at expressionAt
  | cons head tail ih =>
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at expressionAt requestAt
      cases expressionAt
      cases requestAt
      exact ⟨head⟩
    | succ position => exact ih expressionAt requestAt

theorem ConstructorSourceCaptures.observations
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))}
    (captures : ConstructorSourceCaptures env U registry target source locals realization seed replacement
      available expressions requests) :
    List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals realization available expression request.input))
      (expressions.map (·.subst replacement)) requests := by
  induction captures with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.observation⟩ ih

/-- Consume only the finite source demands retained by the constructor plan.
The declaration lookup supplies the first transfer; actual application
observers supply the subsequent hereditary source substitution. -/
theorem FamilyCaptures.sourceCaptures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {source target : List VExpr} {captureLocals callerLocals : List Nat}
    {seed actual replacement realization : Subst}
    {expressions : List VExpr} {requests : List (DataRequest (Profile n))} {footprint : Footprint}
    {captureAvailable callerAvailable : Valuation}
    (captures : FamilyCaptures env U registry target source captureLocals seed expressions requests footprint)
    (sourceContext : CtxStrong sourceEnv U source)
    (hTarget : OnCtx target (env.IsType U))
    (closed : captureAvailable.AtomClosed) (callerClosed : callerAvailable.AtomClosed)
    (substitutions : Ctx.SubstEq env U target seed actual source)
    (fits : PairedFits env U registry source target captureLocals seed actual captureAvailable)
    (resources : footprint.Available captureAvailable)
    (observed : NativeGradedSubstitution env U registry target callerLocals realization callerAvailable
      replacement captureAvailable)
    (agree : ∀ index < source.length, actual index = (replacement index).subst realization) :
    Nonempty (ConstructorSourceCaptures env U registry target source callerLocals realization seed
      replacement callerAvailable expressions requests) := by
  match captures with
  | .nil => exact ⟨.nil⟩
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨level, original⟩ := sourceContext.lookup hsource lookup
    obtain ⟨transferred⟩ := value.graded_bvar henv hscoped lookup (earlier original)
      closed hTarget substitutions fits (fun i need member =>
        resources i need (List.mem_append_left _ member))
    have realized := transferred.observation.realizePrefix lookup.lt (replacement.comp realization) agree
    obtain ⟨supply⟩ := observed.supply transferred.resultAvailable
    obtain ⟨reified⟩ := realized.substitute henv hscoped hTarget replacement realization rfl
      callerLocals callerAvailable callerClosed supply
    let selected : GradedResult env U registry target callerLocals realization callerAvailable
        (replacement _) _ := {
      rank := reified.rank
      bound := Nat.le_trans transferred.bound reified.bound
      raw := reified.raw
      footprint := reified.footprint
      observation := reified.observation
      adapter := by
        simpa only [raiseProfile_trans] using reified.adapter.comp
          ((transferred.adapter.comp (adapter.raise henv hscoped hTarget transferred.bound)).raise
            henv hscoped hTarget reified.bound)
      resources := reified.resources
      live := reified.live }
    obtain ⟨rest⟩ := tail.sourceCaptures henv hscoped hsource earlier sourceContext hTarget
      closed callerClosed substitutions fits
      (fun i need member => resources i need (List.mem_append_right _ member)) observed agree
    refine ⟨.cons ⟨_, lookup, selected, alignment, anchor, ?_⟩ rest⟩
    have pair := alignment.path.symm.cast (substitutions.lookup lookup)
    simpa only [agree _ lookup.lt] using pair
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
