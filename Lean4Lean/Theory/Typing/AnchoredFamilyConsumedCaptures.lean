import Lean4Lean.Theory.Typing.AnchoredFamilyPlanConsumption

/-! A saturated consumed family plan exposes its original terminal
requests and their actual caller argument observers. Its finite grade
adapter is retained, so no original request is replaced by an app key. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

structure FamilyConsumedCaptures
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested) where
  rank : Nat
  level : VLevel
  relevant : Bool
  resultSort : consumed.signature.result = .sort level
  relevance : Relevant level relevant
  requests : List (DataRequest (Profile rank))
  bound : rank + 1 ≤ consumed.rank
  adapter : NormalAtomAdapter env U registry target
    (raiseAtom consumed.rank bound (.family ⟨name, consumed.seedLevels, relevant, requests⟩))
    (raiseAtom consumed.rank consumed.bound requested)
  footprint : Footprint
  captures : FamilyCaptures env U registry target consumed.signature.domains.reverse
    (List.range consumed.anchors.length) (nativeCaptureSubst consumed.anchors)
    (constantCaptureVariables consumed.anchors.length) requests footprint
  resources : footprint.Available consumed.valuation
  sourceCaptures : ConstructorSourceCaptures env U registry target consumed.signature.domains.reverse
    locals σ (nativeCaptureSubst consumed.anchors) (nativeCaptureSubst arguments) available
    (constantCaptureVariables consumed.anchors.length) requests

/-- Reified observations are indexed by the original application arguments,
in their original order, rather than by an independently chosen tuple. -/
theorem FamilyConsumedCaptures.observations
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (packet : FamilyConsumedCaptures consumed) :
    List.Forall₂ (fun expression request => Nonempty
      (GradedResult env U registry target locals σ available expression request.input))
      arguments packet.requests := by
  have result := packet.sourceCaptures.observations
  rw [consumed.length] at result
  have exactArguments :
      (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) =
        arguments := by
    simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments
  rwa [exactArguments] at result

/-- The terminal's original request tuple is exactly the incoming family
descriptor; the finite grade adapter cannot weaken any frozen request. -/
theorem FamilyConsumedCaptures.exactDemand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    {consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)}
    (packet : FamilyConsumedCaptures consumed) :
    packet.rank = n ∧ HEq
      (show FamilyData (Profile packet.rank) from
        ⟨name, consumed.seedLevels, packet.relevant, packet.requests⟩) demand :=
  familyAdapter_exact packet.bound consumed.bound packet.adapter

/-- A literal family demand reaches the real terminal. A remaining
binder cannot be hidden by a finite function adapter or outer padding. -/
theorem FamilyPlanConsumption.saturated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand)) :
    arguments.length = consumed.signature.domains.length := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature,
    typeClosed, anchors, length, output, footprint, plan, resultAdapter, valuation,
    valuationClosed, originalRaw, originalFits, originalResources, originalObserved⟩
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  cases front with
  | terminal saturated => exact length.symm.trans saturated
  | binder _ _ _ _ _ _ adapter =>
    exact (fnAdapter_not_family demandBound (adapter.comp resultAdapter)).elim

theorem FamilyPlanConsumption.sourceCaptures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments requested)
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL consumed.seedLevels)
      (info.type.instL consumed.seedLevels) (.sort typeLevel))
    (full : arguments.length = consumed.signature.domains.length)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed) :
    Nonempty (FamilyConsumedCaptures consumed) := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, output, footprint, plan, resultAdapter, valuation, valuationClosed,
    originalRaw, originalFits, originalResources, originalObserved⟩
  change arguments.length = signature.domains.length at full
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  have resources := originalResources
  cases front with
  | terminal saturated shape relevant captures bound adapter =>
    have sourceContext := signature.prefixCtxStrong formation signature.domains.length
    rw [List.take_length] at sourceContext
    have raw := originalRaw
    have fits := originalFits
    rw [full, List.take_length] at raw fits
    rw [← saturated] at fits
    have observed := originalObserved.substitution
    obtain ⟨actual⟩ := captures.sourceCaptures henv hscoped hsource earlier sourceContext hTarget
      valuationClosed closed raw fits
      resources observed (by
        intro index within
        have bound : index < arguments.length := by simpa only [List.length_reverse, ← full] using within
        simp only [nativeCaptureSubst, List.length_map, dif_pos bound, List.getElem_map])
    exact ⟨{
      rank := _
      level := _
      relevant := _
      resultSort := shape
      relevance := relevant
      requests := _
      bound := bound
      adapter := adapter.comp resultAdapter
      footprint := _
      captures := captures
      resources := resources
      sourceCaptures := actual }⟩
  | binder origin =>
    have bound := (List.getElem?_eq_some_iff.mp origin).1
    have equal := length.trans full
    omega

/-- The whole source family observer needs no assumed arity or terminal
capture supply. Literal demand rigidity supplies saturation. -/
theorem FamilyPlanConsumption.familySourceCaptures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : FamilyData (Profile n)}
    (consumed : FamilyPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.family demand))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL consumed.seedLevels)
      (info.type.instL consumed.seedLevels) (.sort typeLevel))
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed) :
    Nonempty (FamilyConsumedCaptures consumed) :=
  consumed.sourceCaptures henv hscoped hsource earlier formation
    (consumed.saturated henv hscoped hTarget) hTarget closed

end Lean4Lean.AnchoredSource.Adapted
