import Lean4Lean.Theory.Typing.AnchoredConstructorPlanConsumption

/-! A saturated consumed constructor plan exposes its original terminal
requests and their actual caller argument observers. Its finite grade
adapter is retained, so no original request is replaced by an app key. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

structure ConstructorConsumedCaptures
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    (consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments requested) where
  rank : Nat
  family : FamilyData (Profile rank)
  requests : List (DataRequest (Profile rank))
  relevant : family.relevant = true
  familyLevels : List VLevel
  familyArguments : List VExpr
  resultShape : consumed.signature.result = mkApps (.const family.name familyLevels) familyArguments
  bound : rank + 1 ≤ consumed.rank
  adapter : NormalAtomAdapter env U registry target
    (raiseAtom consumed.rank bound (.ctor ⟨name, consumed.seedLevels, requests, family, relevant⟩))
    (raiseAtom consumed.rank consumed.bound requested)
  captureFootprint : Footprint
  resultFootprint : Footprint
  captures : FamilyCaptures env U registry target consumed.signature.domains.reverse
    (List.range consumed.anchors.length) (nativeCaptureSubst consumed.anchors)
    (constantCaptureVariables consumed.anchors.length) requests captureFootprint
  resultCode : CodeCert env U registry target (List.range consumed.anchors.length)
    (nativeCaptureSubst consumed.anchors) consumed.signature.result (.singleton (n := rank + 1) (.family family)) resultFootprint
  resources : (captureFootprint ++ resultFootprint).Available consumed.valuation
  sourceCaptures : ConstructorSourceCaptures env U registry target consumed.signature.domains.reverse
    locals σ (nativeCaptureSubst consumed.anchors) (nativeCaptureSubst arguments) available
    (constantCaptureVariables consumed.anchors.length) requests

/-- Reified observations are indexed by the original application arguments,
in their original order, rather than by an independently chosen tuple. -/
theorem ConstructorConsumedCaptures.observations
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    {consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments requested}
    (packet : ConstructorConsumedCaptures consumed) :
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

/-- The terminal's original request tuple is exactly the incoming constructor
descriptor; the finite grade adapter cannot weaken any frozen request. -/
theorem ConstructorConsumedCaptures.exactDemand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : ConstructorData (Profile n)}
    {consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.ctor demand)}
    (packet : ConstructorConsumedCaptures consumed) :
    packet.rank = n ∧ HEq
      (show ConstructorData (Profile packet.rank) from
        ⟨name, consumed.seedLevels, packet.requests, packet.family, packet.relevant⟩) demand :=
  constructorAdapter_exact packet.bound consumed.bound packet.adapter

/-- A literal constructor demand reaches the real terminal. A remaining
binder cannot be hidden by a finite function adapter or outer padding. -/
theorem ConstructorPlanConsumption.saturated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : ConstructorData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.ctor demand)) :
    arguments.length = consumed.signature.domains.length := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature,
    typeClosed, anchors, length, output, footprint, plan, resultAdapter, valuation,
    valuationClosed, originalRaw, originalFits, originalResources, originalObserved⟩
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  cases front with
  | terminal saturated => exact length.symm.trans saturated
  | binder _ _ _ _ _ _ adapter =>
    exact (fnAdapter_not_constructor demandBound (adapter.comp resultAdapter)).elim

theorem ConstructorPlanConsumption.sourceCaptures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {requested : Atom n}
    (consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments requested)
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL consumed.seedLevels)
      (info.type.instL consumed.seedLevels) (.sort typeLevel))
    (full : arguments.length = consumed.signature.domains.length)
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed) :
    Nonempty (ConstructorConsumedCaptures consumed) := by
  rcases consumed with ⟨rank, demandBound, seedLevels, seedWF, seedLength, equivalent, signature, typeClosed,
    anchors, length, output, footprint, plan, resultAdapter, valuation, valuationClosed,
    originalRaw, originalFits, originalResources, originalObserved⟩
  change arguments.length = signature.domains.length at full
  obtain ⟨front⟩ := plan.front henv hscoped hTarget output rfl
  have resources := originalResources
  cases front with
  | terminal saturated shape relevant captures resultCode bound adapter =>
    have sourceContext := signature.prefixCtxStrong formation signature.domains.length
    rw [List.take_length] at sourceContext
    have raw := originalRaw
    have fits := originalFits
    rw [full, List.take_length] at raw fits
    rw [← saturated] at fits
    have observed := originalObserved.substitution
    obtain ⟨actual⟩ := captures.sourceCaptures henv hscoped hsource earlier sourceContext hTarget
      valuationClosed closed raw fits
      (fun i need member => resources i need (List.mem_append_left _ member)) observed (by
        intro index within
        have bound : index < arguments.length := by simpa only [List.length_reverse, ← full] using within
        simp only [nativeCaptureSubst, List.length_map, dif_pos bound, List.getElem_map])
    exact ⟨{
      rank := _
      family := _
      requests := _
      relevant := relevant
      familyLevels := _
      familyArguments := _
      resultShape := shape
      bound := bound
      adapter := adapter.comp resultAdapter
      captureFootprint := _
      resultFootprint := _
      captures := captures
      resultCode := resultCode
      resources := resources
      sourceCaptures := actual }⟩
  | binder origin =>
    have bound := (List.getElem?_eq_some_iff.mp origin).1
    have equal := length.trans full
    omega

/-- The whole source constructor observer needs no assumed arity or terminal
capture supply. Literal demand rigidity supplies saturation. -/
theorem ConstructorPlanConsumption.constructorSourceCaptures
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {levels : List VLevel} {arguments : List VExpr}
    {demand : ConstructorData (Profile n)}
    (consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      arguments (n := n + 1) (.ctor demand))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL consumed.seedLevels)
      (info.type.instL consumed.seedLevels) (.sort typeLevel))
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed) :
    Nonempty (ConstructorConsumedCaptures consumed) :=
  consumed.sourceCaptures henv hscoped hsource earlier formation
    (consumed.saturated henv hscoped hTarget) hTarget closed

end Lean4Lean.AnchoredSource.Adapted
