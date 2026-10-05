import Lean4Lean.Theory.Typing.AnchoredBoundedVariable
import Lean4Lean.Theory.Typing.AnchoredFamilyIntroduction

/-! Interpret the actual family capture variables at their original lookup
types, then follow the retained finite domain alignment to the frozen keys.
Seed typing alone is never used to infer equality of assigned types. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.interpret
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {expressions : List VExpr} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    {available : Valuation}
    (captures : Adapted.FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (bound : captures.nativeDepth current ≤ fuel)
    (sourceContext : CtxStrong sourceEnv U source)
    (hTarget : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (resources : footprint.Available available) :
    RankedData.Arguments env U (relations env U registry n) target keys
      (expressions.map (·.subst σ)) (expressions.map (·.subst τ)) := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨level, original⟩ := sourceContext.lookup hsource lookup
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Adapted.FamilyCaptures.nativeDepth] using bound)
    obtain ⟨observed⟩ := bvarTransfer henv hscoped lookup (earlier original)
      closed hTarget substitutions fits value bounds.1 (fun i need member =>
        resources i need (List.mem_append_left _ member))
    have aligned := alignment.admission henv anchor.toAdmission
    obtain ⟨_, _, actualSupport, actualTyped, _, actualCode, _, _⟩ := aligned
    have interpreted := adapter.termMap henv hscoped hTarget actualTyped actualCode
      (observed.toGradedTransferResult.requestedRelated henv hTarget)
    obtain ⟨rawAnchor, _, typed, formed, code, anchorRelated, _⟩ := anchor
    have pair := alignment.symm henv |>.related henv typed code interpreted
    refine .cons ?_ (FamilyCaptures.interpret henv hscoped hsource earlier tail bounds.2 sourceContext hTarget
      closed substitutions fits (fun i need member =>
        resources i need (List.mem_append_right _ member)))
    exact ⟨rawAnchor, alignment.path.symm.cast (substitutions.lookup lookup),
      typed, formed, code, anchorRelated, pair⟩
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.Staged
