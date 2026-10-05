import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureInterpretation

/-! Recover the original declared capture substitution from fixed data
requests. Each request is retagged using its retained source domain chain;
no comparison of independently assigned types is used. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.rawLookup
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {expressions : List VExpr} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (admitted : RankedData.Arguments env U (relations env U registry n) target keys
      (expressions.map (·.subst σ)) (expressions.map (·.subst τ)))
    {index : Nat} {type : VExpr} (member : .bvar index ∈ expressions)
    (lookup : Lookup source index type) :
    env.IsDefEq U target (σ index) (τ index) (type.subst σ) := by
  match captures with
  | .nil => cases member
  | .cons stored value adapter alignment anchor tail =>
    cases admitted with
    | cons first rest =>
      rcases List.mem_cons.mp member with same | later
      · cases same
        cases stored.uniq lookup
        exact alignment.path.cast first.2.1
      · exact tail.rawLookup rest later lookup
termination_by sizeOf captures
decreasing_by simp_wf; omega

private theorem substitution_of_lookups
    {env : VEnv} {U : Nat} {target source : List VExpr} {σ τ : Subst}
    (formed : OnCtx source (env.IsType U))
    (pairs : ∀ index type, Lookup source index type →
      env.IsDefEq U target (σ index) (τ index) (type.subst σ)) :
    Ctx.SubstEq env U target σ τ source := by
  induction source generalizing σ τ with
  | nil => exact .nil
  | cons A source ih =>
    obtain ⟨level, formation⟩ := formed.2
    refine .cons (ih formed.1 ?_) formation ?_
    · intro index type lookup
      simpa only [lift_subst, Subst.tail] using pairs (index + 1) type.lift (.succ lookup)
    · simpa only [lift_subst, Subst.head] using pairs 0 A.lift .zero

/-- Every original declaration variable occurs in the terminal capture
list. Its exact fixed-support admission therefore supplies a typed paired
substitution for that declaration, including its dependent field domains. -/
theorem FamilyCaptures.rawSubstitution
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target source locals σ
      (constantCaptureVariables source.length) keys footprint)
    (formed : OnCtx source (env.IsType U))
    (admitted : RankedData.Arguments env U (relations env U registry n) target keys
      ((constantCaptureVariables source.length).map (·.subst σ))
      ((constantCaptureVariables source.length).map (·.subst τ))) :
    Ctx.SubstEq env U target σ τ source := by
  apply substitution_of_lookups formed
  intro index type lookup
  apply captures.rawLookup admitted ?_ lookup
  have bounded := lookup.lt
  simp only [constantCaptureVariables, List.mem_map, List.mem_reverse, List.mem_range]
  exact ⟨index, bounded, rfl⟩

end Lean4Lean.AnchoredSource.Adapted
