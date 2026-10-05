import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureSubstitution
import Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan

/-! Read the original declared-domain conversions retained by the finite
capture tree. These paths connect selected record requests to constructor
fields without changing the requests' frozen input or support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilyCaptures.seedArguments
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {expressions : List VExpr} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint) :
    RankedData.Arguments env U (relations env U registry n) target keys
      (expressions.map (·.subst σ)) (expressions.map (·.subst σ)) := by
  match captures with
  | .nil => exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    exact .cons anchor tail.seedArguments
termination_by sizeOf captures
decreasing_by simp_wf; omega

theorem FamilyCaptures.seedSubstitution
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target source locals σ
      (constantCaptureVariables source.length) keys footprint)
    (formed : OnCtx source (env.IsType U)) :
    Ctx.SubstEq env U target σ σ source :=
  captures.rawSubstitution formed captures.seedArguments

theorem FamilyCaptures.lookupDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {expressions : List VExpr} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    {position index : Nat} {key : DataRequest (Profile n)} {type : VExpr}
    (keyAt : keys[position]? = some key)
    (expressionAt : expressions[position]? = some (.bvar index))
    (lookup : Lookup source index type) :
    TypeConversion env U target key.domain (type.subst σ) := by
  match captures, position with
  | .nil, _ => simp at keyAt
  | .cons stored value adapter alignment anchor tail, 0 =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at keyAt expressionAt
    cases keyAt
    cases expressionAt
    cases stored.uniq lookup
    exact alignment.path
  | .cons stored value adapter alignment anchor tail, position + 1 =>
    exact tail.lookupDomain keyAt expressionAt lookup
termination_by sizeOf captures
decreasing_by simp_wf; omega

theorem FamilyCaptures.declaredDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {domains target arguments : List VExpr} {locals : List Nat}
    {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (length : arguments.length = domains.length)
    (captures : FamilyCaptures env U registry target domains.reverse locals
      (nativeCaptureSubst arguments) (constantCaptureVariables domains.length) keys footprint)
    {position : Nat} {key : DataRequest (Profile n)}
    (bound : position < domains.length) (keyAt : keys[position]? = some key) :
    TypeConversion env U target key.domain
      (domains[position].subst (nativeCaptureSubst (arguments.take position))) := by
  have lookup : Lookup domains.reverse (domains.length - 1 - position)
      (domains[position].liftN (domains.length - position)) := by
    simpa only [List.append_nil] using Lookup.reverse_append domains [] position bound
  have expressionAt : (constantCaptureVariables domains.length)[position]? =
      some (.bvar (domains.length - 1 - position)) := by
    rw [List.getElem?_eq_getElem (by simp only [constantCaptureVariables,
      List.length_map, List.length_reverse, List.length_range]; exact bound)]
    simp only [constantCaptureVariables, List.getElem_map, List.getElem_reverse,
      List.length_range, List.getElem_range]
  have path := captures.lookupDomain keyAt expressionAt lookup
  have domainEq : (domains[position].liftN (domains.length - position)).subst
      (nativeCaptureSubst arguments) =
      domains[position].subst (nativeCaptureSubst (arguments.take position)) := by
    rw [← lift'_consN_skipN (k := 0), subst_lift']
    simp only [Lift.consN]
    rw [← length, nativeCaptureSubst_prefix _ _ (by omega)]
  simpa only [domainEq] using path

end Lean4Lean.AnchoredSource.Adapted
