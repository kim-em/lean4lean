import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReplay

/-! Restore the right endpoint's original assigned type after comparing
natural heads. The same finite conversion route is traversed outward, using
its retained original equality children in the opposite direction from
backward query preparation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- Inward replay may finish in a different source context and realization.
Only the target world and requested profile are shared. -/
theorem PrefixRoute.replayAcross
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals outputLocals : List Nat} {σ outputSubst : Subst}
    {available outputAvailable : Valuation}
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
        (CodeTransferResult env U registry target outputLocals σ outputSubst
          outputAvailable natural outputType profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target outputLocals σ outputSubst
      outputAvailable assigned outputType profile) := by
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

/-- An incoming semantic answer supplies the identity case; no diagonal
type semantics are inferred merely from a source certificate. The left
realization is independent of the right endpoint's source substitution. -/
theorem PrefixRoute.restore
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {leftSubst σ : Subst}
    {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Joints env registry route)
    {profile : Profile n} {inputType : VExpr}
    (incoming : CodeTransferResult env U registry target locals leftSubst σ available
      inputType natural profile) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst σ available
      inputType assigned profile) := by
  induction route with
  | done => exact ⟨incoming⟩
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) incoming
  | convert plan term rest ih =>
    obtain ⟨inner⟩ := ih (fun call => calls (.tail call)) incoming
    obtain ⟨level, backwards⟩ := conversionBackwardJoint henv hscoped below plan
      (fun call => calls (.conversion call))
    obtain ⟨outer⟩ := inner.certificate.transfer_graded henv hscoped hTarget closed
      (backwards.symm target locals σ σ available closed hTarget substitutions fits).1
      inner.available
    exact ⟨⟨outer.footprint, outer.certificate, outer.available,
      inner.related.trans henv outer.related⟩⟩

/-- Peel the left endpoint, compare the natural types, and restore the
right endpoint. Each route consumes only its own original equality children
and its own source substitutions and fitted context. -/
theorem PrefixRoute.compareHeads
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {leftSource rightSource target : List VExpr} {leftLocals rightLocals : List Nat}
    {σ τ : Subst} {leftAvailable rightAvailable : Valuation}
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (leftFits : PairedFits env U registry leftSource target leftLocals σ σ leftAvailable)
    (rightFits : PairedFits env U registry rightSource target rightLocals τ τ rightAvailable)
    {left : EndpointState sourceEnv U leftSource leftExpression leftAssigned}
    {leftHead : EndpointState sourceEnv U leftSource leftExpression leftNatural}
    {right : EndpointState sourceEnv U rightSource rightExpression rightAssigned}
    {rightHead : EndpointState sourceEnv U rightSource rightExpression rightNatural}
    (leftRoute : PrefixRoute sourceEnv U leftSource leftExpression left leftHead)
    (rightRoute : PrefixRoute sourceEnv U rightSource rightExpression right rightHead)
    (leftCalls : PrefixCall.Joints env registry leftRoute)
    (rightCalls : PrefixCall.Joints env registry rightRoute)
    {profile : Profile n}
    (natural : ∀ {footprint}, CodeCert env U registry target leftLocals σ leftNatural profile footprint →
      footprint.Available leftAvailable → Nonempty
        (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
          leftNatural rightNatural profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target leftLocals σ leftAssigned profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      leftAssigned rightAssigned profile) := by
  obtain ⟨compared⟩ := leftRoute.replayAcross henv hscoped below leftClosed hTarget
    leftSubstitutions leftFits leftCalls natural certificate resources
  exact rightRoute.restore henv hscoped below rightClosed hTarget
    rightSubstitutions rightFits rightCalls compared

/-- Raw comparison composes the same actual routes and needs no observation
support. The head comparison must supply the middle path independently of
whether its finite code query was empty. -/
theorem PrefixRoute.comparePath
    {leftEnv rightEnv env : VEnv} {U : Nat}
    (henv : env.Ordered) (leftLe : leftEnv ≤ env) (rightLe : rightEnv ≤ env)
    {leftSource rightSource target : List VExpr} {σ τ : Subst}
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    {left : EndpointState leftEnv U leftSource leftExpression leftAssigned}
    {leftHead : EndpointState leftEnv U leftSource leftExpression leftNatural}
    {right : EndpointState rightEnv U rightSource rightExpression rightAssigned}
    {rightHead : EndpointState rightEnv U rightSource rightExpression rightNatural}
    (leftRoute : PrefixRoute leftEnv U leftSource leftExpression left leftHead)
    (rightRoute : PrefixRoute rightEnv U rightSource rightExpression right rightHead)
    (natural : TypeConversion env U target (leftNatural.subst σ) (rightNatural.subst τ)) :
    TypeConversion env U target (leftAssigned.subst σ) (rightAssigned.subst τ) :=
  ((leftRoute.targetPath henv leftLe hTarget leftSubstitutions).trans natural).trans
    (rightRoute.targetPath henv rightLe hTarget rightSubstitutions).symm

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
