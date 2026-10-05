import Lean4Lean.Theory.Typing.AnchoredSourceLambdaBeta
import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedLambdaFuture
import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedLambdaBehavior

/-! The concrete future body/code producer for an original lambda equality.
Every semantic call below is to its original body or codomain child. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem admitted_right (henv : env.Ordered) (hscoped : registry.Scoped)
    (h : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, (Related.symm henv second).left_diagonal⟩

theorem AdaptedLambdaTypeResult.futureOutputs
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {key : Key n} {output : Atom n} {domainSupport packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (fixed : AdaptedLambdaTypeResult env U registry target locals left available
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) A B body other key output domainSupport)
    (originalDomain : AdaptedJoint env U registry source A A (.sort domainLevel))
    (originalBody : AdaptedJoint env U registry (A :: source) body other B)
    (originalCodomain : AdaptedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (closed : available.AtomClosed)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (leftBody : env.HasType U (A :: source) body B)
    (rightBody : env.HasType U (A' :: source) other B)
    (substitutions : Ctx.SubstEq env U target left right source)
    (fits : PairedFits env U registry source target locals left right available)
    (domain : CodeCert env U registry target locals left A domainSupport domainFootprint)
    (guard : LambdaGuard env U registry target left A key domainSupport)
    (observation : Obs env U registry target (Locals.push locals)
      (left.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    {future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (admitted : Admitted env U registry future (key.rename ρ) x y) :
    TypeRelated env U registry future
      (B.subst ((left.lift_r ρ).cons x)) (B.subst ((left.lift_r ρ).cons y))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A body).subst left).lift' ρ) x)
      (.app (((VExpr.lam A body).subst left).lift' ρ) y)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A' other).subst right).lift' ρ) x)
      (.app (((VExpr.lam A' other).subst right).lift' ρ) y)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) ∧
    Related env U registry future
      (.app (((VExpr.lam A body).subst left).lift' ρ) x)
      (.app (((VExpr.lam A' other).subst right).lift' ρ) x)
      (B.subst ((left.lift_r ρ).cons x)) (.singleton (output.rename ρ))
      (fixed.resultSupport.rename ρ) := by
  let fixed' := fixed.future henv insertion
  have fits' := fits.future henv insertion
  have substitutions' := substitutions.future henv insertion
  have domain' := domain.future henv insertion
  have guard' := guard.future henv insertion
  have observation' := observation.future henv insertion
  simp only [subst_cons_future, Profile.rename_singleton] at observation'
  have pack' := pack.rename ρ
  have covered' : ∀ atom ∈ (packed.rename ρ).atoms,
      atom ∈ (key.input.rename ρ).atoms := by
    intro atom hm
    obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hm
    subst atom
    exact List.mem_map_of_mem (covered original horiginal)
  have domainAvailable' := domainAvailable.rename ρ
  have outsideAvailable' := outsideAvailable.rename ρ
  have hFuture := insertion.targetWF henv
  have hx := admitted.left_diagonal
  have hy := admitted_right henv hscoped admitted
  have lx := fixed'.atArgument henv hscoped originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ly := fixed'.atArgument henv hscoped originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions'.left fits'.left domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hy
  have rx := fixed'.atArgument henv hscoped originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hx
  have ry := fixed'.atArgument henv hscoped originalDomain originalBody originalCodomain (closed.rename ρ) domains.hasType.1
    hFuture substitutions' fits' domain' guard' observation' pack' covered'
    domainAvailable' outsideAvailable' hy
  obtain ⟨code, leftOutput, rightOutput, crossOutput⟩ :=
    LambdaArgumentResult.outputs henv hscoped fixed'.outputTyped lx ly rx ry
  have argumentPair := guard'.path.cast admitted.2.1
  have expanded := lambda_beta_outputs henv hFuture substitutions' domains codomain
    leftBody rightBody argumentPair leftOutput rightOutput crossOutput
  have support_eq : fixed'.resultSupport = fixed.resultSupport.rename ρ := rfl
  rw [support_eq] at expanded
  exact ⟨code, by simpa only [lift'_subst] using expanded⟩

end Lean4Lean.AnchoredSource
