import Lean4Lean.Theory.Typing.AnchoredOriginalPairedApplication

/-! A domain-only query uses no argument anchor and no codomain row.
Transporting it between literal Pis gives the target domain relation at the
exact incoming support. Recovering a source domain certificate from the
transported Pi certificate is a separate obligation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Literal Pi exposure cannot change either displayed domain. Consequently
its ambient code demand can be recovered even when its row table is empty. -/
theorem TypeRelated.literalPiDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {A B C D prototypeDomain prototypeBody : VExpr}
    {n : Nat} {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (bridge : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody domain rows)) :
    TypeRelated env U registry target A C domain := by
  have base := bridge target .refl (.refl hTarget)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  have route := witness.leftExposure.insertion henv
  apply route.codeBack henv hscoped
  have related := witness.domainRelated
  simpa only [TypeRelated, witness.leftExposure.literalPi_components.1,
    witness.rightExposure.literalPi_components.1] using related

/-- The enclosing Pi observation also supplies a raw target-domain path,
including at empty domain support. This is target evidence from its concrete
display, not a source Pi-injectivity assumption. -/
theorem TypeRelated.literalPiDomainPath
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {A B C D prototypeDomain prototypeBody : VExpr}
    {n : Nat} {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (bridge : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody domain rows)) :
    TypeConversion env U target A C := by
  have base := bridge target .refl (.refl hTarget)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  apply (witness.leftExposure.insertion henv).pathBack henv
  simpa only [witness.leftExposure.literalPi_components.1,
    witness.rightExposure.literalPi_components.1] using witness.domains

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Embed the exact incoming type query in a Pi with no codomain requests.
The query keeps precisely the original source footprint. -/
noncomputable def CodeCert.domainOnly
    (domain : CodeCert env U registry target locals σ A support footprint)
    (B : VExpr) :
    CodeCert env U registry target locals σ (.forallE A B)
      (Profile.pi (A.subst σ) (B.subst σ.lift) support []) footprint := by
  simpa only [List.append_nil] using domain.piLiteral (B := B) .nil

/-- The semantic half of domain coherence requires neither an inhabitant
of the domain nor an observation of the function being assigned two types.
The resulting Pi certificate is retained for source-domain extraction. -/
theorem CodeCoherence.domainQuery
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B C D : VExpr} {n : Nat} {support : Profile n} {footprint : Footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (coherence : CodeCoherence env U registry target locals σ available
      (.forallE A B) (.forallE C D))
    (domain : CodeCert env U registry target locals σ A support footprint)
    (resources : footprint.Available available) :
    ∃ _result : CodeTransferResult env U registry target locals σ σ available
        (.forallE A B) (.forallE C D)
        (Profile.pi (A.subst σ) (B.subst σ.lift) support []),
      TypeRelated env U registry target (A.subst σ) (C.subst σ) support := by
  obtain ⟨result⟩ := coherence (CodeCert.domainOnly domain B) resources
  exact ⟨result, TypeRelated.literalPiDomain henv hscoped hTarget
    (by simpa only [subst] using result.related)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
