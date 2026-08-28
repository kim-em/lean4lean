import Lean4Lean.Theory.Inductive

namespace Lean4Lean

/-- Two abstract forall types have the same first `arity` domains.  Their
residual bodies may differ. -/
inductive VExpr.SameForallDomains : Nat → VExpr → VExpr → Prop
  | nil : VExpr.SameForallDomains 0 source target
  | cons : VExpr.SameForallDomains arity sourceBody targetBody →
      VExpr.SameForallDomains (arity + 1)
        (.forallE domain sourceBody) (.forallE domain targetBody)

/-- Expose the exact shared domain list retained by
`SameForallDomains`; only the two residuals may differ. -/
theorem VExpr.SameForallDomains.exists_wrapForalls
    (H : VExpr.SameForallDomains arity source target) :
    ∃ domains sourceTail targetTail,
      domains.length = arity ∧
      source = VExpr.wrapForalls domains sourceTail ∧
      target = VExpr.wrapForalls domains targetTail := by
  induction H with
  | nil => exact ⟨[], _, _, rfl, rfl, rfl⟩
  | @cons _ _ _ domain _ ih =>
    rcases ih with ⟨domains, sourceTail, targetTail, hlength,
      hsource, htarget⟩
    exact ⟨domain :: domains, sourceTail, targetTail, by simp [hlength], by
      simp [VExpr.wrapForalls, hsource], by
      simp [VExpr.wrapForalls, htarget]⟩

/-- Transport the independent raw constructor-parameter judgment across an
exact shared forall-domain prefix.  The constructor residual is irrelevant. -/
theorem VExpr.SameForallDomains.ctorParameterShape
    {env : VEnv} {decl : VInductDecl} {params : List VExpr}
    {source target : VConstVal}
    (Hsame : VExpr.SameForallDomains decl.nparams source.type target.type)
    (Htarget : decl.CtorParameterShape env params target) :
    decl.CtorParameterShape env params source := by
  rcases Hsame.exists_wrapForalls with
    ⟨domains, sourceTail, targetTail, hlength, hsource, htarget⟩
  rcases Htarget with ⟨targetDomains, targetResidual, htake, hparams⟩
  have htargetTake : target.type.takeForalls decl.nparams =
      some (domains, targetTail) := by
    rw [htarget, ← hlength]
    exact VExpr.takeForalls_wrapForalls domains targetTail
  have hpairs : (targetDomains, targetResidual) = (domains, targetTail) :=
    Option.some.inj (htake.symm.trans htargetTake)
  cases hpairs
  exact ⟨domains, sourceTail, by
    rw [hsource, ← hlength]
    exact VExpr.takeForalls_wrapForalls domains sourceTail,
    hparams⟩

namespace VExpr.NestedExprExpansion

/-- Proof-relevant evidence that one structural expansion used no lowering
leaf.  This is intentionally attached to the exact expansion proof retained
by the producer, rather than inferred from an unrestricted expression. -/
inductive NoHit {leaf : Nat → VExpr → VExpr → Prop} :
    {depth : Nat} → {source target : VExpr} →
      NestedExprExpansion leaf depth source target → Prop
  | bvar : NoHit (.bvar : NestedExprExpansion leaf depth (.bvar index)
      (.bvar index))
  | sort : NoHit (.sort : NestedExprExpansion leaf depth (.sort level)
      (.sort level))
  | const : NoHit (.const : NestedExprExpansion leaf depth (.const name levels)
      (.const name levels))
  | app : NoHit Hfn → NoHit Harg → NoHit (.app Hfn Harg)
  | lam : NoHit Hdomain → NoHit Hbody → NoHit (.lam Hdomain Hbody)
  | forallE : NoHit Hdomain → NoHit Hbody →
      NoHit (.forallE Hdomain Hbody)

/-- A leaf-free structural expansion is literal equality. -/
theorem NoHit.eq {leaf : Nat → VExpr → VExpr → Prop} {depth : Nat}
    {source target : VExpr}
    {expansion : NestedExprExpansion leaf depth source target}
    (H : NestedExprExpansion.NoHit expansion) :
    source = target := by
  induction H with
  | bvar | sort | const => rfl
  | app _ _ ihFn ihArg => simp [ihFn, ihArg]
  | lam _ _ ihDomain ihBody => simp [ihDomain, ihBody]
  | forallE _ _ ihDomain ihBody => simp [ihDomain, ihBody]

/-- Reflexive expansion has a canonical proof containing no lowering leaf. -/
theorem NoHit.refl (leaf : Nat → VExpr → VExpr → Prop)
    (depth : Nat) (e : VExpr) :
    ∃ H : NestedExprExpansion leaf depth e e, NoHit H := by
  induction e generalizing depth with
  | bvar => exact ⟨.bvar, .bvar⟩
  | sort => exact ⟨.sort, .sort⟩
  | const => exact ⟨.const, .const⟩
  | app _ _ ihFn ihArg =>
    rcases ihFn depth with ⟨Hfn, HfnNoHit⟩
    rcases ihArg depth with ⟨Harg, HargNoHit⟩
    exact ⟨.app Hfn Harg, .app HfnNoHit HargNoHit⟩
  | lam _ _ ihDomain ihBody =>
    rcases ihDomain depth with ⟨Hdomain, HdomainNoHit⟩
    rcases ihBody (depth + 1) with ⟨Hbody, HbodyNoHit⟩
    exact ⟨.lam Hdomain Hbody, .lam HdomainNoHit HbodyNoHit⟩
  | forallE _ _ ihDomain ihBody =>
    rcases ihDomain depth with ⟨Hdomain, HdomainNoHit⟩
    rcases ihBody (depth + 1) with ⟨Hbody, HbodyNoHit⟩
    exact ⟨.forallE Hdomain Hbody, .forallE HdomainNoHit HbodyNoHit⟩

/-- Lifting both sides of a leaf-free expansion stays leaf-free.  Equality
of the original endpoints lets this avoid any assumption about lifting the
leaf relation itself. -/
theorem NoHit.liftN
    {leaf : Nat → VExpr → VExpr → Prop} {depth : Nat}
    {source target : VExpr}
    {expansion : NestedExprExpansion leaf depth source target}
    (H : NoHit expansion) (amount cutoff : Nat) :
    ∃ expansion' : NestedExprExpansion leaf (depth + amount)
        (source.liftN amount cutoff) (target.liftN amount cutoff),
      NoHit expansion' := by
  rw [H.eq]
  exact NoHit.refl leaf (depth + amount) (target.liftN amount cutoff)

/-- A structural expansion cannot take a lowering leaf when the source is
free of every constant that a genuine leaf must contain.  This converts the
independent expansion specification's source-side freshness invariant into
proof-relevant evidence about the exact retained expansion derivation. -/
theorem NoHit.ofSourceFree
    {leaf : Nat → VExpr → VExpr → Prop} {depth : Nat}
    {source target : VExpr}
    (hleafSource : ∀ {depth input output}, leaf depth input output →
      input.containsAnyConst names = true)
    (H : NestedExprExpansion leaf depth source target)
    (hsource : source.containsAnyConst names = false) :
    NestedExprExpansion.NoHit H := by
  induction H with
  | hit Hleaf => simp [hleafSource Hleaf] at hsource
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg =>
    have hparts := Bool.or_eq_false_iff.mp hsource
    exact .app (ihFn hparts.1) (ihArg hparts.2)
  | lam _ _ ihDomain ihBody =>
    have hparts := Bool.or_eq_false_iff.mp hsource
    exact .lam (ihDomain hparts.1) (ihBody hparts.2)
  | forallE _ _ ihDomain ihBody =>
    have hparts := Bool.or_eq_false_iff.mp hsource
    exact .forallE (ihDomain hparts.1) (ihBody hparts.2)

end VExpr.NestedExprExpansion

namespace VExpr.NestedForallPrefixExpansion

/-- No lowering leaf occurs in any of the retained common-parameter domains.
The residual constructor body is deliberately unrestricted. -/
inductive DomainsNoHit {leaf : Nat → VExpr → VExpr → Prop} :
    {depth arity : Nat} → {source target : VExpr} →
      (H : NestedForallPrefixExpansion leaf depth arity source target) → Prop
  | nil : DomainsNoHit (.nil Hbody)
  | cons : Hdomain.NoHit → DomainsNoHit Hbody →
      DomainsNoHit (.cons Hdomain Hbody)

/-- If the exact retained prefix contains no lowering leaf in its domains,
the source and expanded constructors have literally the same common forall
domains. -/
theorem DomainsNoHit.sameForallDomains
    {leaf : Nat → VExpr → VExpr → Prop} {depth arity : Nat}
    {source target : VExpr}
    {expansion : NestedForallPrefixExpansion leaf depth arity source target}
    (H : NestedForallPrefixExpansion.DomainsNoHit expansion) :
    VExpr.SameForallDomains arity source target := by
  induction H with
  | nil => exact .nil
  | cons Hdomain _ ih =>
    rw [Hdomain.eq]
    exact .cons ih

end VExpr.NestedForallPrefixExpansion

/-- A positionally retained nested constructor prefix transports the raw
parameter-shape judgment back to the source constructor as soon as its exact
domain expansions are proved leaf-free. -/
theorem VInductDecl.NestedConstructorExpansion.sourceCtorParameterShape
    {env : VEnv} {decl : VInductDecl} {params : List VExpr}
    {leaf : Nat → VExpr → VExpr → Prop} {source target : VConstVal}
    (H : VInductDecl.NestedConstructorExpansion leaf decl.nparams
      source target)
    (HnoHit : H.parameters.DomainsNoHit)
    (Htarget : decl.CtorParameterShape env params target) :
    decl.CtorParameterShape env params source :=
  HnoHit.sameForallDomains.ctorParameterShape Htarget

/-- Raw constructor parameter formation transports along a leaf-free exact
nested prefix, while allowing the expanded/source declarations to carry the
same arities propositionally rather than definitionally. -/
theorem VInductDecl.NestedConstructorExpansion.sourceCtorParameterShapeOf
    {env : VEnv} {sourceDecl expandedDecl : VInductDecl}
    {params : List VExpr} {leaf : Nat → VExpr → VExpr → Prop}
    {source target : VConstVal}
    (H : VInductDecl.NestedConstructorExpansion leaf sourceDecl.nparams
      source target)
    (HnoHit : H.parameters.DomainsNoHit)
    (huvars : expandedDecl.uvars = sourceDecl.uvars)
    (hnparams : expandedDecl.nparams = sourceDecl.nparams)
    (Htarget : expandedDecl.CtorParameterShape env params target) :
    sourceDecl.CtorParameterShape env params source := by
  have Htarget' : sourceDecl.CtorParameterShape env params target := by
    simpa [VInductDecl.CtorParameterShape, VInductDecl.ParamsDefEq,
      huvars, hnparams] using Htarget
  exact H.sourceCtorParameterShape HnoHit Htarget'

end Lean4Lean
