import Lean4Lean.Verify.Inductive.Recursor.Telescope
import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean

namespace VerifyInductive

namespace Expr.ForallTelescopeTypeTranslation

/-- Restriction evidence for only the proper forall prefix of a telescope.
The residual is deliberately omitted: nested restoration changes the
current-family major domain, while the normalized index domains preceding it
remain in the common pre-block environment. -/
inductive PrefixUsesOnly (changed : Name → Prop) :
    ∀ {env : VEnv} {levelParams : List Name} {ctx : VLCtx}
      {source : Expr} {arity : Nat} {target : VExpr},
      Expr.ForallTelescopeTypeTranslation env levelParams ctx source arity
        target → Prop where
  | nil : PrefixUsesOnly changed (.nil Htranslation Htype)
  | cons : Hdomain.UsesOnly changed → HdomainType.UsesOnly changed →
      PrefixUsesOnly changed Hbody →
      PrefixUsesOnly changed (.cons Hdomain HdomainType Hbody)

/-- A telescope translated before any selected names are installed carries
canonical restriction evidence at every binder.  Unlike a whole-expression
restriction, this theorem deliberately makes no assertion about the final
residual. -/
theorem PrefixUsesOnly.of_constants
    (H : Expr.ForallTelescopeTypeTranslation env levelParams ctx source arity
      target)
    (Hconstants : ∀ {name ci}, env.constants name = some ci →
      ¬ changed name) :
    PrefixUsesOnly changed H := by
  induction H with
  | nil Htranslation Htype =>
    exact PrefixUsesOnly.nil
      (Htranslation := Htranslation) (Htype := Htype)
  | cons Hdomain HdomainType Hbody IH =>
    exact .cons
      (Hdomain.usesOnly_of_constants Hconstants)
      (HdomainType.usesOnly_of_constants Hconstants)
      IH

/-- Restriction evidence established before an environment extension remains
attached to the monotonically transported telescope derivation. -/
theorem PrefixUsesOnly.mono
    {env env' : VEnv} (henv : env ≤ env')
    {H : Expr.ForallTelescopeTypeTranslation env levelParams ctx source arity
      target}
    (HU : PrefixUsesOnly changed H) :
    PrefixUsesOnly changed (H.mono henv) := by
  induction H with
  | nil Htranslation Htype =>
    cases HU with
    | nil =>
      exact PrefixUsesOnly.nil
        (Htranslation := Htranslation.mono henv)
        (Htype := Htype.mono henv)
  | cons Hdomain HdomainType Hbody IH =>
    cases HU with
    | cons HdomainUses HdomainTypeUses HbodyUses =>
      exact .cons (HdomainUses.mono henv) (HdomainTypeUses.mono henv)
        (IH HbodyUses)

/-- Splitting a restricted telescope preserves the restriction evidence on
the exact suffix.  This is the proof-indexed companion to
`ForallTelescopeTypeTranslation.dropPrefix`; nested restoration uses it to
discard the common parameter prefix and retain only the original index
domains. -/
theorem PrefixUsesOnly.dropPrefix
    (H : Expr.ForallTelescopeTypeTranslation env levelParams ctx source
      (suffixArity + prefixArity) target)
    (HU : PrefixUsesOnly changed H) :
    ∃ prefixDomains suffixSource suffixTarget,
      prefixDomains.length = prefixArity ∧
      Expr.ForallTelescope source prefixArity suffixSource ∧
      target = VExpr.wrapForalls prefixDomains suffixTarget ∧
      ∃ Hsuffix : Expr.ForallTelescopeTypeTranslation env levelParams
          (abstractForallContext prefixDomains ctx)
          suffixSource suffixArity suffixTarget,
        PrefixUsesOnly changed Hsuffix := by
  induction prefixArity generalizing ctx source target with
  | zero =>
    refine ⟨[], source, target, rfl, .nil source, rfl, ?_⟩
    let Hsuffix : Expr.ForallTelescopeTypeTranslation env levelParams
        (abstractForallContext [] ctx) source suffixArity target := by
      simpa [abstractForallContext] using H
    refine ⟨Hsuffix, ?_⟩
    simpa [Hsuffix, abstractForallContext] using HU
  | succ prefixArity ih =>
    cases H with
    | @cons ctx domain domainTarget body arity bodyTarget name binderInfo
        Hdomain HdomainType Hbody =>
      cases HU with
      | cons HdomainUses HdomainTypeUses HbodyUses =>
        rcases ih Hbody HbodyUses with
          ⟨domains, suffixSource, suffixTarget, hlength, Hsource,
            htarget, Hsuffix, HsuffixUses⟩
        refine ⟨domainTarget :: domains, suffixSource, suffixTarget,
          by simp [hlength], .cons Hsource, ?_, ?_, ?_⟩
        · simp [VExpr.wrapForalls, htarget]
        · simpa [abstractForallContext, List.map_append,
            List.append_assoc] using Hsuffix
        · simpa [abstractForallContext, List.map_append,
            List.append_assoc] using HsuffixUses

/-- A concrete, typed replacement for the unique residual leaf of a
translated forall telescope.  This relation is proof-indexed so no
`Prop`-to-`Type` elimination or choice is hidden in the transport theorem. -/
inductive ResidualReplacement (targetEnv : VEnv) :
    ∀ {sourceEnv : VEnv} {levelParams : List Name} {ctx : VLCtx}
      {source : Expr} {arity : Nat} {target : VExpr},
      Expr.ForallTelescopeTypeTranslation sourceEnv levelParams ctx source
        arity target → Prop where
  | nil
      (sourceEnv : VEnv) (levelParams : List Name) (ctx : VLCtx)
      (source : Expr) (oldTarget target : VExpr)
      (HoldTranslation : TrExprS sourceEnv levelParams ctx source oldTarget)
      (HoldType : sourceEnv.IsType levelParams.length ctx.toCtx oldTarget)
      (Htranslation : TrExprS targetEnv levelParams ctx source target)
      (Htype : targetEnv.IsType levelParams.length ctx.toCtx target) :
      ResidualReplacement targetEnv
        (.nil HoldTranslation HoldType)
  | cons
      (sourceEnv : VEnv) (levelParams : List Name) (ctx : VLCtx)
      (name : Name) (binderInfo : BinderInfo)
      (domain body : Expr) (domainTarget bodyTarget : VExpr)
      (Hdomain : TrExprS sourceEnv levelParams ctx domain domainTarget)
      (HdomainType : sourceEnv.IsType levelParams.length ctx.toCtx
        domainTarget)
      (Hbody : Expr.ForallTelescopeTypeTranslation sourceEnv levelParams
        ((none, .vlam domainTarget) :: ctx) body arity bodyTarget) :
      ResidualReplacement targetEnv Hbody →
      ResidualReplacement targetEnv
        (.cons (name := name) (bi := binderInfo)
          Hdomain HdomainType Hbody)

/-- The dummy `Sort 0` residual used by normalized source headers is
environment-independent.  Consequently every exact telescope ending in that
residual has a canonical replacement witness in any target environment; only
its proper binder prefix needs restriction evidence. -/
theorem ResidualReplacement.sortZero
    (H : Expr.ForallTelescopeTypeTranslation sourceEnv levelParams ctx
      source arity target)
    (Htelescope : Expr.ForallTelescope source arity
      (.sort (.zero : Level))) :
    ResidualReplacement targetEnv H := by
  induction H with
  | nil HoldTranslation HoldType =>
    cases Htelescope
    exact ResidualReplacement.nil _ _ _ _ _ _
      HoldTranslation HoldType
      (TrExprS.sort (Us := levelParams) (u := (.zero : Level))
        (u' := (.zero : VLevel)) rfl)
      ⟨.succ .zero,
        VEnv.HasType.sort
          (VLevel.WF.of_ofLevel (ls := levelParams) (l := (.zero : Level))
            (l' := (.zero : VLevel)) rfl)⟩
  | cons Hdomain HdomainType Hbody ih =>
    cases Htelescope with
    | cons Htail =>
      exact ResidualReplacement.cons _ _ _ _ _ _ _ _ _
        Hdomain HdomainType Hbody (ih Htail)

/-- Rebase the unchanged normalized prefix and splice in the independently
reconstructed restored residual.  The output target is existential because
the replacement residual generally differs from the lowered one. -/
theorem rebasePrefixReplaceResidual
    (E : VEnv.LEExcept changed sourceEnv targetEnv)
    (H : Expr.ForallTelescopeTypeTranslation sourceEnv levelParams ctx
      source arity target)
    (Hprefix : PrefixUsesOnly changed H)
    (Hresidual : ResidualReplacement targetEnv H) :
    ∃ target', Expr.ForallTelescopeTypeTranslation targetEnv levelParams ctx
      source arity target' := by
  induction H with
  | nil HoldTranslation HoldType =>
    cases Hprefix
    cases Hresidual with
    | nil _ _ _ _ _ target _ _ Htranslation Htype =>
      exact ⟨target, .nil Htranslation Htype⟩
  | cons Hdomain HdomainType Hbody IH =>
    cases Hprefix with
    | cons HdomainUses HdomainTypeUses HbodyUses =>
      cases Hresidual with
      | cons _ _ _ _ _ _ _ _ _ _ _ _ HbodyResidual =>
        rcases IH HbodyUses HbodyResidual with ⟨bodyTarget, Hbody'⟩
        exact ⟨.forallE _ bodyTarget,
          .cons
            (Hdomain.rebaseExcept E HdomainUses)
            (HdomainType.rebaseExcept E HdomainTypeUses)
            Hbody'⟩

end Expr.ForallTelescopeTypeTranslation

end VerifyInductive

end Lean4Lean
