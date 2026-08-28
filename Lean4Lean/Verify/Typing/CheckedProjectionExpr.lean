import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.Typing.ProjectionRelation

namespace Lean4Lean

open Lean

/-- Native semantic evidence for one canonical primitive-projection target.
The target's type is not asserted as a free well-formedness field: it is an
ordinary derivation in the abstract type theory.  Executable refinement must
construct this derivation from the accepted projection candidate. -/
structure CheckedProjectionExpansion
    (env : VEnv) (U : Nat) (Gamma : List VExpr)
    (P : CanonicalProjectionExpansion) : Prop where
  installed : Nonempty
    (CanonicalProjectionExpansion.InstalledTyping env U Gamma P)
  targetTyping : ∃ targetType, env.HasType U Gamma P.target targetType

namespace CheckedProjectionExpansion

theorem mono
    (H : CheckedProjectionExpansion env U Gamma P)
    (Henv : env ≤ env') :
    CheckedProjectionExpansion env' U Gamma P where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.mono Henv⟩
  targetTyping := by
    rcases H.targetTyping with ⟨targetType, Htarget⟩
    exact ⟨targetType, Htarget.mono Henv⟩

theorem defeqCtx
    (H : CheckedProjectionExpansion env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    CheckedProjectionExpansion env U GammaTwo P where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.defeqCtx Henv Hctx⟩
  targetTyping := by
    rcases H.targetTyping with ⟨targetType, Htarget⟩
    exact ⟨targetType, Htarget.defeqDFC Henv Hctx⟩

theorem instL
    (H : CheckedProjectionExpansion env U Gamma P)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    CheckedProjectionExpansion env U'
      (Gamma.map (VExpr.instL substitution)) (P.instL substitution) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.instL Hlevels⟩
  targetTyping := by
    rcases H.targetTyping with ⟨targetType, Htarget⟩
    rw [CanonicalProjectionExpansion.target_instL]
    exact ⟨targetType.instL substitution, Htarget.instL Hlevels⟩

theorem weakN
    (H : CheckedProjectionExpansion env U Gamma P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    CheckedProjectionExpansion env U Gamma' (P.liftN n k) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.weakN Henv W⟩
  targetTyping := by
    rcases H.targetTyping with ⟨targetType, Htarget⟩
    rw [CanonicalProjectionExpansion.target_liftN]
    exact ⟨targetType.liftN n k, Htarget.weakN Henv W⟩

theorem instN
    (H : CheckedProjectionExpansion env U GammaOne P)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    CheckedProjectionExpansion env U Gamma
      (P.instN substitution k) where
  installed := by
    rcases H.installed with ⟨installed⟩
    exact ⟨installed.instN Henv W Hsubstitution⟩
  targetTyping := by
    rcases H.targetTyping with ⟨targetType, Htarget⟩
    rw [CanonicalProjectionExpansion.target_instN]
    exact ⟨targetType.inst substitution k,
      Htarget.instN Henv W Hsubstitution⟩

theorem majorWF
    (H : CheckedProjectionExpansion env U Gamma P) :
    VExpr.WF env U Gamma P.major := by
  rcases H.installed with ⟨installed⟩
  exact ⟨_, installed.majorType⟩

theorem targetWF
    (H : CheckedProjectionExpansion env U Gamma P) :
    VExpr.WF env U Gamma P.target :=
  H.targetTyping

end CheckedProjectionExpansion

/-- Environment-indexed primitive projection semantics with an exact
canonical target and an actual target typing derivation. -/
inductive CheckedTrProj (env : VEnv) (U : Nat) (Gamma : List VExpr)
    (structName : Name) (index : Nat) (major : VExpr) : VExpr → Prop where
  | canonical
      (P : CanonicalProjectionExpansion)
      (hstruct : P.structName = structName)
      (hindex : P.index = index)
      (hmajor : P.major = major)
      (Hchecked : CheckedProjectionExpansion env U Gamma P) :
      CheckedTrProj env U Gamma structName index major P.target

namespace CheckedTrProj

theorem mono
    (H : CheckedTrProj env U Gamma structName index major target)
    (Henv : env ≤ env') :
    CheckedTrProj env' U Gamma structName index major target := by
  cases H with
  | canonical P hstruct hindex hmajor Hchecked =>
      exact .canonical P hstruct hindex hmajor (Hchecked.mono Henv)

theorem defeqCtx
    (H : CheckedTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (Hctx : env.IsDefEqCtx U base GammaOne GammaTwo) :
    CheckedTrProj env U GammaTwo structName index major target := by
  cases H with
  | canonical P hstruct hindex hmajor Hchecked =>
      exact .canonical P hstruct hindex hmajor
        (Hchecked.defeqCtx Henv Hctx)

theorem instL
    (H : CheckedTrProj env U Gamma structName index major target)
    (Hlevels : ∀ level ∈ substitution, level.WF U') :
    CheckedTrProj env U' (Gamma.map (VExpr.instL substitution)) structName
      index (major.instL substitution) (target.instL substitution) := by
  cases H with
  | canonical P hstruct hindex hmajor Hchecked =>
      have Hcanonical : CheckedTrProj env U'
          (Gamma.map (VExpr.instL substitution)) structName index
          (major.instL substitution) (P.instL substitution).target :=
        .canonical (P.instL substitution) hstruct hindex
          (by simp [CanonicalProjectionExpansion.instL, hmajor])
          (Hchecked.instL Hlevels)
      simpa using Hcanonical

theorem weakN
    (H : CheckedTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.LiftN n k Gamma Gamma') :
    CheckedTrProj env U Gamma' structName index (major.liftN n k)
      (target.liftN n k) := by
  cases H with
  | canonical P hstruct hindex hmajor Hchecked =>
      have Hcanonical : CheckedTrProj env U Gamma' structName index
          (major.liftN n k) (P.liftN n k).target :=
        .canonical (P.liftN n k) hstruct hindex
          (by simp [CanonicalProjectionExpansion.liftN, hmajor])
          (Hchecked.weakN Henv W)
      simpa using Hcanonical

theorem instN
    (H : CheckedTrProj env U GammaOne structName index major target)
    (Henv : VEnv.Ordered env)
    (W : Ctx.InstN GammaZero substitution substitutionType k GammaOne Gamma)
    (Hsubstitution : env.HasType U GammaZero substitution substitutionType) :
    CheckedTrProj env U Gamma structName index (major.inst substitution k)
      (target.inst substitution k) := by
  cases H with
  | canonical P hstruct hindex hmajor Hchecked =>
      have Hcanonical : CheckedTrProj env U Gamma structName index
          (major.inst substitution k) (P.instN substitution k).target :=
        .canonical (P.instN substitution k) hstruct hindex
          (by simp [CanonicalProjectionExpansion.instN, hmajor])
          (Hchecked.instN Henv W Hsubstitution)
      simpa using Hcanonical

theorem sourceWF
    (H : CheckedTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma major := by
  cases H with
  | canonical P _ _ hmajor Hchecked =>
      simpa [hmajor] using Hchecked.majorWF

theorem targetWF
    (H : CheckedTrProj env U Gamma structName index major target) :
    VExpr.WF env U Gamma target := by
  cases H with
  | canonical P _ _ _ Hchecked => exact Hchecked.targetWF

/-- A checked projection target cannot mention a constant absent from its
actual abstract environment.  This is a consequence of target typing, not a
projection compatibility premise. -/
theorem noFreshConsts
    (H : CheckedTrProj env U Gamma structName index major target)
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : OnCtx Gamma (env.IsType U)) :
    target.containsAnyConst names = false :=
  VExpr.WF.noFreshConsts Henv Hfresh Hctx H.targetWF

end CheckedTrProj

/-- Strict concrete-to-abstract expression translation whose projection leaf
is tied to the surrounding environment, universe count, and local context.
This is the migration target for the legacy `TrExprS` relation. -/
inductive CheckedTrExprS (env : VEnv) (Us : List Name) :
    VLCtx → Expr → VExpr → Prop
  | bvar : Delta.find? (.inl index) = some (target, type) →
      CheckedTrExprS env Us Delta (.bvar index) target
  | fvar : Delta.find? (.inr fvarId) = some (target, type) →
      CheckedTrExprS env Us Delta (.fvar fvarId) target
  | sort : VLevel.ofLevel Us level = some targetLevel →
      CheckedTrExprS env Us Delta (.sort level) (.sort targetLevel)
  | const :
      env.constants name = some constant →
      levels.mapM (VLevel.ofLevel Us) = some targetLevels →
      levels.length = constant.uvars →
      CheckedTrExprS env Us Delta (.const name levels) (.const name targetLevels)
  | app :
      env.HasType Us.length Delta.toCtx fnTarget (.forallE domain body) →
      env.HasType Us.length Delta.toCtx argTarget domain →
      CheckedTrExprS env Us Delta fn fnTarget →
      CheckedTrExprS env Us Delta arg argTarget →
      CheckedTrExprS env Us Delta (.app fn arg) (.app fnTarget argTarget)
  | lam :
      env.IsType Us.length Delta.toCtx domainTarget →
      CheckedTrExprS env Us Delta domain domainTarget →
      CheckedTrExprS env Us ((none, .vlam domainTarget) :: Delta) body bodyTarget →
      CheckedTrExprS env Us Delta (.lam name domain body info)
        (.lam domainTarget bodyTarget)
  | forallE :
      env.IsType Us.length Delta.toCtx domainTarget →
      env.IsType Us.length (domainTarget :: Delta.toCtx) bodyTarget →
      CheckedTrExprS env Us Delta domain domainTarget →
      CheckedTrExprS env Us ((none, .vlam domainTarget) :: Delta) body bodyTarget →
      CheckedTrExprS env Us Delta (.forallE name domain body info)
        (.forallE domainTarget bodyTarget)
  | letE :
      env.HasType Us.length Delta.toCtx valueTarget typeTarget →
      CheckedTrExprS env Us Delta type typeTarget →
      CheckedTrExprS env Us Delta value valueTarget →
      CheckedTrExprS env Us ((none, .vlet typeTarget valueTarget) :: Delta)
        body bodyTarget →
      CheckedTrExprS env Us Delta (.letE name type value body nondep) bodyTarget
  | lit : env.ContainsLits literal →
      CheckedTrExprS env Us Delta literal.toConstructor target →
      CheckedTrExprS env Us Delta (.lit literal) target
  | mdata : CheckedTrExprS env Us Delta body target →
      CheckedTrExprS env Us Delta (.mdata data body) target
  | proj :
      CheckedTrExprS env Us Delta major majorTarget →
      CheckedTrProj env Us.length Delta.toCtx structName index majorTarget target →
      CheckedTrExprS env Us Delta (.proj structName index major) target

namespace CheckedTrExprS

theorem closed
    (H : CheckedTrExprS env Us Delta expression target) :
    Closed expression Delta.bvars := by
  induction H with
  | @bvar target type Delta index hfind =>
      simp [Closed]
      induction Delta generalizing index target type with
      | nil => cases hfind
      | cons declaration Delta ih =>
          match declaration, index with
          | (none, _), 0 => exact Nat.succ_pos _
          | (none, _), _ + 1 =>
              simp [VLCtx.find?, VLCtx.next, bind] at hfind
              obtain ⟨_, _, hfind, rfl, rfl⟩ := hfind
              exact Nat.succ_lt_succ (ih hfind)
          | (some _, _), _ =>
              simp [VLCtx.find?, VLCtx.next, bind] at hfind
              obtain ⟨_, _, hfind, rfl, rfl⟩ := hfind
              exact ih hfind
  | fvar | sort | const | lit | mdata => trivial
  | app _ _ _ _ ihFn ihArg => exact ⟨ihFn, ihArg⟩
  | lam _ _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | forallE _ _ _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | letE _ _ _ _ ihType ihValue ihBody =>
      exact ⟨ihType, ihValue, ihBody⟩
  | proj _ _ ihMajor => exact ihMajor

theorem fvarsIn
    (H : CheckedTrExprS env Us Delta expression target) :
    FVarsIn (· ∈ Delta.fvars) expression := by
  induction H with
  | fvar hfind => exact VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  | sort hlevel => exact ofLevel_hasMVar hlevel
  | const _ hlevels =>
      rw [List.mapM_eq_some] at hlevels
      intro _ hlevel
      have ⟨_, _, htranslated⟩ :=
        Lean4Lean.List.Forall₂.forall_exists_l hlevels _ hlevel
      exact ofLevel_hasMVar htranslated
  | bvar | lit | mdata => trivial
  | app _ _ _ _ ihFn ihArg => exact ⟨ihFn, ihArg⟩
  | lam _ _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | forallE _ _ _ _ ihDomain ihBody => exact ⟨ihDomain, ihBody⟩
  | letE _ _ _ _ ihType ihValue ihBody =>
      exact ⟨ihType, ihValue, ihBody⟩
  | proj _ _ ihMajor => exact ihMajor

theorem mono
    (H : CheckedTrExprS env Us Delta expression target)
    (Henv : env ≤ env') :
    CheckedTrExprS env' Us Delta expression target := by
  induction H with
  | bvar hfind => exact .bvar hfind
  | fvar hfind => exact .fvar hfind
  | sort hlevel => exact .sort hlevel
  | const hlookup hlevels hlength =>
      exact .const (Henv.constants hlookup) hlevels hlength
  | app hfn harg _ _ ihFn ihArg =>
      exact .app (hfn.mono Henv) (harg.mono Henv) ihFn ihArg
  | lam hdomain _ _ ihDomain ihBody =>
      exact .lam (hdomain.mono Henv) ihDomain ihBody
  | forallE hdomain hbody _ _ ihDomain ihBody =>
      exact .forallE (hdomain.mono Henv) (hbody.mono Henv)
        ihDomain ihBody
  | letE hvalue _ _ _ ihType ihValue ihBody =>
      exact .letE (hvalue.mono Henv) ihType ihValue ihBody
  | lit hliteral _ ih => exact .lit (hliteral.mono Henv) ih
  | mdata _ ih => exact .mdata ih
  | proj _ Hprojection ihMajor =>
      exact .proj ihMajor (Hprojection.mono Henv)

theorem weakBV
    (H : CheckedTrExprS env Us Delta expression target)
    (henv : VEnv.Ordered env)
    (W : VLCtx.BVLift Delta Delta' domainAmount domainCutoff
      targetAmount targetCutoff) :
    CheckedTrExprS env Us Delta'
      (expression.liftLooseBVars' domainCutoff domainAmount)
      (target.liftN targetAmount targetCutoff) := by
  induction H generalizing Delta' domainCutoff targetCutoff with
  | bvar hfind => exact .bvar (W.find? hfind)
  | fvar hfind => exact .fvar (W.find? hfind)
  | sort hlevel => exact .sort hlevel
  | const hlookup hlevels hlength => exact .const hlookup hlevels hlength
  | app hfn harg _ _ ihFn ihArg =>
      exact .app (hfn.weakN henv W.toCtx) (harg.weakN henv W.toCtx)
        (ihFn W) (ihArg W)
  | lam hdomain _ _ ihDomain ihBody =>
      exact .lam (hdomain.weakN henv W.toCtx)
        (ihDomain W) (ihBody (W.cons _))
  | forallE hdomain hbody _ _ ihDomain ihBody =>
      exact .forallE (hdomain.weakN henv W.toCtx)
        (hbody.weakN henv W.toCtx.succ)
        (ihDomain W) (ihBody (W.cons _))
  | letE hvalue _ _ _ ihType ihValue ihBody =>
      exact .letE (hvalue.weakN henv W.toCtx)
        (ihType W) (ihValue W) (ihBody (W.cons _))
  | lit hliteral _ ih =>
      refine .lit hliteral (Expr.liftLooseBVars_eq_self ?_ ▸ ih W :)
      exact Closed.toConstructor.looseBVarRange_le
  | mdata _ ih => exact .mdata (ih W)
  | proj _ Hprojection ihMajor =>
      exact .proj (ihMajor W) (Hprojection.weakN henv W.toCtx)

/-- Universe weakening of checked translation follows the concrete level
translation and the native projection certificate's proved substitution
operation. -/
theorem prependLevelParam
    (H : CheckedTrExprS env Us Delta expression target)
    (hDelta : Delta.WF env Us.length)
    (hfresh : fresh ∉ Us) :
    CheckedTrExprS env (fresh :: Us)
      (Delta.instL (VLevel.prependShift Us.length)) expression
      (target.instL (VLevel.prependShift Us.length)) := by
  let shift := VLevel.prependShift Us.length
  have hshift : ∀ level ∈ shift, level.WF (fresh :: Us).length := by
    simpa [shift] using VLevel.prependShift_wf (n := Us.length)
  induction H with
  | bvar hfind => exact .bvar (VLCtx.find?_instL hfind)
  | fvar hfind => exact .fvar (VLCtx.find?_instL hfind)
  | sort hlevel => exact .sort (VLevel.ofLevel_fresh_cons hfresh hlevel)
  | const hlookup hlevels harity =>
      exact .const hlookup
        (VLevel.mapM_ofLevel_fresh_cons hfresh hlevels) harity
  | app hfn harg _ _ ihFn ihArg =>
      exact .app
        (VLCtx.instL_toCtx _ ▸ hfn.instL hshift)
        (VLCtx.instL_toCtx _ ▸ harg.instL hshift)
        (ihFn hDelta) (ihArg hDelta)
  | lam hdomain _ _ ihDomain ihBody =>
      exact .lam
        (VLCtx.instL_toCtx _ ▸ hdomain.instL hshift)
        (ihDomain hDelta) (ihBody ⟨hDelta, nofun, hdomain⟩)
  | forallE hdomain hbody _ _ ihDomain ihBody =>
      exact .forallE
        (VLCtx.instL_toCtx _ ▸ hdomain.instL hshift)
        (VLCtx.instL_toCtx _ ▸ hbody.instL hshift)
        (ihDomain hDelta) (ihBody ⟨hDelta, nofun, hdomain⟩)
  | letE hvalue _ _ _ ihType ihValue ihBody =>
      exact .letE
        (VLCtx.instL_toCtx _ ▸ hvalue.instL hshift)
        (ihType hDelta) (ihValue hDelta)
        (ihBody ⟨hDelta, nofun, hvalue⟩)
  | lit hliteral _ ih => exact .lit hliteral (ih hDelta)
  | mdata _ ih => exact .mdata (ih hDelta)
  | proj _ Hprojection ihMajor =>
      exact .proj (ihMajor hDelta)
        (VLCtx.instL_toCtx _ ▸ Hprojection.instL hshift)

/-- Checked strict translations are well formed without an opaque projection
lemma: the projection case uses the target typing derivation retained by the
environment-indexed certificate. -/
theorem wf
    (H : CheckedTrExprS env Us Delta expression target)
    (henv : VEnv.Ordered env)
    (hDelta : VLCtx.WF env Us.length Delta) :
    VExpr.WF env Us.length Delta.toCtx target := by
  induction H with
  | bvar hfind | fvar hfind =>
      exact ⟨_, hDelta.find?_wf henv hfind⟩
  | sort hlevel =>
      exact ⟨_, VEnv.HasType.sort (.of_ofLevel hlevel)⟩
  | const hlookup hlevels hlength =>
      exact ⟨_, VEnv.HasType.const hlookup (.of_mapM_ofLevel hlevels)
        ((Lean4Lean.List.Forall₂.length_eq
          (List.mapM_eq_some.1 hlevels)).symm.trans hlength)⟩
  | app hfn harg _ _ => exact ⟨_, hfn.app harg⟩
  | lam hdomain _ _ _ ihBody =>
      rcases hdomain with ⟨_, hdomain⟩
      rcases ihBody ⟨hDelta, nofun, ⟨_, hdomain⟩⟩ with ⟨_, hbody⟩
      exact ⟨_, hdomain.lam hbody⟩
  | forallE hdomain hbody =>
      rcases hdomain with ⟨_, hdomain⟩
      rcases hbody with ⟨_, hbody⟩
      exact ⟨_, hdomain.forallE hbody⟩
  | letE hvalue _ _ _ _ _ ihBody =>
      exact ihBody ⟨hDelta, nofun, hvalue⟩
  | lit _ _ ih | mdata _ ih => exact ih hDelta
  | proj _ Hprojection _ => exact Hprojection.targetWF

end CheckedTrExprS

/-- Non-strict checked translation, used at normalization boundaries. -/
def CheckedTrExpr (env : VEnv) (Us : List Name) (Delta : VLCtx)
    (expression : Expr) (target : VExpr) : Prop :=
  ∃ strictTarget,
    CheckedTrExprS env Us Delta expression strictTarget ∧
      env.IsDefEqU Us.length Delta.toCtx strictTarget target

namespace CheckedTrExpr

theorem ofStrict
    (H : CheckedTrExprS env Us Delta expression target)
    (henv : VEnv.Ordered env)
    (hDelta : VLCtx.WF env Us.length Delta) :
    CheckedTrExpr env Us Delta expression target :=
  ⟨target, H, H.wf henv hDelta⟩

theorem defeq
    (H : CheckedTrExpr env Us Delta expression left)
    (henv : VEnv.WF env)
    (hDelta : OnCtx Delta.toCtx (env.IsType Us.length))
    (Hdefeq : env.IsDefEqU Us.length Delta.toCtx left right) :
    CheckedTrExpr env Us Delta expression right := by
  rcases H with ⟨strictTarget, Hstrict, Hleft⟩
  exact ⟨strictTarget, Hstrict, Hleft.trans henv hDelta Hdefeq⟩

theorem mono
    (H : CheckedTrExpr env Us Delta expression target)
    (Henv : env ≤ env') :
    CheckedTrExpr env' Us Delta expression target := by
  rcases H with ⟨strictTarget, Hstrict, Hdefeq⟩
  exact ⟨strictTarget, Hstrict.mono Henv, Hdefeq.mono Henv⟩

theorem wf
    (H : CheckedTrExpr env Us Delta expression target) :
    VExpr.WF env Us.length Delta.toCtx target := by
  rcases H with ⟨strictTarget, _, Hdefeq⟩
  rcases Hdefeq with ⟨type, Hdefeq⟩
  exact ⟨type, Hdefeq.hasType.2⟩

theorem fvarsIn
    (H : CheckedTrExpr env Us Delta expression target) :
    FVarsIn (· ∈ Delta.fvars) expression := by
  rcases H with ⟨_, Hstrict, _⟩
  exact Hstrict.fvarsIn

end CheckedTrExpr

def CheckedTrTyping (env : VEnv) (Us : List Name) (Delta : VLCtx)
    (expression type : Expr) (target targetType : VExpr) : Prop :=
  FVarsBelow Delta expression type ∧
    CheckedTrExprS env Us Delta expression target ∧
    CheckedTrExprS env Us Delta type targetType ∧
    env.HasType Us.length Delta.toCtx target targetType

end Lean4Lean
