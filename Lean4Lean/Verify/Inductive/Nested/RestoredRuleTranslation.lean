import Lean4Lean.Verify.Inductive.Nested.AuxRecNames
import Lean4Lean.Verify.Inductive.Nested.RestorationTranslation

/-! # Translation of restored recursor rules

The right-hand side of a restored recursor rule is the executable restoration
(`restoreNested`) of the lowered rule. `NestedRestorationOpening.translatesLambda`
(`Nested/RestorationTranslation.lean`) shows that it translates in the target
environment of a renaming restoration substitution, given that the syntax the
executable copies verbatim avoids the restorable names. This file restates
that theorem with its hypotheses on the stored lowered input, in the form in
which they are available for lowered rules (`Expr.HitTrailAvoids`,
`Expr.LamPrefixAvoids`, `Expr.HitShapeTele`).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

namespace VerifyInductive

theorem Expr.HitTrailAvoids.toHitTrailWith {heads names : List Name} {np : Nat}
    {e : Expr} (H : e.HitTrailAvoids heads names np) :
    e.HitTrailWith heads np (·.AvoidsConsts names) := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | app _ _ h ihf iha => exact .app ihf iha h
  | lam _ _ ihd ihb => exact .lam ihd ihb
  | forallE _ _ ihd ihb => exact .forallE ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

theorem Expr.LamPrefixAvoids.lamDomainsOnly {names : List Name} :
    ∀ {n : Nat} {e : Expr}, e.LamPrefixAvoids names n →
      (Expr.lamDomainsOnly n e).AvoidsConsts names
  | 0, _, _ => by simpa [Expr.lamDomainsOnly] using Lean.Expr.AvoidsConsts.sort _
  | _ + 1, _, .succ hd hb => by
    simp only [Expr.lamDomainsOnly]
    exact .lam _ _ _ _ hd (Expr.LamPrefixAvoids.lamDomainsOnly hb)

theorem Expr.ProjsOK.lamDomainsOnly {ok : Name → Prop} :
    ∀ (n : Nat) {e : Expr}, e.ProjsOK ok → (Expr.lamDomainsOnly n e).ProjsOK ok
  | 0, _, _ => by simp [Expr.lamDomainsOnly]
  | n + 1, e, h => by
    cases e with
    | lam _ _ b _ =>
      simp only [Expr.lamDomainsOnly]
      exact ⟨h.1, Expr.ProjsOK.lamDomainsOnly n h.2⟩
    | _ => simp [Expr.lamDomainsOnly]

theorem Expr.ProjsOK.lambdaTelescope {ok : Name → Prop} {e suffix : Expr} {n : Nat}
    (Htel : Expr.LambdaTelescope e n suffix) (H : e.ProjsOK ok) : suffix.ProjsOK ok := by
  induction Htel with
  | nil => exact H
  | cons _ ih => exact ih H.2

/-- **A restored lambda telescope translates**, from hypotheses on the stored
lowered input. -/
theorem NestedRestorationOpening.translatesLambdaTrail
    {r : Restoration} {envT envL : VEnv} {ρ : Name → Option VExpr} {σ : Name → Name}
    (S : InductiveSignature.RenamingRestorationSubstitutionOnCtx envT envL r ρ σ)
    {decl : VInductDecl} {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us : List Name}
    (D : RestorationTableData decl auxiliaries result env auxRec Us)
    (hr : r = InductiveSignature.compilationRestoration decl auxiliaries)
    {input output suffix : Expr} {s : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (hLwf : envL.WF) (hTwf : envT.WF) (hβ : envT.BetaSubjectReduction Us.length)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hlits : ∀ l, envL.ContainsLits l → envT.ContainsLits l)
    (Hlitnames : ∀ l : Literal, l.toConstructor.AvoidsConsts r.restorableNames)
    (Hheads : ∀ MT : TypeChecker.MLCtx, MT.lctx = Hopen.lctx → MT.WF envT Us →
      RestoreHeadsTranslate r result env envT Us (Us.map Level.param) Hopen.params MT.vlctx)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (Hshape : Expr.HitShapeTele (r.heads.map (·.auxiliary)) result.nparams
      (Us.map Level.param) input)
    (Htrail : input.HitTrailAvoids (r.heads.map (·.auxiliary)) r.restorableNames
      result.nparams)
    (Hdom : input.LamPrefixAvoids r.restorableNames result.nparams)
    (Hprojs : input.ProjsOK (· ∉ r.restorableNames))
    (Hs : TrExprS envL Us [] input s) :
    ∃ t, TrExprS envT Us [] output t ∧ VExpr.WF envT Us.length [] t ∧
      r.expr s = some t := by
  subst hr
  have hclosed : Closed input := by simpa [VLCtx.bvars] using Hs.closed
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have HbodyTrail : Hopen.body.HitTrailWith
      ((InductiveSignature.compilationRestoration decl auxiliaries).heads.map (·.auxiliary))
      result.nparams
      (·.AvoidsConsts (InductiveSignature.compilationRestoration decl auxiliaries).restorableNames) := by
    rw [hbody]
    exact ((Htrail.lambdaTelescope Htel).instantiateRevList_fvars _ 0).toHitTrailWith
  have HbodyProjs : Hopen.body.ProjsOK
      (· ∉ (InductiveSignature.compilationRestoration decl auxiliaries).restorableNames) := by
    rw [hbody]
    exact (Expr.ProjsOK.lambdaTelescope Htel Hprojs).instantiateRevList
      (fun a ha => by
        rcases List.mem_map.mp ha with ⟨fv, _, rfl⟩
        exact Expr.ProjsOK.fvar) 0
  exact Hopen.translatesLambda S hLwf hTwf hβ (D.agreement envT Us) hc Hlits Hlitnames
    Hheads Htel Hdom.lamDomainsOnly (Expr.ProjsOK.lamDomainsOnly _ Hprojs)
    (Hopen.hitShape_of_lowered_lam Htel Hshape) HbodyTrail HbodyProjs
    (Hopen.restoredBody_closed_lam D Htel (by simpa using Htel.closed_result' hclosed)) Hs

end VerifyInductive
end Lean4Lean
