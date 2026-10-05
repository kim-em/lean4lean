import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldChoice

/-! Field domains of a generated minor premise, in the abstract contexts used
by the independent generator.

The consumed field telescope of a minor, closed over the parameters, mentions
no free variable at all, so abstracting any further binders merely lifts it.
Weakening it beneath the motives and earlier minors therefore yields the
generator's `insertBinders` form of the selected source field domains. -/

namespace Lean4Lean

/-- Translation is syntactically unique: every constructor of `TrExprS` is
determined by the source syntax and the context, including projections
(`TrProj.target_eq`).  This strengthens `TrExprS.unique'`, whose `IsUnique`
hypothesis excludes projections. -/
theorem TrExprS.uniqueCtx {env : VEnv} {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (hΔ : TrExprS.IsUniqueCtx Δ₁ Δ₂)
    (H1 : TrExprS env Us Δ₁ e e₁) (H2 : TrExprS env Us Δ₂ e e₂) : e₁ = e₂ := by
  induction H1 generalizing Δ₂ e₂ with cases H2
  | bvar => exact hΔ.find?_uniq ‹_› ‹_›
  | fvar => exact hΔ.find?_uniq ‹_› ‹_›
  | sort h1
  | const _ h1 => cases h1.symm.trans ‹_›; rfl
  | app _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 hΔ ‹_›; rfl
  | lam _ _ _ ih1 ih2
  | forallE _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlam) ‹_›; rfl
  | letE _ _ _ _ _ ih1 ih2 => cases ih1 hΔ ‹_›; cases ih2 (hΔ.cons .vlet) ‹_›; rfl
  | lit _ _ ih => exact ih hΔ ‹_›
  | mdata _ ih => exact ih hΔ ‹_›
  | proj _ hp ih =>
    rename_i h2 hp2
    cases ih hΔ h2
    rw [hp.target_eq, hp2.target_eq]

theorem TrExprS.uniqueS {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Lean.Expr}
    {e₁ e₂ : VExpr} (H1 : TrExprS env Us Δ e e₁) (H2 : TrExprS env Us Δ e e₂) : e₁ = e₂ :=
  H1.uniqueCtx .base H2

theorem FVarsIn.abstract1_eq_liftLooseBVars {e : Lean.Expr} {v : Lean.FVarId} {k : Nat}
    (h : FVarsIn (· ≠ v) e) : e.abstract1 v k = e.liftLooseBVars' k 1 := by
  induction e generalizing k with
  | fvar v' =>
    simp only [FVarsIn] at h
    simp [Lean.Expr.abstract1, Lean.Expr.liftLooseBVars', Ne.symm h]
  | _ => simp_all [FVarsIn, Lean.Expr.abstract1, Lean.Expr.liftLooseBVars']

theorem _root_.Lean.Expr.liftLooseBVars'_liftLooseBVars' (e : Lean.Expr) (k d₁ d₂ : Nat) :
    (e.liftLooseBVars' k d₁).liftLooseBVars' k d₂ = e.liftLooseBVars' k (d₁ + d₂) := by
  induction e generalizing k <;> simp_all [Lean.Expr.liftLooseBVars']
  split <;> (try split) <;> omega

/-- Abstracting variables that do not occur only shifts the loose bound
variables at and above the abstraction depth. -/
theorem FVarsIn.abstractList_eq_liftLooseBVars {e : Lean.Expr} {xs : List Lean.FVarId}
    {k : Nat} (h : FVarsIn (fun fv => fv ∉ xs) e) :
    e.abstractList xs k = e.liftLooseBVars' k xs.length := by
  induction xs generalizing e with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [Lean.Expr.abstractList, List.length_cons]
    rw [(h.mono fun _ hfv => hfv.1).abstract1_eq_liftLooseBVars,
      ih ((h.mono fun _ hfv => hfv.2).liftLooseBVars),
      Lean.Expr.liftLooseBVars'_liftLooseBVars', Nat.add_comm]

namespace VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The selected source field domains of one minor, lifted beneath `inserted`
abstract binders placed between the parameters and the fields.  The source
side abstracts any `extra` free variables of the same count, because the
parameter-closed field telescope contains no free variable. -/
theorem CompletedRecursorConstruction.minorFieldsTemplate
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (inserted : List VExpr) (extra : List FVarId) (hextra : extra.length = inserted.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let fields := (H.sourceFields owner howner localIndex hlocal).map
      (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible))
    TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted) [])
      ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList (H.params.fvars ++ extra))
      (VExpr.wrapForalls (InductiveSignature.insertBinders fields inserted.length) (.sort .zero)) := by
  intro S fields
  have Hsrc := (H.sourceFields_headerReplay owner howner localIndex hlocal).2.2
  have Hweak := Hsrc.weakBV H.recursorWF.checking.tr.wf.ordered
    (abstractForallContext.bvLift inserted
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []))
  have hfvars : VLCtx.fvars ([] : VLCtx) = [] := rfl
  have hnofvars : ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
      H.params.fvars).FVarsIn (fun fv => fv ∉ extra) := by
    have h := Hsrc.fvarsIn
    simp only [abstractForallContext_fvars, hfvars] at h
    exact h.mono fun fv hfv => by simp at hfv
  have hsource : (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
      (H.params.fvars ++ extra) =
      ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList
        H.params.fvars).liftLooseBVars' 0 inserted.length := by
    rw [Expr.abstractList_append, hnofvars.abstractList_eq_liftLooseBVars, hextra]
  rw [hsource, insertBinders_eq_prefix]
  rw [VExpr.liftN_wrapForalls] at Hweak
  simpa [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc,
    VExpr.liftN] using Hweak

end VerifyInductive
end Lean4Lean
