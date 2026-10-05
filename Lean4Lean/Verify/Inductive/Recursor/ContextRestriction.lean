import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMinorFields

/-! Restriction of a translated local context to an up-set of its free
variables.

Translation strengthening (`TrExprS.weakFV'_inv`) can drop free-variable
declarations that nothing kept depends on.  For a typechecker context whose
declarations are all lambdas, any up-set of free variables (every kept
declaration's dependencies are kept) determines such a restriction together
with the free-variable lift witnessing it.  The restricted context is
well-formed by `FVLift'.wf` and has no bound variables. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

theorem TypeChecker.MLCtx.restrictUpSet {env : VEnv} {Us : List Name} (henv : env.WF)
    (P : FVarId → Prop) :
    ∀ (c : MLCtx), c.WF env Us → VerifyInductive.MLCtxOnlyLams c → IsFVarUpSet P c.vlctx →
    ∃ (Δ : VLCtx) (n : Lift), VLCtx.FVLift' Δ c.vlctx 0 n 0 ∧
      (∀ fv, fv ∈ Δ.fvars ↔ fv ∈ c.vlctx.fvars ∧ P fv) ∧
      (∀ entry ∈ Δ, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty))
  | .nil, _, _, _ => ⟨[], .refl, .refl, by simp, by simp⟩
  | .vlet id name ty v ty' v' c, _, honly, _ => by
    exfalso
    obtain ⟨_, _, _, _, _, _, h⟩ :=
      honly (.ldecl c.length id name ty v false default) (by simp [MLCtx.decls])
    cases h
  | .vlam fv name ty ty' bi c, hwf, honly, hup => by
    obtain ⟨hwfc, _, htr, _⟩ := hwf
    have honlyc : VerifyInductive.MLCtxOnlyLams c := fun d hd => honly d (by simp [MLCtx.decls, hd])
    have hupc : IsFVarUpSet P c.vlctx := hup.1
    obtain ⟨Δ, n, W, hfvars, hlams⟩ := restrictUpSet henv P c hwfc honlyc hupc
    have hvwf : VLCtx.WF env Us.length c.vlctx := hwfc.tr.wf
    by_cases hP : P fv
    · have hdeps : ∀ fv' ∈ ty.fvarsList, P fv' := hup.2 hP
      have hdepsIn : ty.fvarsList ⊆ Δ.fvars := fun fv' h =>
        (hfvars fv').2 ⟨htr.fvarsList h, hdeps fv' h⟩
      have hv : FVarsIn (· ∈ Δ.fvars) ty :=
        fvarsIn_iff.mpr ⟨hdepsIn, (fvarsIn_iff.mp htr.fvarsIn).2⟩
      have hc : Closed ty 0 := by
        have h := htr.closed
        rwa [c.noBV] at h
      obtain ⟨ty₀, htr₀⟩ := htr.weakFV'_inv henv W (.refl henv.ordered hvwf) hc hv
      have hlift := htr₀.weakFV' henv W hvwf
      have hty' : ty' = ty₀.lift' n := by simpa using htr.uniqueS hlift
      refine ⟨(some (fv, ty.fvarsList), .vlam ty₀) :: Δ, .consN n 1, ?_, ?_, ?_⟩
      · have W' := W.cons_fvar (fv, ty.fvarsList) (.vlam ty₀) hdepsIn
        simpa [VLocalDecl.lift', VLocalDecl.depth, hty'] using W'
      · intro x
        simp only [MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact ⟨Or.inl rfl, hP⟩
          · exact ⟨Or.inr ((hfvars x).1 hx).1, ((hfvars x).1 hx).2⟩
        · rintro ⟨rfl | hx, hPx⟩
          · exact Or.inl rfl
          · exact Or.inr ((hfvars x).2 ⟨hx, hPx⟩)
      · intro entry hentry
        rcases List.mem_cons.mp hentry with rfl | h
        · exact ⟨_, _, _, rfl⟩
        · exact hlams entry h
    · refine ⟨Δ, n.skipN 1, ?_, ?_, hlams⟩
      · simpa [VLocalDecl.depth] using W.skip_fvar (fv, ty.fvarsList) (.vlam ty')
      · intro x
        simp only [MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons]
        constructor
        · intro hx
          exact ⟨Or.inr ((hfvars x).1 hx).1, ((hfvars x).1 hx).2⟩
        · rintro ⟨rfl | hx, hPx⟩
          · exact absurd hPx hP
          · exact (hfvars x).2 ⟨hx, hPx⟩

/-- A context of lambda declarations pairs with its own free-variable list. -/
theorem VLCtx.allLams_forall₂ : ∀ (Δ : VLCtx),
    (∀ entry ∈ Δ, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty)) →
    List.Forall₂ (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type)) Δ.fvars Δ
  | [], _ => .nil
  | entry :: Δ, h => by
    obtain ⟨fv, deps, ty, rfl⟩ := h entry (List.mem_cons_self ..)
    exact .cons ⟨deps, ty, rfl⟩ (allLams_forall₂ Δ fun e he => h e (List.mem_cons_of_mem _ he))

/-- Close every declaration of a lambda-only context into abstract binders. -/
theorem TrExprS.closeAllLams {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (hlams : ∀ entry ∈ Δ, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty))
    (hnodup : Δ.fvars.Nodup) (Htr : TrExprS env Us Δ e e') :
    TrExprS env Us (VerifyInductive.abstractForallContext Δ.toCtx.reverse [])
      (e.abstractList Δ.fvars.reverse) e' := by
  have h := VerifyInductive.TrExprS.abstractFVarLambdaSuffix (domains := [])
    (VLCtx.allLams_forall₂ Δ hlams) hnodup
    (by simpa [VerifyInductive.abstractForallContext] using Htr)
  simpa using h

end Lean4Lean
