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

theorem TypeChecker.MLCtx.restrictUpSet {env : VEnv} {Us : List Name} (henv : env.WF) (hs : env.Strengthening)
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
    obtain ⟨Δ, n, W, hfvars, hlams⟩ := restrictUpSet henv hs P c hwfc honlyc hupc
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
      obtain ⟨ty₀, htr₀⟩ := htr.weakFV'_inv henv hs W (.refl henv.ordered hvwf) hc hv
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

/-- Restriction to an up-set as a typechecker context: the kept declarations
keep their concrete types, and their abstract types are the strengthened
translations in the restricted tail. -/
theorem TypeChecker.MLCtx.restrictUpSetCtx {env : VEnv} {Us : List Name} (henv : env.WF) (hs : env.Strengthening)
    (P : FVarId → Prop) :
    ∀ (c : MLCtx), c.WF env Us → VerifyInductive.MLCtxOnlyLams c → IsFVarUpSet P c.vlctx →
    ∃ (c' : MLCtx) (n : Lift), c'.WF env Us ∧ VerifyInductive.MLCtxOnlyLams c' ∧
      VLCtx.FVLift' c'.vlctx c.vlctx 0 n 0 ∧
      (∀ fv, fv ∈ c'.vlctx.fvars ↔ fv ∈ c.vlctx.fvars ∧ P fv) ∧
      (∀ fv decl', c'.lctx.find? fv = some decl' →
        ∃ decl, c.lctx.find? fv = some decl ∧ decl.type = decl'.type)
  | .nil, _, _, _ => ⟨.nil, .refl, trivial, VerifyInductive.MLCtxOnlyLams.nil, .refl, by simp,
      fun _ _ h => ⟨_, h, rfl⟩⟩
  | .vlet id name ty v ty' v' c, _, honly, _ => by
    exfalso
    obtain ⟨_, _, _, _, _, _, h⟩ :=
      honly (.ldecl c.length id name ty v false default) (by simp [MLCtx.decls])
    cases h
  | .vlam fv name ty ty' bi c, hwf, honly, hup => by
    have hwfBig : VLCtx.WF env Us.length (MLCtx.vlam fv name ty ty' bi c).vlctx := hwf.tr.wf
    obtain ⟨hwfc, _, htr, _⟩ := hwf
    have honlyc : VerifyInductive.MLCtxOnlyLams c := honly.tail_vlam
    have hupc : IsFVarUpSet P c.vlctx := hup.1
    obtain ⟨c', n, hwf', honly', W, hfvars, hfind⟩ := restrictUpSetCtx henv hs P c hwfc honlyc hupc
    have hvwf : VLCtx.WF env Us.length c.vlctx := hwfc.tr.wf
    have hnotin : fv ∉ c.vlctx.fvars := (hwfBig.2.1 fv ty.fvarsList rfl).1
    have hnotin' : fv ∉ c'.vlctx.fvars := fun h => hnotin ((hfvars fv).1 h).1
    by_cases hP : P fv
    · have hdeps : ∀ fv' ∈ ty.fvarsList, P fv' := hup.2 hP
      have hdepsIn : ty.fvarsList ⊆ c'.vlctx.fvars := fun fv' h =>
        (hfvars fv').2 ⟨htr.fvarsList h, hdeps fv' h⟩
      have hv : FVarsIn (· ∈ c'.vlctx.fvars) ty :=
        fvarsIn_iff.mpr ⟨hdepsIn, (fvarsIn_iff.mp htr.fvarsIn).2⟩
      have hc : Closed ty 0 := by
        have h := htr.closed
        rwa [c.noBV] at h
      obtain ⟨ty₀, htr₀⟩ := htr.weakFV'_inv henv hs W (.refl henv.ordered hvwf) hc hv
      have hlift := htr₀.weakFV' henv W hvwf
      have hty' : ty' = ty₀.lift' n := by simpa using htr.uniqueS hlift
      have W' : VLCtx.FVLift' ((some (fv, ty.fvarsList), .vlam ty₀) :: c'.vlctx)
          (MLCtx.vlam fv name ty ty' bi c).vlctx 0 (.consN n 1) 0 := by
        have W'' := W.cons_fvar (fv, ty.fvarsList) (.vlam ty₀) hdepsIn
        simpa [VLocalDecl.lift', VLocalDecl.depth, hty'] using W''
      have hwfSmall := W'.wf henv hs hwfBig
      have hfind' : c'.lctx.find? fv = none :=
        hwf'.tr.find?_eq_none.2 fun h => hnotin ((hfvars fv).1 h).1
      refine ⟨.vlam fv name ty ty₀ bi c', .consN n 1, ⟨hwf', hfind', htr₀, hwfSmall.2.2⟩,
        honly'.vlam, W', ?_, ?_⟩
      · intro x
        simp only [MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons]
        constructor
        · rintro (rfl | hx)
          · exact ⟨Or.inl rfl, hP⟩
          · exact ⟨Or.inr ((hfvars x).1 hx).1, ((hfvars x).1 hx).2⟩
        · rintro ⟨rfl | hx, hPx⟩
          · exact Or.inl rfl
          · exact Or.inr ((hfvars x).2 ⟨hx, hPx⟩)
      · intro x decl' hx
        by_cases hxfv : x = fv
        · subst hxfv
          simp only [MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
            hwf'.tr.1.map_wf.find?_insert, BEq.rfl, ↓reduceIte, Option.some.injEq] at hx
          refine ⟨.cdecl c.lctx.decls.size x name ty bi .default, ?_, ?_⟩
          · simp only [MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
              hwfc.tr.1.map_wf.find?_insert, BEq.rfl, ↓reduceIte]
          · rw [← hx]
            rfl
        · have hne : (fv == x) = false := by simpa using (Ne.symm hxfv)
          simp only [MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
            hwf'.tr.1.map_wf.find?_insert, hne, Bool.false_eq_true, ↓reduceIte] at hx
          obtain ⟨decl, hdecl, hty⟩ := hfind x decl' hx
          refine ⟨decl, ?_, hty⟩
          simp only [MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
            hwfc.tr.1.map_wf.find?_insert, hne, Bool.false_eq_true, ↓reduceIte]
          exact hdecl
    · refine ⟨c', n.skipN 1, hwf', honly', ?_, ?_, ?_⟩
      · simpa [VLocalDecl.depth] using W.skip_fvar (fv, ty.fvarsList) (.vlam ty')
      · intro x
        simp only [MLCtx.vlctx, VLCtx.fvars_cons_some, List.mem_cons]
        constructor
        · intro hx
          exact ⟨Or.inr ((hfvars x).1 hx).1, ((hfvars x).1 hx).2⟩
        · rintro ⟨rfl | hx, hPx⟩
          · exact absurd hPx hP
          · exact (hfvars x).2 ⟨hx, hPx⟩
      · intro x decl' hx
        obtain ⟨decl, hdecl, hty⟩ := hfind x decl' hx
        have hxmem : x ∈ c'.vlctx.fvars := (hwf'.tr.find?_eq_some).1 ⟨decl', hx⟩
        have hxfv : x ≠ fv := fun h => hnotin' (h ▸ hxmem)
        have hne : (fv == x) = false := by simpa using (Ne.symm hxfv)
        refine ⟨decl, ?_, hty⟩
        simp only [MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
          hwfc.tr.1.map_wf.find?_insert, hne, Bool.false_eq_true, ↓reduceIte]
        exact hdecl

end Lean4Lean
