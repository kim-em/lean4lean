import Lean4Lean.Theory.Typing.CaseLevelEquiv
import Lean4Lean.Theory.Typing.CaseMotiveCoherence

/-! Typed soundness of case-program congruence. The target universes are
recovered from the supplied motives rather than compared as unused metadata. -/

set_option maxHeartbeats 1000000

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.CaseSchema
variable {env : VEnv} {U : Nat}

private theorem arguments_wf (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    ∀ arg ∈ args, VExpr.WF env U Γ arg := by
  induction args generalizing fn with
  | nil => simp
  | cons a args ih =>
    have hf := VExpr.WF.of_mkApps (f := fn.app a) (args := args) henv.ordered hΓ H
    obtain ⟨_, _, _, ha⟩ := hf.app_inv henv.ordered hΓ
    intro arg hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ha⟩
    · exact ih H arg hm

private theorem congr_apps (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ fn fn')
    (ha : List.Forall₂ (env.IsDefEqU U Γ) args args')
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    env.IsDefEqU U Γ (mkApps fn args) (mkApps fn' args') := by
  induction ha generalizing fn fn' with
  | nil => exact hf
  | @cons a a' args args' ha hs ih =>
    obtain ⟨_, _, hfn, harg⟩ :=
      (VExpr.WF.of_mkApps (f := fn.app a) (args := args) henv.ordered hΓ H).app_inv henv.ordered hΓ
    exact ih ⟨_, .appDF (hf.of_l henv hΓ hfn) (ha.of_l henv hΓ harg)⟩ H

private theorem apply_arguments
    (h : List.Forall₂ (fun e e' => ∀ Γ, OnCtx Γ (env.IsType U) →
      VExpr.WF env U Γ e → VExpr.WF env U Γ e' → env.IsDefEqU U Γ e e') args args')
    (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : ∀ e ∈ args, VExpr.WF env U Γ e)
    (h₂ : ∀ e ∈ args', VExpr.WF env U Γ e) :
    List.Forall₂ (env.IsDefEqU U Γ) args args' := by
  induction h with
  | nil => exact .nil
  | cons h hs ih =>
    exact .cons (h Γ hΓ (h₁ _ (by simp)) (h₂ _ (by simp)))
      (ih (fun e he => h₁ e (by simp [he])) (fun e he => h₂ e (by simp [he])))

/-- Well-typed generated programs related by case congruence are
definitionally equal, including at target universes inferred from motives. -/
theorem _root_.Lean4Lean.VExpr.CaseLevelEquiv.defeq (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (L : CaseLevelEquiv env U e e')
    (H : VExpr.WF env U Γ e) (H' : VExpr.WF env U Γ e') :
    env.IsDefEqU U Γ e e' := by
  apply CaseLevelEquiv.rec
    (motive_1 := fun e e' _ => ∀ Γ, OnCtx Γ (env.IsType U) →
      VExpr.WF env U Γ e → VExpr.WF env U Γ e' → env.IsDefEqU U Γ e e')
    (motive_2 := fun es es' _ => List.Forall₂ (fun e e' => ∀ Γ,
      OnCtx Γ (env.IsType U) → VExpr.WF env U Γ e → VExpr.WF env U Γ e' →
      env.IsDefEqU U Γ e e') es es')
    (fun hl Γ hΓ h h' => hl.defeq henv hΓ h)
    (fun _ _ ihf iha Γ hΓ h h' => by
      obtain ⟨_, _, hf, ha⟩ := h.app_inv henv.ordered hΓ
      obtain ⟨_, _, hf', ha'⟩ := h'.app_inv henv.ordered hΓ
      exact ⟨_, .appDF ((ihf Γ hΓ ⟨_, hf⟩ ⟨_, hf'⟩).of_l henv hΓ hf)
        ((iha Γ hΓ ⟨_, ha⟩ ⟨_, ha'⟩).of_l henv hΓ ha)⟩)
    (fun _ _ ihd ihb Γ hΓ h h' => by
      obtain ⟨_, h⟩ := h
      obtain ⟨_, h'⟩ := h'
      obtain ⟨⟨_, hd⟩, hb⟩ := HasType.lam_inv henv.ordered hΓ h
      obtain ⟨⟨_, hd'⟩, hb'⟩ := HasType.lam_inv henv.ordered hΓ h'
      have he := (ihd Γ hΓ ⟨_, hd⟩ ⟨_, hd'⟩).of_l henv hΓ hd
      have hctx : OnCtx (_ :: Γ) (env.IsType U) := ⟨hΓ, _, hd⟩
      have hb'' := hb'.defeqDFC henv.ordered (.succ .zero he.symm)
      obtain ⟨_, hbody⟩ := hb
      exact ⟨_, .lamDF he ((ihb _ hctx ⟨_, hbody⟩ hb'').of_l henv hctx hbody)⟩)
    (fun _ _ ihd ihb Γ hΓ h h' => by
      obtain ⟨_, h⟩ := h
      obtain ⟨_, h'⟩ := h'
      obtain ⟨⟨_, hd⟩, _, hb⟩ := HasType.forallE_inv henv.ordered h
      obtain ⟨⟨_, hd'⟩, _, hb'⟩ := HasType.forallE_inv henv.ordered h'
      have he := (ihd Γ hΓ ⟨_, hd⟩ ⟨_, hd'⟩).of_l henv hΓ hd
      have hctx : OnCtx (_ :: Γ) (env.IsType U) := ⟨hΓ, _, hd⟩
      have hb'' := hb'.defeqDFC henv.ordered (.succ .zero he.symm)
      exact ⟨_, .forallEDF he ((ihb _ hctx ⟨_, hb⟩ ⟨_, hb''⟩).of_l henv hctx hb)⟩)
    (fun _ ih Γ hΓ h h' => by
      obtain ⟨_, h⟩ := h
      obtain ⟨_, h'⟩ := h'
      obtain ⟨info, ls, P, idx, sm, F, fl, hinfo, hls, huv, hP, hidx, hfield,
        hFty, hsm, hclosed, hguard⟩ := HasType.proj_inv henv.ordered hΓ h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsm', _, _⟩ :=
        HasType.proj_inv henv.ordered hΓ h'
      have hmaj := hsm.hasType.2
      exact ⟨_, .projDF hinfo hls huv hP hidx hfield hFty hsm
        (hsm.transU_l henv hΓ (ih _ hΓ ⟨_, hmaj⟩ ⟨_, hsm'.hasType.2⟩)) hclosed hguard⟩)
    (fun {block levels levels' args args' target target' schema owner} hl hu hlen hs ih Γ hΓ h h' => by
      have hargs := apply_arguments ih hΓ (arguments_wf henv hΓ h)
        (arguments_wf henv hΓ h')
      have hlen' : args'.length = caseMajorArity schema owner + 1 := by
        rw [← List.Forall₂.length_eq hs]; exact hlen
      have hp : schema.signature.params.length < args.length := by
        rw [hlen]; simp only [caseMajorArity]; omega
      have hp' : schema.signature.params.length < args'.length := by
        rw [hlen']; simp only [caseMajorArity]; omega
      have htarget := caseMotive_target_coherence henv hΓ hl hlen hlen' hp hp' h h'
        (case_forall₂_get hargs hp hp')
      obtain ⟨_, hh'⟩ := VExpr.WF.of_mkApps henv.ordered hΓ h'
      obtain ⟨_, _, _, _, _, _, _, hpck, _, _, _, hperm, _, _⟩ :=
        HasType.elim_inv henv.ordered hΓ hh'
      have hw : ∀ l ∈ target' :: levels', l.WF U := by
        rw [hpck]; exact hperm.packedWF
      have hhead := (LEquiv.elim (.cons htarget hu) hw).defeq henv hΓ
        (VExpr.WF.of_mkApps henv.ordered hΓ h)
      exact congr_apps henv hΓ hhead hargs h)
    (.nil)
    (fun _ _ ih ihs => .cons ih ihs) L Γ hΓ H H'

end Lean4Lean.VEnv
