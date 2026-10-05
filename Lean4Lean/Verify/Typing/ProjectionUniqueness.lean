import Lean4Lean.Verify.Typing.ProjectionDesugaring
import Lean4Lean.Theory.Typing.ProjectionProgramCongruence
import Lean4Lean.Theory.Typing.CaseLevelEquivTyping
import Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-! Typed uniqueness of declaration-derived projection abbreviations. -/

namespace Lean4Lean
open VExpr VEnv InductiveSignature InductiveSignature.CaseSchema

private theorem projection_mkApps_defeq {env : VEnv} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (hargs : List.Forall₂ (env.IsDefEqU U Γ) args args')
    (hfn : env.IsDefEqU U Γ fn fn')
    (H : VExpr.WF env U Γ (mkApps fn args)) :
    env.IsDefEqU U Γ (mkApps fn args) (mkApps fn' args') := by
  induction hargs generalizing fn fn' with
  | nil => exact hfn
  | cons ha has ih =>
    have happ : VExpr.WF env U Γ (.app fn _) := H.of_mkApps henv.ordered hΓ
    obtain ⟨A, B, hf, hx⟩ := happ.app_inv henv.ordered hΓ
    exact ih ⟨_, (hfn.of_l henv hΓ hf).appDF (ha.of_l henv hΓ hx)⟩ H

/-- Separate occurrence witnesses for the same projection agree by typed
equality, even when their hidden arguments or unused field universes differ. -/
theorem ProjectionDesugaring.unique (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : ProjectionDesugaring env U Γ name index major target)
    (H' : ProjectionDesugaring env U Γ name index major target') :
    env.IsDefEqU U Γ target target' := by
  cases H with
  | @intro block programs fieldSorts levels params indices schema owner program
      hr ho hf hg hs hlu hfu hw hp hn hi hm ht =>
    cases H' with
    | @intro block' programs' fieldSorts' levels' params' indices' schema' owner' program'
        hr' ho' hf' hg' hs' hlu' hfu' hw' hp' hn' hi' hm' ht' =>
      obtain ⟨rfl, rfl, howner⟩ := henv.eliminator_slot_unique hr hr' ho ho'
      have hoeq : owner = owner' := Fin.ext howner
      subst owner'
      have hprograms : programs = programs' := Option.some.inj (hg.symm.trans hg')
      subst programs'
      have hprogram : program = program' := Option.some.inj (hs.symm.trans hs')
      subst program'
      have hrigid := henv.case_original_family_rigid hr (List.mem_of_getElem? ho)
      obtain ⟨_, hfamily⟩ := hm.isType henv.ordered hΓ
      have htypes := IsDefEq.uniqU henv hΓ hm hm'
      obtain ⟨hlevels, hargs⟩ := IsDefEqU.rigidApp_inv henv hΓ
        (nativeHeadRigid_iff.mp hrigid) htypes hfamily
      have hprogram := genericProjectionPrefix_congr hr hg hfu hfu' hlu hlu'
        (fun u hu => hw u (List.mem_append_right _ hu))
        (fun u hu => hw' u (List.mem_append_right _ hu)) hlevels
        program (List.mem_of_getElem? hs)
      have hfn := CaseLevelEquiv.defeq henv hΓ hprogram
        (ht.of_mkApps henv.ordered hΓ) (ht'.of_mkApps henv.ordered hΓ)
      exact projection_mkApps_defeq henv hΓ
        (case_forall₂_append hargs (.cons (show env.IsDefEqU U Γ major major from ⟨_, hm⟩) .nil))
        hfn ht

/-- Projection translation also respects equality of the translated major,
without retaining the same hidden universe or argument witnesses. -/
theorem ProjectionDesugaring.defeq (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : ProjectionDesugaring env U Γ name index major target)
    (H' : ProjectionDesugaring env U Γ name index major' target')
    (hmajor : env.IsDefEqU U Γ major major') :
    env.IsDefEqU U Γ target target' := by
  obtain ⟨middle, hmiddle, heq⟩ := H.congr_major henv hΓ hmajor
  exact heq.trans henv hΓ (hmiddle.unique henv hΓ H')

end Lean4Lean
