import Lean4Lean.Theory.Typing.QuotPatterns

/-! Typing soundness of the actual primitive quotient iota pattern. -/

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
private theorem quotient_walk (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, major])) :
    ∃ result, InstForallsC env U Γ (quotLiftConst.type.instL [u,v])
      [alpha, relation, beta, fn, compat, major] result := by
  obtain ⟨result, hw, _⟩ := HasType.mkApps_telescope henv hΓ
    (HasType.const hr.lift (ls := [u,v]) (by simpa using And.intro hu hv) rfl) H
    (by rfl)
  exact ⟨result, hw⟩

private theorem quotient_sound_spine (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hr : QuotRegistered env) (hu : u.WF U) (hv : v.WF U) (hu' : u'.WF U)
    (H : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v])
      [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]]))
    (hae : env.IsDefEqU U Γ alpha alpha') (hre : env.IsDefEqU U Γ relation relation') :
    env.IsDefEqU U Γ
      (mkApps (.const ``Quot.lift [u,v])
        [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]])
      (.app fn value) := by
  obtain ⟨result, hw⟩ := quotient_walk henv hΓ hr hu hv H
  cases hw with | cons ha hw =>
    cases hw with | cons hrel hw =>
      cases hw with | cons hbeta hw =>
        cases hw with | cons hf hw =>
          cases hw with | cons hcompat hw =>
            cases hw with | cons hmajor hw =>
              simp [instL, inst, VLevel.inst, inst_lift, ← lift_instN_lo] at ha hrel hbeta hf hcompat hmajor
              obtain ⟨_, hcw, _⟩ := HasType.mkApps_telescope henv hΓ
                (HasType.const hr.constructor (ls := [u']) (by simpa using hu') rfl)
                (show VExpr.WF env U Γ _ from ⟨_, hmajor⟩) (by rfl)
              cases hcw with | cons hca hcw =>
                cases hcw with | cons hcr hcw =>
                  cases hcw with | cons hvalue _ =>
                    simp [instL, inst, VLevel.inst, inst_lift] at hca hcr hvalue
                    have hvalue' := hvalue.defeqU_r henv hΓ hae.symm
                    have hue : u' ≈ u :=
                      (hca.uniqU henv hΓ (ha.defeqU_l henv hΓ hae)).sort_inv henv hΓ
                    have hmatch : NativeSpineMatch env U Γ
                        (mkApps (.const ``Quot.mk [u']) [alpha', relation', value])
                        (mkApps (.const ``Quot.mk [u]) [alpha, relation, value]) :=
                      ⟨_, _, _, _, _, rfl, rfl, by simpa using hu', by simpa using hu,
                        .cons hue .nil, .cons hae.symm (.cons hre.symm (.cons ⟨_, hvalue⟩ .nil))⟩
                    have hm := hmatch.defeq henv hΓ hmajor
                    obtain ⟨A, B, hp, hmj⟩ := H.app_inv henv.ordered hΓ
                    have hreplace : env.IsDefEqU U Γ
                        (mkApps (.const ``Quot.lift [u,v])
                          [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u']) [alpha', relation', value]])
                        (mkApps (.const ``Quot.lift [u,v])
                          [alpha, relation, beta, fn, compat, mkApps (.const ``Quot.mk [u]) [alpha, relation, value]]) :=
                      ⟨_, hp.appDF (hm.of_l henv hΓ hmj)⟩
                    let ds := ((quotDefEq.type.takeForalls 6).getD ([], .bvar 0)).1
                    have he := IsDefEq.extra_instOuter henv hΓ hr.equation
                      (ls := [u,v]) (by simpa using And.intro hu hv) rfl
                      (doms := ds) (lhsBody := quotDefEq.lhs.stripLams)
                      (rhsBody := quotDefEq.rhs.stripLams) (typeBody := .bvar 3)
                      rfl rfl rfl (args := [alpha, relation, beta, fn, compat, value]) rfl ?_
                    · refine hreplace.trans henv hΓ ⟨beta, ?_⟩
                      simpa [quotDefEq, stripLams, instL, instOuter, inst,
                        VLevel.inst, ← lift_instN_lo, inst_lift, mkApps] using he
                    · intro j hj hd
                      have hj' : j < 6 := hj
                      match j with
                      | 0 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst] using ha
                      | 1 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hrel
                      | 2 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hbeta
                      | 3 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hf
                      | 4 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hcompat
                      | 5 => simpa [ds, quotDefEq, takeForalls, instL, instOuter, inst, VLevel.inst, ← lift_instN_lo, inst_lift] using hvalue'
                      | _ + 6 => omega

theorem QuotPattern.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotPattern env p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type)
    (hcheck : rhs.2.OK (env.IsDefEqU U Γ) levels values) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) := by
  cases H with
  | intro hr =>
    cases hm with
    | app hf hc =>
      cases hf with | var hf =>
        cases hf with | var hf =>
          cases hf with | var hf =>
            cases hf with | var hf =>
              cases hf with | var hf =>
                cases hf
                cases hc with | var hc =>
                  cases hc with | var hc =>
                    cases hc with | var hc =>
                      cases hc
                      rename_i ctorLevels compat fn beta relation alpha value relation' alpha'
                      change env.HasType U Γ (mkApps (.const ``Quot.lift levels)
                        [alpha, relation, beta, fn, compat,
                          mkApps (.const ``Quot.mk ctorLevels) [alpha', relation', value]]) type at ht
                      have hh := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, ht⟩
                      obtain ⟨ci, hci, hw, hl⟩ := hh.const_inv henv.ordered hΓ
                      cases Option.some.inj (hci.symm.trans hr.lift)
                      change levels.length = 2 at hl
                      obtain ⟨u, v, rfl⟩ : ∃ u v, levels = [u,v] := by
                        rcases levels with _ | ⟨u, _ | ⟨v, tail⟩⟩ <;> simp_all
                      obtain ⟨_, _, _, hc⟩ := (show VExpr.WF env U Γ _ from ⟨_, ht⟩).app_inv henv.ordered hΓ
                      have hch := VExpr.WF.of_mkApps henv.ordered hΓ
                        (show VExpr.WF env U Γ (mkApps (.const ``Quot.mk ctorLevels) _) from ⟨_, hc⟩)
                      obtain ⟨ci, hci, hwc, hlc⟩ := hch.const_inv henv.ordered hΓ
                      cases Option.some.inj (hci.symm.trans hr.constructor)
                      change ctorLevels.length = 1 at hlc
                      obtain ⟨u', rfl⟩ : ∃ u', ctorLevels = [u'] := by
                        rcases ctorLevels with _ | ⟨u', tail⟩ <;> simp_all
                      simp only [quotPatternCheck, Pattern.Check.OK, Pattern.RHS.apply] at hcheck
                      have hresult := quotient_sound_spine henv hΓ hr
                        (hw u (by simp)) (hw v (by simp)) (hwc u' (by simp))
                        ⟨_, ht⟩ hcheck.2.1 hcheck.2.2.1
                      exact hresult

theorem DefinitionQuotPattern.sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionQuotPattern env registry p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type)
    (hcheck : rhs.2.OK (env.IsDefEqU U Γ) levels values) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) :=
  H.elim (fun h => h.sound henv hΓ hregistry hm ht)
    (fun h => h.sound henv hΓ hm ht hcheck)

end Lean4Lean.VEnv
