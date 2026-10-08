import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Typing.Pattern

/-! Typing soundness of the actual primitive quotient iota pattern. -/

namespace Lean4Lean.VEnv
open VExpr
set_option maxHeartbeats 1000000
theorem quotient_walk (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
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

end Lean4Lean.VEnv
