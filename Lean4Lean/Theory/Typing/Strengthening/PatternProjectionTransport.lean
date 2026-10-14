import Lean4Lean.Theory.Typing.Strengthening.PatternIotaTransport

/-! # Projection computation through normal comparison without eta reduction

Normal comparison of a projection's major beta-exposes the same constructor
spine, or forces a proof result. Function alternatives contradict its family
typing. This is the root case needed for compatible pattern simulation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- Saturated constructor projection transports through a normal comparison of
its major using beta and projection computation alone. -/
theorem normal_projection_compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (lproj : Γ ⊢ .proj family index major : resultType)
    (lMajor : NormalEqN true k Γ major (VExpr.mkApps (.const info.ctorName levels) args))
    (hl : env.projections family info)
    (hproj : Γ ⊢ .proj family index (VExpr.mkApps (.const info.ctorName levels) args) : fieldType)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + index]? = some field) (hfield : Γ ⊢ field : fieldType) :
    ∃ X, PatternCompute D (.proj family index major) X ∧ NormalEq Γ X field := by
  obtain ⟨info', levels', params, indexArgs, sourceMajor, fieldType', fieldLevel,
    hinfo, hlevels, huvars, hparams, hindices, hfieldTy, hfieldTyping,
    hmajor, hclosed, hguard⟩ := lproj.proj_inv henv hΓ
  have hmT := hmajor.hasType.2
  have hnormal := NormalEq.projDF lproj ⟨_, lMajor⟩
  have hright := ((hnormal.defeq hΓ).of_l henv hΓ lproj).hasType.2
  have hfield' : Γ ⊢ field : resultType :=
    HasType.defeqU_r henv hΓ (hproj.uniqU henv hΓ hright) hfield
  rcases normal_spine_expose_beta hΓ .const k lMajor (bs := []) .nil hmT with
    hprop | ⟨h', args', he, hred, hargs⟩ | ⟨A, g, m, targs₁, B, _, _, _, hrel, hty⟩ |
      ⟨z, A, B, m, targs₁, _, _, _, _, hrel, hty⟩
  · have hprop' := lproj.proj_result_prop_of_major_proof henv hΓ hprop hmT
    have hout := ((PatternCompute.base (.projIota hl hlen hget)).simAt hs hΓ _ hright).hasType.2
    exact ⟨_, .refl, .proofIrrel hprop' lproj hout⟩
  · obtain ⟨ls', rfl, -⟩ : ∃ ls', h' = .const info.ctorName ls' ∧
        List.Forall₂ (· ≈ ·) ls' levels := by
      cases he with | const h => exact ⟨_, rfl, h⟩
    simp only [List.append_nil] at hargs
    have hred' : PatternCompute D (.proj family index major)
        (.proj family index (VExpr.mkApps (.const info.ctorName ls') args')) := PatternCompute.proj (.of_beta hred)
    obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp hget
    have hi' : info.nparams + index < args'.length := by rw [hargs.length_eq]; exact hi
    have hn := Lean4Lean.List.Forall₂.getElem_of hargs (info.nparams + index) hi' hi
    rw [heq] at hn
    have hget' : args'[info.nparams + index]? = some args'[info.nparams + index] := by simp [hi']
    have hlen' : args'.length = info.nparams + info.numFields := hargs.length_eq.trans hlen
    exact ⟨_, hred'.trans (.base (.projIota hl hlen' hget')), hn⟩
  · exfalso
    simp only [List.append_nil] at hrel
    obtain ⟨_, hcc⟩ := mkApps_head_type hΓ hty
    have hsp := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
    have hpi := hty.defeqU_l henv hΓ (hsp.defeq hΓ)
    have hfam := hmT.defeqU_l henv hΓ (lMajor.defeq hΓ)
    have ⟨_, hsort⟩ := hmajor.hasType.2.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hinfo) hsort
      (hfam.uniqU henv hΓ hpi)
  · exfalso
    simp only [List.append_nil] at hrel
    obtain ⟨_, hcc⟩ := mkApps_head_type hΓ hty
    have hsp := NormalEq.mkApps_spine hΓ (NormalEq.refl hcc) hrel hty
    have hpi := hty.defeqU_l henv hΓ (hsp.defeq hΓ)
    have hfam := hmT.defeqU_l henv hΓ (lMajor.defeq hΓ)
    have ⟨_, hsort⟩ := hmajor.hasType.2.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hinfo) hsort
      (hfam.uniqU henv hΓ hpi)

end Lean4Lean.VEnv.Strengthening.PureObservation
