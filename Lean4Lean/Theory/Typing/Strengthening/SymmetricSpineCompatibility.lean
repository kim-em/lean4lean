import Lean4Lean.Theory.Typing.Strengthening.SymmetricPrefixCompatibility

/-! # Symmetric phase compatibility along dependent application spines

Original typings of both complete spines recover each argument's typing.
Soundness of the shorter comparison aligns its function and argument types;
no strengthening or phase transitivity is used.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Symmetric terminal eta joins extend over a dependent application spine.
Both original spines are typed, possibly at different displayed types. -/
theorem EtaJoin.mkApps_spine (hΓ : OnCtx Γ (env.IsType univs))
    (HF : EtaJoin Γ f f') (HA : List.Forall₂ (EtaJoin Γ) args args')
    (ht : env.HasType univs Γ (mkApps f args) T)
    (ht' : env.HasType univs Γ (mkApps f' args') T') :
    EtaJoin Γ (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact HF
  | cons H HA ih =>
    obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app f _) ht
    obtain ⟨_, happ'⟩ := mkApps_head_type hΓ (fn := .app f' _) ht'
    obtain ⟨_, _, hf, ha⟩ := happ.app_inv henv hΓ
    obtain ⟨_, _, hf', ha'⟩ := happ'.app_inv henv hΓ
    exact ih (.app hΓ hf (HF.defeq hΓ hf hf').hasType.2
      ha (H.defeq hΓ ha ha').hasType.2 HF H) ht ht'

/-- Computational symmetric phases extend over a whole dependent spine.
This only uses compatible application and original endpoint typings. -/
theorem PrefixEtaJoin.mkApps_spine (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : PrefixEtaJoin D Γ f f') (HA : List.Forall₂ (PrefixEtaJoin D Γ) args args')
    (ht : env.HasType univs Γ (mkApps f args) T)
    (ht' : env.HasType univs Γ (mkApps f' args') T') :
    PrefixEtaJoin D Γ (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact HF
  | cons H HA ih =>
    obtain ⟨_, happ⟩ := mkApps_head_type hΓ (fn := .app f _) ht
    obtain ⟨_, happ'⟩ := mkApps_head_type hΓ (fn := .app f' _) ht'
    obtain ⟨_, _, hf, ha⟩ := happ.app_inv henv hΓ
    obtain ⟨_, _, hf', ha'⟩ := happ'.app_inv henv hΓ
    exact ih (.app hs hΓ hf (HF.defeq hs hΓ hf hf').hasType.2
      ha (H.defeq hs hΓ ha ha').hasType.2 HF H) ht ht'

end Lean4Lean.VEnv.Strengthening.PureObservation
