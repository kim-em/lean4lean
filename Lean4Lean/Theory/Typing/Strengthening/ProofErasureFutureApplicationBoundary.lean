import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrierFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyInstantiation

/-! # Future common comparison is not closed under shared application

The functions `fun f => f x` and `fun f => f y` retain future comparisons
when x and y have a positive unit type. Their bound function remains neutral
through ambient substitution and beta. Applying both to the identity exposes
x and y, which cannot compare as distinct bare variables.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

private theorem selector_beta (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (R : ProofShape.BetaRed
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) a)) p)
    (S : ProofShape.BetaRed
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) b)) q) :
    JointCompare Step Δ true p q := by
  obtain ⟨D, body, rfl, RD, RB⟩ := R.lam_inv
  obtain ⟨E, body', rfl, RE, RB'⟩ := S.lam_inv
  have hn : NormalSyntax (fun _ _ => False)
      (.forallE (.const family ls) (.const family ls)) :=
    ⟨fun _ H => H, ⟨fun _ H => H, trivial⟩, ⟨fun _ H => H, trivial⟩⟩
  obtain rfl := RD.fixed_of_normal hn
  obtain rfl := RE.fixed_of_normal hn
  obtain ⟨args, rfl, HA⟩ := RB.bvar_spine (args := [a])
  obtain ⟨args', rfl, HB⟩ := RB'.bvar_spine (args := [b])
  cases HA with
  | cons _ HA =>
    cases HA
    cases HB with
    | cons _ HB =>
      cases HB
      apply JointCheck.lamCommon
      apply JointCheck.appCarrier (A := .const family ls) (B := .const family ls)
      · exact .bvar
      · exact .leaf .refl
      · exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- A bound neutral function hides distinct unit arguments from beta even
after arbitrary ambient substitution. Consequently these selector lambdas
have full future common certificates at every primitive collection. The
certificate does not assert future substitution of the bound function. -/
theorem unit_selector_family (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) a))
      (.lam (.forallE (.const family ls) (.const family ls)) (.app (.bvar 0) b)) := by
  refine ⟨fun R S => selector_beta hi hp hx hf R S, ?_⟩
  intro Δ' τ p q _ R S
  simp only [ProofShape.subst, ProofShape.Subst.lift] at R S
  exact selector_beta hi hp hx hf R S

private theorem selector_typing
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hv : env.HasType univs Γ (.bvar i) (.const family ls)) :
    let F := VExpr.forallE (.const family ls) (.const family ls)
    let f := VExpr.lam F (.app (.bvar 0) (.bvar (i + 1)))
    env.HasType univs Γ f (.forallE F (.const family ls)) ∧
    proofErase Γ f = .lam (.forallE (.const family ls) (.const family ls))
      (.app (.bvar 0) (.bvar (i + 1))) := by
  dsimp only
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  have hF : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ u))) :=
    .forallE hS (hS.weak henv)
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hfun : env.HasType univs (F :: Γ) (.bvar 0) F := .bvar .zero
  have harg : env.HasType univs (F :: Γ) (.bvar (i + 1)) S := by
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hv.weak (B := F) henv
  have hbody : env.HasType univs (F :: Γ) (.app (.bvar 0) (.bvar (i + 1))) S := .app hfun harg
  have hsel := HasType.lam hF hbody
  have hid : env.HasType univs Γ (.lam S (.bvar 0)) F := .lam hS (.bvar .zero)
  have happ : env.HasType univs Γ (.app (.lam F (.app (.bvar 0) (.bvar (i + 1))))
      (.lam S (.bvar 0))) S := .app hsel hid
  have hnapp := not_proof_at_positive_type hΓ hS happ
  have hnbody := not_proof_at_positive_type hΓF (hS.weak henv) hbody
  have Econst : proofErase Γ S = .const family ls := if_neg (not_isProof_of_sort hΓ hS)
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have Econst' : proofErase (S :: Γ) S = .const family ls :=
    if_neg (not_isProof_of_sort hΓS (hS.weak henv))
  have EF : proofErase Γ F = .forallE (.const family ls) (.const family ls) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ S) (proofErase (S :: Γ) S) from
      if_neg (not_isProof_of_sort hΓ hF), Econst, Econst']
  refine ⟨hsel, ?_⟩
  rw [show proofErase Γ (.lam F (.app (.bvar 0) (.bvar (i + 1)))) = .lam _ _ from
    if_neg (not_isProof_fn hΓ hsel hid hnapp), EF]
  rw [show proofErase (F :: Γ) (.app (.bvar 0) (.bvar (i + 1))) = .app _ _ from if_neg hnbody]
  rw [show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_fn hΓF hfun harg hnbody)]
  rw [show proofErase (F :: Γ) (.bvar (i + 1)) = .bvar (i + 1) from
    if_neg (not_proof_at_positive_type hΓF (hS.weak henv) harg)]

/-- Two actual selector functions have a full future common comparison, but
application to the same typed identity has no such certificate. Both
applications beta-reduce to distinct positive-unit variables. The failure
holds even when the source and target primitive collections are identical. -/
theorem unit_family_shared_application_failure
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ∃ f g x A B, env.HasType univs Γ f (.forallE A B) ∧
      env.HasType univs Γ g (.forallE A B) ∧ env.HasType univs Γ x A ∧
      BetaStableFamily (fun Δ => JointCompare Source Δ true) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ g) ∧
      ¬ BetaStableFamily (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  obtain ⟨hfi, Efi⟩ := selector_typing hΓ hS hiT
  obtain ⟨hfj, Efj⟩ := selector_typing hΓ hS hjT
  have hid : env.HasType univs Γ (.lam (.const family ls) (.bvar 0))
      (.forallE (.const family ls) (.const family ls)) := .lam hS (.bvar .zero)
  refine ⟨_, _, _, _, _, hfi, hfj, hid, ?_, ?_⟩
  · rw [Efi, Efj]
    exact unit_selector_family hi hp hx hf
  · intro H
    have RI := proofErase_beta_forward hΓ (HasType.app hfi hid) (BetaRed.trans .beta .beta)
    have RJ := proofErase_beta_forward hΓ (HasType.app hfj hid) (BetaRed.trans .beta .beta)
    have HC := H.1 RI RJ
    simp only [VExpr.liftN_zero, VExpr.inst, VExpr.instVar_upper, VExpr.instVar_zero] at HC
    rw [show proofErase Γ (.bvar i) = .bvar i from
      if_neg (not_proof_at_positive_type hΓ hS hiT),
      show proofErase Γ (.bvar j) = .bvar j from
      if_neg (not_proof_at_positive_type hΓ hS hjT)] at HC
    exact hne (HC.bvar_injective hhead)

/-- A closed positive empty structure supplies an actual context witnessing
failure of shared application. The input future certificate uses no primitive
steps, while the proposed output fails even in the full joint union. -/
theorem unit_family_shared_application_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ f g x A B, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE A B) ∧ env.HasType univs Γ g (.forallE A B) ∧
      env.HasType univs Γ x A ∧
      BetaStableFamily (fun Δ => JointCompare (fun _ _ _ => False) Δ true) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ g) ∧
      ¬ BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hiT : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hjT : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨f, g, x, A, B, H⟩ := unit_family_shared_application_failure
    (Source := fun _ _ _ => False) erased_joint_union_head hΓ hi hp hx hf
    (hS.weak0 henv.ordered) hiT hjT (by decide)
  exact ⟨Γ, f, g, x, A, B, hΓ, H⟩

/-- The selector lambdas' future certificates cannot be inverted to future
body certificates. Instantiating their bound function by the typed identity
would expose distinct unit variables. Thus outer future stability does not
supply the hereditary binder invariant needed by the existing instantiation
theorem, even though arbitrary ambient substitutions are retained. -/
theorem unit_selector_body_not_future
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    let F := VExpr.forallE (.const family ls) (.const family ls)
    ¬ BetaStableFamily (fun Δ => JointCompare Target Δ true) (proofEraseCtx (F :: Γ))
      (proofErase (F :: Γ) (.app (.bvar 0) (.bvar (i + 1))))
      (proofErase (F :: Γ) (.app (.bvar 0) (.bvar (j + 1)))) := by
  dsimp only
  intro H
  obtain ⟨hfi, _⟩ := selector_typing hΓ hS hiT
  obtain ⟨hgj, _⟩ := selector_typing hΓ hS hjT
  obtain ⟨⟨_, hF⟩, _, hbi⟩ := hfi.lam_inv henv hΓ
  obtain ⟨_, _, hbj⟩ := hgj.lam_inv henv hΓ
  have hid : env.HasType univs Γ (.lam (.const family ls) (.bvar 0))
      (.forallE (.const family ls) (.const family ls)) := .lam hS (.bvar .zero)
  have hΓF : OnCtx ((VExpr.forallE (.const family ls) (.const family ls)) :: Γ)
      (env.IsType univs) := ⟨hΓ, _, hF⟩
  have HC := proofErase_family_inst hΓF hid hbi hbj H
  simp only [VExpr.inst, VExpr.instVar_zero, VExpr.instVar_upper] at HC
  have RI := proofErase_beta_forward hΓ (HasType.app hid hiT) BetaRed.beta
  have RJ := proofErase_beta_forward hΓ (HasType.app hid hjT) BetaRed.beta
  have HG := HC.1 RI RJ
  simp only [VExpr.inst, VExpr.instVar_zero] at HG
  rw [show proofErase Γ (.bvar i) = .bvar i from
    if_neg (not_proof_at_positive_type hΓ hS hiT),
    show proofErase Γ (.bvar j) = .bvar j from
    if_neg (not_proof_at_positive_type hΓ hS hjT)] at HG
  exact hne (HG.bvar_injective hhead)

end Lean4Lean.VEnv.Strengthening
