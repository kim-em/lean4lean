import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationFront

/-! # Proposition-valued future application still exposes native carriers

Selector functions bind a predicate on a positive unit. Their future common
certificates survive ambient substitution because the bound predicate stays
neutral. Applying them to one predicate assigned the unit domain but declared
at another domain forces carrier checking at that native domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem prop_selector_beta (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (R : ProofShape.BetaRed
      (.lam (.forallE (.const family ls) (.sort .zero)) (.app (.bvar 0) a)) p)
    (S : ProofShape.BetaRed
      (.lam (.forallE (.const family ls) (.sort .zero)) (.app (.bvar 0) b)) q) :
    JointCompare Step Δ true p q := by
  obtain ⟨D, body, rfl, RD, RB⟩ := R.lam_inv
  obtain ⟨E, body', rfl, RE, RB'⟩ := S.lam_inv
  have hn : NormalSyntax (fun _ _ => False)
      (.forallE (.const family ls) (.sort .zero)) :=
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
      apply JointCheck.appCarrier (A := .const family ls) (B := .sort .zero)
      · exact .bvar
      · exact .leaf .refl
      · exact .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)

/-- A bound neutral function hides distinct unit arguments from beta even
after arbitrary ambient substitution. Consequently these selector lambdas
have full future common certificates at every primitive collection. The
certificate does not assert future substitution of the bound function. -/
theorem unit_prop_selector_family (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (.lam (.forallE (.const family ls) (.sort .zero)) (.app (.bvar 0) a))
      (.lam (.forallE (.const family ls) (.sort .zero)) (.app (.bvar 0) b)) := by
  refine ⟨fun R S => prop_selector_beta hi hp hx hf R S, ?_⟩
  intro Δ' τ p q _ R S
  simp only [ProofShape.subst, ProofShape.Subst.lift] at R S
  exact prop_selector_beta hi hp hx hf R S

/-- Missing future application law restricted to proposition-valued functions
and their one shared typed argument. The conclusion retains future paths.
No proof or strictness claim is made for this law. -/
def TypedFuturePropositionApplication
    (Source Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ f g x A}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ f (.forallE A (.sort .zero)) →
    env.HasType univs Γ g (.forallE A (.sort .zero)) → env.HasType univs Γ x A →
    BetaStableFamily (fun Δ => JointCompare Source Δ true) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) →
    BetaStableFamily (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x))

private theorem prop_selector_typing
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hx : env.HasType univs Γ x (.const family ls)) :
    let F := VExpr.forallE (.const family ls) (.sort .zero)
    let f := VExpr.lam F (.app (.bvar 0) x.lift)
    env.HasType univs Γ f (.forallE F (.sort .zero)) ∧
    proofErase Γ f = .lam (.forallE (.const family ls) (.sort .zero))
      (.app (.bvar 0) ((proofErase Γ x).liftN 1)) := by
  dsimp only
  let S := VExpr.const family ls
  let F := VExpr.forallE S (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallE hS (.sort (by trivial))
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have hfun : env.HasType univs (F :: Γ) (.bvar 0) F := .bvar .zero
  have harg : env.HasType univs (F :: Γ) x.lift S := hx.weak henv
  have hbody : env.HasType univs (F :: Γ) (.app (.bvar 0) x.lift) (.sort .zero) := .app hfun harg
  have hsel := HasType.lam hF hbody
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have EF : proofErase Γ F = .forallE (.const family ls) (.sort .zero) := by
    rw [show proofErase Γ F = .forallE (proofErase Γ S) (proofErase (S :: Γ) (.sort .zero)) from
      if_neg (not_isProof_of_sort hΓ hF),
      show proofErase Γ S = .const family ls from if_neg (not_isProof_of_sort hΓ hS),
      show proofErase (S :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓS (HasType.sort (by trivial)))]
  refine ⟨hsel, ?_⟩
  rw [show proofErase Γ (.lam F (.app (.bvar 0) x.lift)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ hsel), EF]
  rw [show proofErase (F :: Γ) (.app (.bvar 0) x.lift) = .app _ _ from
    if_neg (not_isProof_of_sort hΓF hbody),
    show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hΓF hfun)]
  rw [proofErase_liftN hΓ hΓF Ctx.LiftN.one hx]

/-- Proposition-only future application already moves the unit argument
certificate to a predicate variable's native domain. Its actual assigned
unit-domain typing is the only conversion premise. The input selector
certificate works even with no source primitives. -/
theorem TypedFuturePropositionApplication.native_unit_guard
    (Happ : TypedFuturePropositionApplication Source Target)
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hz : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hB : env.HasType univs Γ B (.sort v))
    (hl : Lookup Γ f (.forallE B (.sort .zero)))
    (hfS : env.HasType univs Γ (.bvar f) (.forallE (.const family ls) (.sort .zero)))
    (hx : env.HasType univs Γ x (.const family ls))
    (hy : env.HasType univs Γ y (.const family ls)) :
    JointCarrierGuard Target (proofEraseCtx Γ) (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  obtain ⟨hfx, Efx⟩ := prop_selector_typing hΓ hS hx
  obtain ⟨hgy, Egy⟩ := prop_selector_typing hΓ hS hy
  have HC := Happ hΓ hfx hgy hfS (by
    rw [Efx, Egy]
    exact unit_prop_selector_family hi hp hz hf)
  have RX := proofErase_beta_forward hΓ (hfx.app hfS) BetaRed.beta
  have RY := proofErase_beta_forward hΓ (hgy.app hfS) BetaRed.beta
  have HG := HC.1 RX RY
  simp only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] at HG
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (not_isProof_function_to_sort hΓ hfS)
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hPiB := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have EPiB : proofErase Γ (.forallE B (.sort .zero)) = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPiB),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from
        if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))]
  have HO : contextOracle (proofEraseCtx Γ) f = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl, EPiB]
  rw [show proofErase Γ (.app (.bvar f) x) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ (hfS.app hx)),
    show proofErase Γ (.app (.bvar f) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ (hfS.app hy)), EF] at HG
  exact HG.bvar_app_carrier hhead HO

/-- Proposition-valued shared application transports all actual unit values
to any definitionally equal supplied carrier. A fresh predicate observes the
target domain; forward substitution of an exactly recovered inhabitant
removes its binder. No strengthening or general substitution law is used. -/
theorem TypedFuturePropositionApplication.unit_carrier_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Happ : TypedFuturePropositionApplication Source (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hz : info.nindices = 0) (hf : info.numFields = 0)
    (HE : env.IsDefEq univs Γ (.const family ls) B (.sort (.succ u)))
    (hx : env.HasType univs Γ x (.const family ls))
    (hy : env.HasType univs Γ y (.const family ls)) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have hS := HE.hasType.1
  have hB := HE.hasType.2
  let F := VExpr.forallE B (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallE hB (.sort (by trivial))
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have HFS : env.IsDefEq univs Γ F (.forallE (.const family ls) (.sort .zero))
      (.sort (.imax (.succ u) (.succ .zero))) :=
    .forallEDF HE.symm (.sortDF (by trivial) (by trivial) rfl)
  have hl : Lookup (F :: Γ) 0 (.forallE B.lift (.sort .zero)) := by
    simpa only [F, VExpr.lift, VExpr.liftN] using (Lookup.zero (ty := F) (Γ := Γ))
  have hfS : env.HasType univs (F :: Γ) (.bvar 0) (.forallE (.const family ls) (.sort .zero)) := by
    simpa only [VExpr.lift, VExpr.liftN] using
      (HFS.weak henv (B := F)).defeq (HasType.bvar (Lookup.zero (ty := F)))
  have HC := Happ.native_unit_guard erased_joint_union_head hΓF hi hp hz hf
    (hS.weak henv) (hB.weak henv) hl hfS (hx.weak henv) (hy.weak henv)
  obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
  obtain ⟨f, hft, _, RF⟩ := recoverable_prop_function (Step := ErasedJointStage D 0) heq hΓ hB
  have Hout := proofErase_joint_carrier_inst_recoverable heq hs hΓ hft (fun _ => RF)
    ((HE.defeq hx).weak henv) ((HE.defeq hy).weak henv) HC
  simp only [Nat.zero_add, VExpr.inst_lift] at Hout
  exact Hout.mono (fun H => ⟨stage, H⟩)

end Lean4Lean.VEnv.Strengthening
