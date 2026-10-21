import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageBetaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction

/-! # Reading native argument carriers from neutral applications

A comparison of f x and f y, for a variable f with a literal Pi oracle,
contains an argument carrier guard at that native domain. Computation may
change arguments and recovered domains; the readout retains both paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- A computation from a variable-headed unary application changes only its
argument. This includes arbitrary beta and sequential primitive computation. -/
theorem ProofShape.ScopedCompute.bvar_app_inv
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.app (.bvar f) a) out) :
    ∃ a', out = .app (.bvar f) a' ∧ ScopedCompute Step Δ a a' := by
  obtain ⟨args, HE, HA⟩ := R.bvar_spine (args := [a]) hhead
  cases HA with
  | cons RA Hnil =>
    cases Hnil
    exact ⟨_, HE, RA⟩

variable [Params]

/-- Neutral application comparison yields a guard at the variable's native
oracle domain. Recovery conversions are retained as carrier computations;
argument computations are retained as endpoint computations. The result needs
no typings, recovery completeness, or conversion of carrier domains. -/
theorem ProofShape.JointCompare.bvar_app_carrier
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HO : contextOracle Δ f = .forallE A B)
    (H : JointCompare Step Δ mode (.app (.bvar f) x) (.app (.bvar f) y)) :
    JointCarrierGuard Step Δ A x y := by
  generalize EL : ProofShape.app (.bvar f) x = a at H
  generalize ER : ProofShape.app (.bvar f) y = b at H
  change JointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing f x y mode A B with
  | leaf H =>
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (EL.trans ER.symm)).2
      rw [E]
      exact .carrierChecked (.leaf .refl)
    | sort | const => cases EL
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EL.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases ER.trans E
  | app HF HX =>
    cases EL
    cases ER
    exact .carrierChecked HX
  | appCarrier R HF HX =>
    cases EL
    cases ER
    have RT := R.bvar_compute
    rw [HO] at RT
    obtain ⟨A', B', E, RA⟩ := RT.forallE_domain_inv hhead
    cases E
    exact .carrierCompute RA HX
  | compute RX RY HC ih =>
    obtain ⟨x', EX, RX'⟩ := (EL ▸ RX).bvar_app_inv hhead
    obtain ⟨y', EY, RY'⟩ := (ER ▸ RY).bvar_app_inv hhead
    exact .carrierReduce RX' RY' (ih HO EX.symm EY.symm hk)
  | symm HC ih => exact .carrierSymm (ih HO ER EL hk)
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases ER
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EL
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- For a variable with a literal Pi oracle, neutral application comparison is
exactly explicit checking of its arguments at the native domain. This remains
true in either comparison mode and through arbitrary computation prefixes. -/
theorem ProofShape.JointCompare.bvar_app_iff
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HO : contextOracle Δ f = .forallE A B) :
    JointCompare Step Δ mode (.app (.bvar f) x) (.app (.bvar f) y) ↔
      JointCarrierGuard Step Δ A x y := by
  constructor
  · exact JointCompare.bvar_app_carrier hhead HO
  · intro H
    have HR : ScopedTypeRecovery Step Δ (.bvar f) (.forallE A B) := by
      rw [← HO]
      exact .bvar
    exact .appCarrier HR (.leaf .refl) H

/-- Proposition endpoint-beta transport necessarily moves an argument guard
from an assigned domain A to a variable function's native domain B. The source
comparison uses the eta wrapper with displayed domain A and reflexive function
comparison; its beta contracta expose the native application. No relation
between A and B is assumed beyond the supplied ordinary typing of the function.
This is a necessary consequence, not a proved carrier-conversion closure law. -/
theorem JointPropBetaTransport.native_domain_guard
    (Hbeta : JointPropBetaTransport Source Target)
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (hl : Lookup Γ f (.forallE B (.sort .zero)))
    (hfA : env.HasType univs Γ (.bvar f) (.forallE A (.sort .zero)))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard Target (proofEraseCtx Γ) (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have hn := not_isProof_function_to_sort hΓ hfA
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg hn
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, v, hB⟩
  have hPiB := HasType.forallE hB (HasType.sort (l := .zero) (by trivial))
  have EPiB : proofErase Γ (.forallE B (.sort .zero)) = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPiB),
      show proofErase (B :: Γ) (.sort .zero) = .sort .zero from if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))]
  have HO : contextOracle (proofEraseCtx Γ) f = .forallE (proofErase Γ B) (.sort .zero) := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl, EPiB]
  let body := VExpr.app (VExpr.bvar f).lift (.bvar 0)
  let wrapper := VExpr.lam A body
  have hb : env.HasType univs (A :: Γ) body (.sort .zero) := by
    simpa only [body, lift, VExpr.liftN, inst_liftN_bvar, VExpr.inst] using
      HasType.app (hfA.weak henv (B := A)) (HasType.bvar Lookup.zero)
  have hw : env.HasType univs Γ wrapper (.forallE A (.sort .zero)) := .lam hA hb
  have Ebody : proofErase (A :: Γ) body =
      .app ((ProofShape.bvar f).liftN 1) (etaArgument u) := by
    simpa only [body, EF] using proofErase_eta_body hΓ hA hfA hn
  have EW : proofErase Γ wrapper = .lam (proofErase Γ A)
      (.app ((ProofShape.bvar f).liftN 1) (etaArgument u)) := by
    rw [show proofErase Γ wrapper = .lam (proofErase Γ A) (proofErase (A :: Γ) body) from
      if_neg (not_isProof_function_to_sort hΓ hw), Ebody]
  have HR : ScopedTypeRecovery Source (proofEraseCtx Γ) (proofErase Γ wrapper)
      (.forallE (proofErase Γ A) (.sort .zero)) := by
    rw [EW]
    apply ScopedTypeRecovery.lam
    have RF : ScopedTypeRecovery Source (proofErase Γ A :: proofEraseCtx Γ)
        ((ProofShape.bvar f).liftN 1) (.forallE ((proofErase Γ B).liftN 1) (.sort .zero)) := by
      have R := ScopedTypeRecovery.bvar (Step := Source) (Δ := proofErase Γ A :: proofEraseCtx Γ) (i := f + 1)
      simpa only [contextOracle, TypeOracle.cons, HO, ProofShape.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm] using R
    exact ScopedTypeRecovery.app (a := etaArgument u) RF
  have hlx := hw.app hx
  have hly := hw.app hy
  have HL : JointCompare Source (proofEraseCtx Γ) true
      (proofErase Γ (.app wrapper x)) (proofErase Γ (.app wrapper y)) := by
    rw [show proofErase Γ (.app wrapper x) = .app _ _ from if_neg (not_isProof_of_sort hΓ hlx),
      show proofErase Γ (.app wrapper y) = .app _ _ from if_neg (not_isProof_of_sort hΓ hly)]
    exact .appCarrier HR (.leaf .refl) HX
  have RP : ProofShape.BetaRed (proofErase Γ (.app wrapper x)) (proofErase Γ (.app (.bvar f) x)) := by
    simpa only [body, wrapper, VExpr.inst, instVar_zero, inst_lift] using
      proofErase_beta_forward hΓ hlx (VExpr.BetaRed.beta (A := A) (b := body) (a := x))
  have RQ : ProofShape.BetaRed (proofErase Γ (.app wrapper y)) (proofErase Γ (.app (.bvar f) y)) := by
    simpa only [body, wrapper, VExpr.inst, instVar_zero, inst_lift] using
      proofErase_beta_forward hΓ hly (VExpr.BetaRed.beta (A := A) (b := body) (a := y))
  have HC := Hbeta hΓ hlx hly HL RP RQ
  rw [show proofErase Γ (.app (.bvar f) x) = .app _ _ from if_neg (not_isProof_of_sort hΓ (hfA.app hx)),
    show proofErase Γ (.app (.bvar f) y) = .app _ _ from if_neg (not_isProof_of_sort hΓ (hfA.app hy)), EF] at HC
  exact JointCompare.bvar_app_carrier hhead HO HC

open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Even beta transport from one finite source stage entails carrier transport
along arbitrary ordinary type conversion. A fresh observer declared at B -> Prop
is assigned A -> Prop, exposing the target guard after head beta. Its unused
binder is then removed by an exactly recovered inhabitant, using forward typed
substitution. This does not assume strengthening or compared recovery coverage. -/
theorem JointPropBetaTransport.carrier_conversion_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A B (.sort u))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ x) (proofErase Γ y) := by
  have hA := HE.hasType.1
  have hB := HE.hasType.2
  let F := VExpr.forallE B (.sort .zero)
  have hF : env.HasType univs Γ F (.sort (.imax u (.succ .zero))) :=
    .forallE hB (.sort (by trivial))
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, _, hF⟩
  have HFA : env.IsDefEq univs Γ F (.forallE A (.sort .zero))
      (.sort (.imax u (.succ .zero))) :=
    .forallEDF HE.symm (.sortDF (by trivial) (by trivial) rfl)
  have hl : Lookup (F :: Γ) 0 (.forallE B.lift (.sort .zero)) := by
    simpa only [F, lift, VExpr.liftN] using (Lookup.zero (ty := F) (Γ := Γ))
  have hfA : env.HasType univs (F :: Γ) (.bvar 0) (.forallE A.lift (.sort .zero)) := by
    simpa only [lift, VExpr.liftN] using
      (HFA.weak henv (B := F)).defeq (HasType.bvar (Lookup.zero (ty := F)))
  have HL := HX.rename (erased_joint_stage_rename heq hs stage)
    (ContextRenaming.of_liftN hΓ hΓF Ctx.LiftN.one)
  simp only [JointCheckKind.subst, subst_bvar_liftN] at HL
  rw [← proofErase_liftN hΓ hΓF Ctx.LiftN.one hA,
    ← proofErase_liftN hΓ hΓF Ctx.LiftN.one hx,
    ← proofErase_liftN hΓ hΓF Ctx.LiftN.one hy] at HL
  have HC := Hbeta.native_domain_guard erased_joint_union_head hΓF
    (hA.weak henv) (hB.weak henv) hl hfA (hx.weak henv) (hy.weak henv) HL
  obtain ⟨targetStage, HC⟩ := HC.finite_stage erased_joint_stage_mono
  obtain ⟨f, hf, _, RF⟩ := recoverable_prop_function (Step := ErasedJointStage D 0) heq hΓ hB
  have Hout := proofErase_joint_carrier_inst_recoverable heq hs hΓ hf (fun _ => RF)
    ((HE.defeq hx).weak henv) ((HE.defeq hy).weak henv) HC
  simp only [Nat.zero_add, VExpr.inst_lift] at Hout
  exact Hout.mono (fun H => ⟨targetStage, H⟩)

end Lean4Lean.VEnv.Strengthening
