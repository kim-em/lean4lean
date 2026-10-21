import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe

/-! # Joined arguments with non-joining application residuals

The identity and eta-expanding lambda apply to a function variable and an
identity-redex copy of that variable. Argument computation supplies a join;
the applications reduce to distinct normal eta endpoints. The constructed
future certificate therefore does more than produce an application join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private functionType function_type etaRaw erasures
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- Two displayed lambda applications receive a future certificate from joined
arguments and an eta body certificate. They have no certified computational
join: their beta reducts are a variable and its distinct normal eta expansion. -/
theorem joined_arguments_nonjoining_applications
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' a b T, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' a T ∧ env.HasType univs Γ' b T ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
        (proofEraseCtx Γ') (proofErase Γ' a) (proofErase Γ' b) ∧
      ProofShape.BetaRed (proofErase Γ' a) (.bvar 0) ∧
      ProofShape.BetaRed (proofErase Γ' b) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) ∧
      ¬ ∃ shared, ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ') (proofErase Γ' a) shared ∧
        ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ') (proofErase Γ' b) shared := by
  let A := functionType
  let Γ' := A :: Γ
  have hC : OnCtx Γ' (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hA : env.HasType univs Γ' A (.sort (.imax (.succ .zero) (.succ .zero))) := function_type
  have hf : env.HasType univs Γ' (.bvar 0) A := .bvar .zero
  have hC' : OnCtx (A :: Γ') (env.IsType univs) := ⟨hC, _, hA⟩
  have hx : env.HasType univs (A :: Γ') (.bvar 0) A := .bvar .zero
  have HE := IsDefEq.eta hx
  let body := VExpr.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))
  have hb : env.HasType univs (A :: Γ') body A := HE.hasType.1
  let y := VExpr.app (.lam A (.bvar 0)) (.bvar 0)
  have hy : env.HasType univs Γ' y A := .app (.lam hA hx) hf
  have RY : ProofShape.BetaRed (proofErase Γ' y) (proofErase Γ' (.bvar 0)) :=
    proofErase_beta_forward hC hy .beta
  have Hbody := (proofErase_function_eta_family (Step := ErasedJointUnion D) hC' hx).joint_symm
  have H := proofErase_family_apply_lams_joined heq hs hC hA hx hb hf hy Hbody .refl (.beta RY)
  let a := y
  let b := VExpr.app (.lam A body) y
  have ha : env.HasType univs Γ' a A := hy
  have hb' : env.HasType univs Γ' b A := .app (.lam hA hb) hy
  have RB : ProofShape.BetaRed (proofErase Γ' b) (proofErase Γ' body) :=
    proofErase_beta_forward hC hb' (.trans (.app .refl .beta) .beta)
  obtain ⟨_, Ef, Eη⟩ := erasures hΓ
  change proofErase Γ' (.bvar 0) = .bvar 0 at Ef
  change proofErase Γ' body = etaRaw at Eη
  have RA : ProofShape.BetaRed (proofErase Γ' a) (.bvar 0) := by simpa only [Ef] using RY
  have RB : ProofShape.BetaRed (proofErase Γ' b) etaRaw := by simpa only [Eη] using RB
  refine ⟨Γ', a, b, A, hC, ha, hb', H, RA, RB, ?_⟩
  rintro ⟨shared, CA, CB⟩
  obtain ⟨left, BL, CL⟩ := proofErase_beta_stable_joint_beta_commute heq hs hC ha CA RA
  obtain ⟨right, BR, CR⟩ := proofErase_beta_stable_joint_beta_commute heq hs hC hb' CB RB
  have EL := CL.bvar_fixed erased_beta_stable_joint_head
  have hnormal (Δ) : NormalSyntax (ErasedBetaStableJoint D Δ) etaRaw := by
    have hv (i) : NormalSyntax (ErasedBetaStableJoint D Δ) (.bvar i) :=
      ⟨fun _ H => erased_beta_stable_joint_head H, trivial⟩
    have hs : NormalSyntax (ErasedBetaStableJoint D Δ) (.sort .zero) :=
      ⟨fun _ H => erased_beta_stable_joint_head H, trivial⟩
    exact ⟨fun _ H => erased_beta_stable_joint_head H, hs,
      (fun _ H => erased_beta_stable_joint_head H), (fun _ _ H => nomatch H), hv 1, hv 0⟩
  have ER := scoped_normal_fixed CR hnormal
  rw [EL] at BL
  rw [ER] at BR
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hC ha rfl rfl CA
  rw [← EE] at BL BR
  obtain ⟨out, HL, HR⟩ := proofErase_beta_confluent hC HE.hasType.2 BL BR
  have EL := HL.fixed_of_normal
    (show NormalSyntax (fun _ _ => False) (.bvar 0) from ⟨fun _ H => H, trivial⟩)
  have ER := HR.fixed_of_normal (hnormal [])
  cases EL.symm.trans ER

end Lean4Lean.VEnv.Strengthening
