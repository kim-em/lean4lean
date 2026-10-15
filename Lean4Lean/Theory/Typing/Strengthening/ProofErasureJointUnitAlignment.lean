import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # Empty-structure carrier alignment beyond literal type joins

For an existing empty structure S parameterized by Prop -> Prop, S f and
S (fun p => f p) are equal typed carriers with no joint computational join.
Type comparison nevertheless supplies a guard at the eta-parameterized carrier
at the same finite stage. The theorem assumes the displayed registration and
constant typing; it does not construct a new registered environment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private functionType familyType function_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]
namespace UnitCarrierAlignment

private def native (family : Name) : VExpr := .app (.const family []) (.bvar 0)
private def assigned (family : Name) : VExpr :=
  .app (.const family []) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))
private def nativeRaw (family : Name) : ProofShape := .app (.const family []) (.bvar 0)
private def assignedRaw (family : Name) : ProofShape :=
  .app (.const family []) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))

private theorem family_typed (hc : env.constants family = some ⟨0, familyType⟩) :
    env.HasType univs Γ (.const family []) familyType := by
  exact HasType.const (Γ := Γ) hc (by simp) rfl

private theorem erasures (hc : env.constants family = some ⟨0, familyType⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (functionType :: Γ) (native family) = nativeRaw family ∧
      proofErase (functionType :: Γ) (assigned family) = assignedRaw family := by
  have hC : OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hF := family_typed (Γ := functionType :: Γ) hc
  have hf : env.HasType univs (functionType :: Γ) (.bvar 0) functionType := .bvar .zero
  have hη := (IsDefEq.eta hf).hasType.1
  have hT : env.HasType univs (functionType :: Γ) (native family) (.sort (.succ .zero)) := .app hF hf
  have hU : env.HasType univs (functionType :: Γ) (assigned family) (.sort (.succ .zero)) := .app hF hη
  have hC' : OnCtx (.sort .zero :: functionType :: Γ) (env.IsType univs) :=
    ⟨hC, _, HasType.sort (by trivial)⟩
  have hf' : env.HasType univs (.sort .zero :: functionType :: Γ) (.bvar 1) functionType :=
    .bvar (.succ .zero)
  have hx : env.HasType univs (.sort .zero :: functionType :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hbody := HasType.app hf' hx
  have EF : proofErase (functionType :: Γ) (.const family []) = .const family [] :=
    if_neg (not_isProof_function_to_sort hC hF)
  have Ef : proofErase (functionType :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_function_to_sort hC hf)
  constructor
  · change proofErase _ (.app _ _) = _
    rw [show proofErase (functionType :: Γ) (.app (.const family []) (.bvar 0)) = .app _ _ from if_neg (not_isProof_of_sort hC hT), EF, Ef]
    rfl
  · change proofErase _ (.app _ _) = _
    rw [show proofErase (functionType :: Γ) (.app (.const family []) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))) = .app _ _ from if_neg (not_isProof_of_sort hC hU), EF]
    rw [show proofErase _ (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0))) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hC hη)]
    rw [show proofErase (functionType :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hC (HasType.sort (by trivial)))]
    rw [show proofErase (.sort .zero :: functionType :: Γ) (.app (.bvar 1) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hC' hbody)]
    rw [show proofErase (.sort .zero :: functionType :: Γ) (.bvar 1) = .bvar 1 from
      if_neg (not_isProof_function_to_sort hC' hf')]
    rw [show proofErase (.sort .zero :: functionType :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hC' hx)]
    rfl

omit [Params] in
private theorem normal_forms {Step : List ProofShape → ProofShape → ProofShape → Prop}
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out) (Δ) :
    NormalSyntax (Step Δ) (nativeRaw family) ∧ NormalSyntax (Step Δ) (assignedRaw family) := by
  have hv (i) : NormalSyntax (Step Δ) (.bvar i) := ⟨fun _ H => hhead H, trivial⟩
  have hs : NormalSyntax (Step Δ) (.sort .zero) := ⟨fun _ H => hhead H, trivial⟩
  have hc : NormalSyntax (Step Δ) (.const family []) := ⟨fun _ H => hn (args := []) H, trivial⟩
  have happ {a} (H : NormalSyntax (Step Δ) a) : NormalSyntax (Step Δ) (.app (.const family []) a) :=
    ⟨fun _ H => hn (args := [a]) H, (fun _ _ H => nomatch H), hc, H⟩
  have hb : NormalSyntax (Step Δ) (.app (.bvar 1) (.bvar 0)) :=
    ⟨fun _ H => hhead H, (fun _ _ H => nomatch H), hv 1, hv 0⟩
  exact ⟨happ (hv 0), happ ⟨(fun _ H => hhead H), hs, hb⟩⟩

/-- Conditional on an existing registered empty family S : (Prop -> Prop) ->
Type, its eta-variant parameters give actual typed carriers with no join in the
whole repaired joint union. At every finite stage, their type comparison still
constructs arbitrary endpoint guards at the target carrier. -/
theorem typed_alignment_without_join
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (hc : env.constants family = some ⟨0,
      .forallE (.forallE (.sort .zero) (.sort .zero)) (.sort (.succ .zero))⟩)
    (hi : env.projections family info) (hp : info.nparams = 1)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' T U, OnCtx Γ' (env.IsType univs) ∧
      env.HasType univs Γ' T (.sort (.succ .zero)) ∧
      env.HasType univs Γ' U (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ' T U (.sort (.succ .zero)) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion (ErasedQuotCore.definitions hq)) (proofEraseCtx Γ') (proofErase Γ' T) shared ∧
        ScopedCompute (ErasedJointUnion (ErasedQuotCore.definitions hq)) (proofEraseCtx Γ') (proofErase Γ' U) shared) ∧
      ∀ stage, JointCompare (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
          (proofEraseCtx Γ') false (proofErase Γ' T) (proofErase Γ' U) ∧
        ∀ a b, JointCarrierGuard (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
          (proofEraseCtx Γ') (proofErase Γ' U) a b := by
  have hC : OnCtx (functionType :: Γ) (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hF := family_typed (Γ := functionType :: Γ) hc
  have hvar : env.HasType univs (functionType :: Γ) (.bvar 0) functionType := .bvar .zero
  have Heta := IsDefEq.eta hvar
  have hT : env.HasType univs (functionType :: Γ) (native family) (.sort (.succ .zero)) := .app hF hvar
  have hU : env.HasType univs (functionType :: Γ) (assigned family) (.sort (.succ .zero)) := .app hF Heta.hasType.1
  obtain ⟨ET, EU⟩ := erasures hc hΓ
  have hn {Δ args out} : ¬ ErasedJointUnion (ErasedQuotCore.definitions hq) Δ
      (ProofShape.mkApps (.const family []) args) out := fun R =>
    erased_joint_union_no_rigid heq (henv.projectionRigid hi)
      (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) R (ProofShape.constHead_mkApps _ _)
  refine ⟨functionType :: Γ, native family, assigned family, hC, hT, hU,
    IsDefEq.appDF hF Heta.symm, ?_, ?_⟩
  · rintro ⟨shared, RT, RU⟩
    rw [ET] at RT
    rw [EU] at RU
    have EN := scoped_normal_fixed RT (fun Δ => (normal_forms (Step := ErasedJointUnion (ErasedQuotCore.definitions hq)) erased_joint_union_head hn Δ).1)
    have EA := scoped_normal_fixed RU (fun Δ => (normal_forms (Step := ErasedJointUnion (ErasedQuotCore.definitions hq)) erased_joint_union_head hn Δ).2)
    cases EN.symm.trans EA
  · intro stage
    have HC : JointCompare (ErasedJointStage (ErasedQuotCore.definitions hq) stage)
        (proofEraseCtx (functionType :: Γ)) false
        (proofErase (functionType :: Γ) (native family))
        (proofErase (functionType :: Γ) (assigned family)) := by
      rw [ET, EU]
      exact .app (.leaf .refl) (.leaf (.etaR (.boundVar (f := ProofShape.bvar 0))))
    refine ⟨HC, fun a b => ?_⟩
    exact proofErase_joint_quot_unit_carrier_target heq hq hi hx hf (ps := [.bvar 0])
      (by simpa using hp.symm) hC hT hU HC ET

end UnitCarrierAlignment
end Lean4Lean.VEnv.Strengthening
