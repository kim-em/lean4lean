import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignmentExample

/-! # Native application checking with non-joining result parameters

For the declaration `(R : Sort u) → (Prop → R) → Prop`, changing the result
parameter leaves the argument carrier's displayed domain intact. A neutral
source result therefore transports every joint guard to the target native
domain. Ordinary type equality supplies the target argument typings; no raw
native-type congruence or computational join is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_app native_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoverablePropFunction
open private replaceResult_neutral
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignment
variable [Params]

/-- A result parameter occurs only at the end of the function argument's
telescope. In particular, it does not occur in that telescope's domain. -/
def nativeResultObserverType (u : VLevel) : VExpr :=
  .forallE (.sort u) (.forallE (.forallE (.sort .zero) (.bvar 1)) (.sort .zero))

/-- The result-only observer needs no recursive declaration or logical axiom:
a closed implementation returns the proposition `∀ P : Prop, P`. -/
theorem nativeResultObserverType_inhabited (hu : u.WF univs) :
    ∃ e, env.HasType univs [] e (nativeResultObserverType u) := by
  have hR : env.HasType univs [.sort .zero, .sort u] (.bvar 1) (.sort u) :=
    .bvar (.succ .zero)
  have hF := HasType.forallE (HasType.sort (l := .zero) (by trivial)) hR
  have hP (Γ) : env.HasType univs Γ (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  exact ⟨_, HasType.lam (HasType.sort hu) (HasType.lam hF (hP _))⟩

private theorem erase_function_result
    (hΓ : OnCtx Γ (env.IsType univs)) (hR : env.HasType univs Γ R (.sort u)) :
    proofErase Γ (.forallE (.sort .zero) R.lift) =
      .forallE (.sort .zero) ((proofErase Γ R).liftN 1) := by
  have hΓ' : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hF := HasType.forallE (HasType.sort (l := .zero) (by trivial)) (hR.weak henv)
  rw [show proofErase Γ (.forallE (.sort .zero) R.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hF),
    show proofErase Γ (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
    proofErase_liftN hΓ hΓ' Ctx.LiftN.one hR]

/-- Neutral result parameters transport arbitrary function guards to a new
result type. Both erasures are derived from actual types, so the retained
domain is literally Prop on both sides. No relation between parameters is
needed for this raw guard transport; sound use must supply target typings. -/
theorem proofErase_neutral_function_result_guard
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hR : env.HasType univs Γ R (.sort u)) (hS : env.HasType univs Γ S (.sort v))
    (ER : proofErase Γ R = ProofShape.mkApps (.bvar i) args)
    (H : JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.sort .zero) R.lift)) a b) :
    JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.sort .zero) S.lift)) a b := by
  rw [erase_function_result hΓ hR, ER, ProofShape.liftN_mkApps] at H
  simp only [ProofShape.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm] at H
  rw [erase_function_result hΓ hS]
  have N : NeutralResult (.forallE (.sort .zero)
      (ProofShape.mkApps (.bvar (i + 1)) (args.map (ProofShape.liftN 1)))) :=
    .forallE .neutral
  simpa only [replaceResult, replaceResult_neutral] using
    H.replace_neutral_result (result := (proofErase Γ S).liftN 1) hhead N

/-- A result-only native observer consumes a guard supplied at its old
parameter, even when the old and new parameters have no computational join.
The actual target prefix is recovered, its argument guard is transported,
and both proposition endpoint typings are constructed. This holds for any
primitive relation with the joint head invariant, including the full union. -/
theorem proofErase_native_neutral_result_propositions
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars) (hdecl : ci.type.instL ls = nativeResultObserverType u)
    (HRS : env.IsDefEq univs Γ R S (.sort u))
    (ER : proofErase Γ R = ProofShape.mkApps (.bvar i) args)
    (hx : env.HasType univs Γ x (.forallE (.sort .zero) R.lift))
    (hy : env.HasType univs Γ y (.forallE (.sort .zero) R.lift))
    (HX : JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.sort .zero) R.lift)) (proofErase Γ x) (proofErase Γ y)) :
    let f := VExpr.app (.const c ls) S
    env.HasType univs Γ (.app f x) (.sort .zero) ∧
      env.HasType univs Γ (.app f y) (.sort .zero) ∧
      JointCompare Step (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  have h0 : env.HasType univs Γ (.const c ls) (nativeResultObserverType u) :=
    hdecl ▸ HasType.const hc hw hl
  have hf : env.HasType univs Γ (.app (.const c ls) S)
      (.forallE (.forallE (.sort .zero) S.lift) (.sort .zero)) := by
    simpa [nativeResultObserverType, VExpr.inst, instVar, VExpr.liftN] using h0.app HRS.hasType.2
  have HE := IsDefEq.forallEDF (HasType.sort (l := .zero) (by trivial)) (HRS.weak henv)
  have hL := hf.app (HE.defeq hx)
  have hR := hf.app (HE.defeq hy)
  have hn := not_isProof_function_to_sort hΓ hf
  have hn0 := not_isProof_fn hΓ h0 HRS.hasType.2 hn
  have R0 := native_const (Step := Step) hΓ hc hw hl hn0
  rw [hdecl] at R0
  have RF := native_app hΓ h0 HRS.hasType.2 hn R0
  have RF : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.app (.const c ls) S))
      (proofErase Γ (.forallE (.forallE (.sort .zero) S.lift) (.sort .zero))) := by
    simpa [nativeResultObserverType, VExpr.inst, instVar, VExpr.liftN] using RF
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE (.forallE (.sort .zero) S.lift) (.sort .zero)) =
    .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at RF
  have HG := proofErase_neutral_function_result_guard hhead hΓ HRS.hasType.1 HRS.hasType.2 ER HX
  refine ⟨hL, hR, ?_⟩
  rw [show proofErase Γ (.app (.app (.const c ls) S) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hL),
    show proofErase Γ (.app (.app (.const c ls) S) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hR)]
  exact .appCarrier RF (.leaf .refl) HG

open private context native assigned nativeRaw assignedRaw erasures context_wf
  types_equal source_typed normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private nativeType assignedType nativeShape assignedShape erase_types normal_types
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignmentExample
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout

/-- The result-parameter case is strictly outside the parameter-join case:
actual eta-compared parameters, and their native function domains, have no
computational join even in the full union. The source domain is inhabited.
Nevertheless every finite-stage guard at that domain produces an actual
proposition comparison at the target observer prefix, at the same stage.
The assumed observer declaration has the closed inhabitant proved above. -/
theorem native_neutral_result_without_join (D : PureObservation.Definitions)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (hdecl : ci.type.instL ls = nativeResultObserverType (.succ .zero)) :
    ∃ Γ' R S, OnCtx Γ' (env.IsType univs) ∧
      env.IsDefEq univs Γ' R S (.sort (.succ .zero)) ∧
      JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ') false
        (proofErase Γ' R) (proofErase Γ' S) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' R) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' S) shared) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
          (proofErase Γ' (.forallE (.sort .zero) R.lift)) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
          (proofErase Γ' (.forallE (.sort .zero) S.lift)) shared) ∧
      (∃ x, env.HasType univs Γ' x (.forallE (.sort .zero) R.lift)) ∧
      ∀ stage x y,
        env.HasType univs Γ' x (.forallE (.sort .zero) R.lift) →
        env.HasType univs Γ' y (.forallE (.sort .zero) R.lift) →
        JointCarrierGuard (ErasedJointStage D stage) (proofEraseCtx Γ')
          (proofErase Γ' (.forallE (.sort .zero) R.lift)) (proofErase Γ' x) (proofErase Γ' y) →
        let f := VExpr.app (.const c ls) S
        env.HasType univs Γ' (.app f x) (.sort .zero) ∧
          env.HasType univs Γ' (.app f y) (.sort .zero) ∧
          JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ') false
            (proofErase Γ' (.app f x)) (proofErase Γ' (.app f y)) := by
  have hC := context_wf hΓ
  obtain ⟨EN, EA⟩ := erasures hΓ
  obtain ⟨EFN, EFA⟩ := erase_types hΓ
  refine ⟨context Γ, assigned, native, hC, types_equal, ?_, ?_, ?_, ?_, ?_⟩
  · rw [EA, EN]
    exact .app (.leaf .refl) (.leaf (.etaL (.boundVar (f := ProofShape.bvar 2))))
  · rintro ⟨shared, RA, RN⟩
    rw [EA] at RA
    rw [EN] at RN
    have HA := scoped_normal_fixed RA (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
    have HN := scoped_normal_fixed RN (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
    cases HA.symm.trans HN
  · rintro ⟨shared, RA, RN⟩
    change ScopedCompute _ _ (proofErase _ assignedType) _ at RA
    change ScopedCompute _ _ (proofErase _ nativeType) _ at RN
    rw [EFA] at RA
    rw [EFN] at RN
    have HA := scoped_normal_fixed RA (fun Δ =>
      (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
    have HN := scoped_normal_fixed RN (fun Δ =>
      (normal_types (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
    cases HA.symm.trans HN
  · exact ⟨_, HasType.lam (HasType.sort (by trivial))
      ((types_equal.defeq' source_typed).weak henv)⟩
  · intro stage x y hx hy HX
    exact proofErase_native_neutral_result_propositions (erased_joint_stage_head stage)
      hC hc hw hl hdecl types_equal
      (show proofErase (context Γ) assigned = ProofShape.mkApps (.bvar 1)
        [.lam (.sort .zero) (.app (.bvar 3) (.bvar 0))] from EA) hx hy HX

end Lean4Lean.VEnv.Strengthening
