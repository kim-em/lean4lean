import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionBetaBoundary

/-! # Exact native transfer is not closed under dependent argument contexts

A constant beta cut discards a fresh Type variable and preserves all native
outputs. Putting that cut in the argument of a dependent function exposes the
fresh variable in a recovered type. The contracted application was typed below
that variable, so native descent forbids this output. The two recovered types
still beta-join. This refutes exact transfer as a general marked-context
invariant, even for the full union and a natively certified original argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params] {D : PureObservation.Definitions}

private def argumentFunctionType : VExpr :=
  .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort (.succ .zero)))

private theorem argumentFunctionType_typed (Γ : List VExpr) :
    env.HasType univs Γ argumentFunctionType
      (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ (.succ .zero))))) :=
  .forallE (.sort (by trivial)) (.forallE (.bvar .zero) (.sort (by trivial)))

private theorem sort_erasure (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) :
    proofErase Γ (.sort u) = .sort u :=
  if_neg (not_isProof_of_sort hΓ (HasType.sort hu))

private theorem argumentFunctionType_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ argumentFunctionType =
      .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort (.succ .zero))) := by
  have hΓA : OnCtx (VExpr.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hv : env.HasType univs (VExpr.sort (.succ .zero) :: Γ) (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hΓB : OnCtx (VExpr.bvar 0 :: .sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓA, _, hv⟩
  rw [show proofErase Γ argumentFunctionType = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (argumentFunctionType_typed Γ)),
    sort_erasure hΓ (by trivial)]
  rw [show proofErase _ (.forallE (.bvar 0) (.sort (.succ .zero))) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓA (HasType.forallE hv (HasType.sort (by trivial)))),
    show proofErase _ (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓA hv),
    sort_erasure hΓB (by trivial)]

/-- Exact transfer survives a typed, originally certified constant cut but
fails after placing it in a dependent argument position. Both applications are
retained and well typed at a common type. Failure holds for the full union in
any canonical-Eq Params environment; no special structure declaration is needed.
A stage-zero certificate and a beta path give a common native type afterward,
so this is an invariant obstruction, not a strengthening counterexample. -/
theorem native_output_transfer_argument_beta_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ Γ f a b T out shared,
      OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a (.sort (.succ .zero)) ∧
      env.HasType univs Γ b (.sort (.succ .zero)) ∧
      env.HasType univs Γ (.app f a) T ∧ env.HasType univs Γ (.app f b) T ∧
      NativeHeadBeta D Γ a b ∧
      ProofShape.BetaRed (proofErase Γ a) (proofErase Γ b) ∧
      NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ a) (proofErase Γ b) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app f a)) out ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f b)) out) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app f b)) shared ∧ ProofShape.BetaRed out shared := by
  let Γ₀ := [argumentFunctionType]
  let Γ := VExpr.sort (.succ .zero) :: Γ₀
  let a : VExpr := .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0)
  let rawA : ProofShape := .app (.lam (.sort (.succ .zero)) (.sort .zero)) (.bvar 0)
  let rawF : ProofShape := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort (.succ .zero)))
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨trivial, _, argumentFunctionType_typed []⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, HasType.sort (by trivial)⟩
  have hΓA : OnCtx (VExpr.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hq : env.HasType univs Γ (.bvar 0) (.sort (.succ .zero)) := .bvar .zero
  have hb : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have HE : env.IsDefEq univs Γ a (.sort .zero) (.sort (.succ .zero)) :=
    .beta (HasType.sort (by trivial)) hq
  have Ea : proofErase Γ a = rawA := by
    rw [show proofErase Γ a = .app _ _ from if_neg (not_isProof_of_sort hΓ HE.hasType.1)]
    rw [show proofErase Γ (.lam (.sort (.succ .zero)) (.sort .zero)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ
        (HasType.lam (HasType.sort (by trivial)) (HasType.sort (by trivial))))]
    rw [sort_erasure hΓ (by trivial), sort_erasure hΓA (by trivial),
      show proofErase Γ (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓ hq)]
  have Eb := sort_erasure hΓ (u := .zero) (by trivial)
  have hf₀ : env.HasType univs Γ₀ (.bvar 0) argumentFunctionType := .bvar .zero
  have hf : env.HasType univs Γ (.bvar 1) argumentFunctionType := .bvar (.succ .zero)
  have hfa : env.HasType univs Γ (.app (.bvar 1) a) (.forallE a (.sort (.succ .zero))) :=
    .app hf HE.hasType.1
  have hfb : env.HasType univs Γ (.app (.bvar 1) (.sort .zero))
      (.forallE (.sort .zero) (.sort (.succ .zero))) := .app hf hb
  have Efa : proofErase Γ (.app (.bvar 1) a) = .app (.bvar 1) rawA := by
    rw [show proofErase Γ (.app (.bvar 1) a) = .app _ _ from
      if_neg (not_isProof_function_to_sort hΓ hfa), Ea]
    rw [show proofErase Γ (.bvar 1) = .bvar 1 from if_neg
      (not_isProof_fn hΓ hf HE.hasType.1 (not_isProof_function_to_sort hΓ hfa))]
  have Efb : proofErase Γ (.app (.bvar 1) (.sort .zero)) = .app (.bvar 1) (.sort .zero) := by
    rw [show proofErase Γ (.app (.bvar 1) (.sort .zero)) = .app _ _ from
      if_neg (not_isProof_function_to_sort hΓ hfb), Eb]
    rw [show proofErase Γ (.bvar 1) = .bvar 1 from if_neg
      (not_isProof_fn hΓ hf hb (not_isProof_function_to_sort hΓ hfb))]
  have EΓ : proofEraseCtx Γ = [.sort (.succ .zero), rawF] := by
    simp only [Γ, Γ₀, rawF, proofEraseCtx,
      sort_erasure hΓ₀ (show (VLevel.succ .zero).WF univs from by trivial),
      argumentFunctionType_erasure (show OnCtx [] (env.IsType univs) from trivial)]
  have RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (.bvar 1) rawF := by
    rw [EΓ]
    exact .bvar
  have RNA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar 1) a)) (.forallE rawA (.sort (.succ .zero))) := by
    rw [Efa]
    exact .app RF
  have RNB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar 1) (.sort .zero)))
      (.forallE (.sort .zero) (.sort (.succ .zero))) := by
    rw [Efb]
    exact .app RF
  have HN : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ (.sort .zero)) := by
    intro out RN
    exact static_structure_constant_beta_native_recovery heq hs hΓ hb hq RN
  have Hno : ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.bvar 1) (.sort .zero))) (.forallE rawA (.sort (.succ .zero))) := by
    intro RN
    have ht₀ : env.HasType univs Γ₀ (.app (.bvar 0) (.sort .zero))
        (.forallE (.sort .zero) (.sort (.succ .zero))) := .app hf₀ (.sort (by trivial))
    have EW := proofErase_liftN hΓ₀ hΓ (Ctx.LiftN.one (A := .sort (.succ .zero))) ht₀
    change proofErase Γ (.app (.bvar 1) (.sort .zero)) = _ at EW
    rw [EW] at RN
    obtain ⟨C, _, EC⟩ := proofErase_scoped_typeRecovery_descend
      (erased_static_structure_eta_expansion_union_descent heq hs)
      hΓ₀ hΓ Ctx.LiftN.one ht₀ rfl RN
    obtain ⟨X, _, _, EX, _⟩ := ProofShape.liftN_forallE_inv EC
    exact ProofShape.fresh_argument_constant_not_lift X EX
  have Hcut : NativeHeadBeta D Γ a (.sort .zero) := by
    apply NativeHeadBeta.beta (HasType.sort (by trivial)) (HasType.sort (by trivial)) hq
    intro _
    rw [show proofErase Γ (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓ hq),
      sort_erasure hΓ (by trivial), EΓ]
    exact .bvar
  have Htype := IsDefEq.forallEDF HE (HasType.sort (l := .succ .zero) (by trivial))
  refine ⟨Γ, .bvar 1, a, .sort .zero, _, _, _, hΓ, HE.hasType.1, hb,
    Htype.defeq hfa, hfb, Hcut, ?_, HN, RNA, Hno, RNB, ?_⟩
  · rw [Ea, Eb]
    exact .beta
  · exact .forallE (.beta) .refl

/-- Even certified head beta cannot be closed under arbitrary argument
positions while retaining its exact native-output theorem. The witness uses
retained applications at a common ordinary type and beta-joining native types. -/
theorem native_head_beta_not_argument_closed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ Γ f a b T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.app f a) T ∧ env.HasType univs Γ (.app f b) T ∧
      NativeHeadBeta D Γ a b ∧ ¬ NativeHeadBeta D Γ (.app f a) (.app f b) := by
  obtain ⟨Γ, f, a, b, T, out, _, hΓ, _, _, hfa, hfb, Hcut, _, _, RN, Hno, _⟩ :=
    native_output_transfer_argument_beta_failure heq hs
  refine ⟨Γ, f, a, b, T, hΓ, hfa, hfb, Hcut, ?_⟩
  intro H
  exact Hno (H.recovery heq hs hΓ hfa (RN.mono (fun H => ⟨0, H⟩)))

/-- Exact native-output transfer is not a congruence for dependent argument
contexts, even when the arguments themselves are joined by certified beta.
A broader marked-context invariant must permit a change of selected output. -/
theorem native_output_transfer_not_argument_congruent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∃ Γ f a b T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.app f a) T ∧ env.HasType univs Γ (.app f b) T ∧
      NativeHeadBeta D Γ a b ∧
      NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ a) (proofErase Γ b) ∧
      ¬ NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f a)) (proofErase Γ (.app f b)) := by
  obtain ⟨Γ, f, a, b, T, out, _, hΓ, _, _, hfa, hfb, Hcut, _, HN, RN, Hno, _⟩ :=
    native_output_transfer_argument_beta_failure heq hs
  exact ⟨Γ, f, a, b, T, hΓ, hfa, hfb, Hcut, HN,
    fun H => Hno (H out (RN.mono (fun H => ⟨0, H⟩)))⟩

end Lean4Lean.VEnv.Strengthening
