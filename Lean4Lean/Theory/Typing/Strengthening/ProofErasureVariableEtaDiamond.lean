import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaDiamond
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaEtaStages

/-! # Neutral variable eta peaks with independent native guards

Both type recoveries of a variable compute from the same context lookup.
Core-joinable guard paths therefore have joined outputs, although the variable
itself cannot join either eta expansion in the core. The long/long diamond
does not require native-image coverage or an assigned-type path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Two native types recovered from the same actual variable have a common
core reduct if their guard paths are core-joinable. The common typed middle
is the variable's actual lookup type, not an arbitrary assigned annotation. -/
theorem proofErase_variable_native_core_join
    (hc : TypedCoreConfluence Core)
    (hleft : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hright : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ (.bvar i) T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (.bvar i) A)
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (.bvar i) B) : ComputeJoin Core A B := by
  obtain ⟨C, hl⟩ := hx.bvar_inv henv hΓ
  have hv : env.HasType univs Γ (.bvar i) C := .bvar hl
  obtain ⟨u, hC⟩ := hv.isType henv hΓ
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ C := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl]
  have HL := RL.bvar_compute
  have HR := RR.bvar_compute
  rw [EO] at HL HR
  exact (hleft hΓ hC HL).symm.trans_typed hc hΓ hC (hright hΓ hC HR)

/-- Independently selected eta expansions of a retained variable meet by
core computation of their domains alone. The two source guard relations can
differ, and no native certificate for an arbitrary substitution image occurs. -/
theorem proofErase_variable_native_eta_diamond
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hc : TypedCoreConfluence Core) (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ (.bvar i) T)
    (hn : ¬ IsProof Γ (.bvar i))
    (RL : NativeEtaExpansion Left (proofEraseCtx Γ) (.bvar i) a)
    (RR : NativeEtaExpansion Right (proofEraseCtx Γ) (.bvar i) b) : ComputeJoin Core a b := by
  have Ex : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  cases RL with
  | intro RN SN =>
    cases RR with
    | intro RN' SN' =>
      have HJ := proofErase_variable_native_core_join hc hlj hrj hΓ hx RN RN'
      simpa only [Ex] using proofErase_native_eta_type_diamond hld hrd hpi hΓ hx
        (Ex ▸ RN) (Ex ▸ RN') SN SN' HJ

/-- Native eta of a variable has a long/long diamond when each guard uses
arbitrarily nested literal-lambda eta. Base identity-guard relations may be
unrelated, provided each descends. Neutral eta itself is now present at the
two roots; it is not silently inserted into the inner core-joinable stages. -/
theorem proofErase_variable_lambda_eta_guard_diamond
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ (.bvar i) T)
    (hn : ¬ IsProof Γ (.bvar i))
    (RL : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery) (proofEraseCtx Γ) (.bvar i) a)
    (RR : NativeEtaExpansion (ErasedLambdaEtaUnion D Recovery') (proofEraseCtx Γ) (.bvar i) b) :
    ComputeJoin (ErasedLevelCore D) a b :=
  proofErase_variable_native_eta_diamond (erased_lambda_eta_union_descent hs hr)
    (erased_lambda_eta_union_descent hs hr') (proofErase_level_core_confluent hs hlevels hcon hc)
    (fun H => erased_level_core_no_pi H)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr hΓ ht R)
    (fun hΓ ht R => proofErase_lambda_eta_union_join hs hlevels hcon hc hr' hΓ ht R)
    hΓ hx hn RL RR

end Lean4Lean.VEnv.Strengthening
