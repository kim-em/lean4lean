import Lean4Lean.Theory.Typing.Strengthening.ProofErasureVariableEtaDiamond

/-! # Native eta diamonds at named constant sources

Both native recoveries start with the same registered declaration type.
Typed replay reifies that shared starting type, and common-core guard paths
join the selected Pi outputs. No unfolding or reduction of the constant's
body is needed to compare the two eta annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Recovery of a constant consists of its registered type followed by
computation. The declaration and universe side conditions are retained. -/
theorem ProofShape.ScopedTypeRecovery.const_origin
    (R : ScopedTypeRecovery Step Δ (.const c ls) out) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF univs) ∧ ls.length = ci.uvars ∧
      ScopedCompute Step Δ (proofErase [] (ci.type.instL ls)) out := by
  generalize E : ProofShape.const c ls = e at R
  induction R with
  | const hc hw hl => cases E; exact ⟨_, hc, hw, hl, .refl⟩
  | convert _ RC ih =>
    obtain ⟨ci, hc, hw, hl, R⟩ := ih E
    exact ⟨ci, hc, hw, hl, R.trans RC⟩
  | bvar | sort | lam | app | forallE | proj => cases E

/-- Constant recovery has a common declared type, hence independent guard
computations produce core-joined outputs. Typed replay supplies the shared
actual type in the ambient context, without changing declaration syntax. -/
theorem proofErase_constant_native_core_join
    (hrec : ErasedScopedPrimitiveDescent Left) (hc : TypedCoreConfluence Core)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ (.const c ls) T)
    (hn : ¬ IsProof Γ (.const c ls))
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (.const c ls) A)
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (.const c ls) B) : ComputeJoin Core A B := by
  obtain ⟨ci, hc₀, hw, hl, RA⟩ := RL.const_origin
  obtain ⟨ci', hc₁, _, _, RB⟩ := RR.const_origin
  have Eci : ci = ci' := Option.some.inj (hc₀.symm.trans hc₁)
  subst ci'
  have Ef : proofErase Γ (.const c ls) = .const c ls := if_neg hn
  have RN : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ (.const c ls))
      (proofErase [] (ci.type.instL ls)) := Ef ▸ ScopedTypeRecovery.const hc₀ hw hl
  obtain ⟨C, hfC, EC⟩ := proofErase_scoped_typeRecovery_replay hrec hΓ hf RN
  obtain ⟨_, hC⟩ := hfC.isType henv hΓ
  rw [← EC] at RA RB
  exact (hlj hΓ hC RA).symm.trans_typed hc hΓ hC (hrj hΓ hC RB)

/-- Independent native eta expansions of a retained named constant meet by
core reductions of the annotations. Their native relations may be unrelated
and may use non-normalizing guard paths, provided those paths are core-joinable. -/
theorem proofErase_constant_native_eta_diamond
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hc : TypedCoreConfluence Core) (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ (.const c ls) T)
    (hn : ¬ IsProof Γ (.const c ls))
    (RL : NativeEtaExpansion Left (proofEraseCtx Γ) (.const c ls) a)
    (RR : NativeEtaExpansion Right (proofEraseCtx Γ) (.const c ls) b) : ComputeJoin Core a b := by
  have Ef : proofErase Γ (.const c ls) = .const c ls := if_neg hn
  cases RL with
  | intro RN SN =>
    cases RR with
    | intro RN' SN' =>
      have HJ := proofErase_constant_native_core_join hld hc hlj hrj hΓ hf hn RN RN'
      simpa only [Ef] using proofErase_native_eta_type_diamond hld hrd hpi hΓ hf
        (Ef ▸ RN) (Ef ▸ RN') SN SN' HJ

end Lean4Lean.VEnv.Strengthening
