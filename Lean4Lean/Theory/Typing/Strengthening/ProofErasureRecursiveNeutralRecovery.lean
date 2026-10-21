import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralTypeChange

/-! # Recovery with recursive changes to neutral oracle types

Native recovered domains may themselves change. Source and target recovery
replay provide actual equal types for the computation simulation, avoiding
an assumed global output-congruence theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private NeutralTypeChange.sort NeutralTypeChange.const_spine
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralTypeChange

private theorem oracle_cons_recursive
    (HO : ∀ i, NeutralTypeChange k (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, NeutralTypeChange (k + 1) (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (HO i).liftN (by omega)

variable [Params]

/-- Typed recovery transports between actually convertible contexts when
their oracle types differ recursively at protected neutral leaves. The new
output is related by NeutralTypeChange, including possible domain changes.
Conversion uses the equality obtained by replaying both recovery certificates;
it does not assume comparison or recovery completeness. -/
theorem proofErase_recovery_recursive_neutral
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, NeutralTypeChange k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ NeutralTypeChange k out out' := by
  induction R generalizing Γ Γ' e T k with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨out', HR, HB⟩ := ih (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_recursive HO)
    exact ⟨_, .lam (by simpa only [proofEraseCtx, ← EAt, EA] using HR), .forallE .refl HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨A', B', rfl, _, HC⟩ := HB.forallE_inv
    exact ⟨_, .app HR, HC.inst (by omega)⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    obtain rfl := NeutralTypeChange.sort BA
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_recursive HO)
    obtain rfl := NeutralTypeChange.sort BB
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain rfl := NeutralTypeChange.const_spine HB
    exact ⟨_, .proj hi HT hj hlen HR, .refl⟩
  | @convert Δ₀ e₀ A₀ B₀ R RC ih =>
    obtain ⟨out', HR, HB⟩ := ih hΓ ht EΓ Ee W HO
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    have hΓ' := (W.symm henv.ordered).isType
    have ht' := ht.defeqDFC henv W
    have Ee' := (proofErase_defeqCtx hΓ W ht).symm.trans Ee
    obtain ⟨B, heB', EB'⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ' ht'
      (by simpa only [Ee'] using HR)
    have heB := heB'.defeqDFC henv (W.symm henv.ordered)
    have EB := (proofErase_defeqCtx hΓ W (heB.isType henv hΓ).choose_spec).trans EB'
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    have HAB := (heA.uniqU henv hΓ heB).of_l henv hΓ hA
    obtain ⟨out'', RS, HS⟩ := HB.compute hstep hhead hsubst hΓ HAB EA EB
      (by simpa only [EΓ] using RC)
    have RS' := RS.defeqCtx hsubst (by trivial) W
    exact ⟨out'', HR.convert RS', HS⟩

end Lean4Lean.VEnv.Strengthening
