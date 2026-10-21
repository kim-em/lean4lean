import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxTypeChange

/-! # Recovery with recursive Pi and Box oracle changes

Native recovered domains and record parameters may themselves change. Source and target recovery
replay provide actual equal types for the computation simulation, avoiding
an assumed global output-congruence theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private BoxTypeChange.sort
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxTypeChange

open private BoxCarrierAlignment.projection_recipe
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment

private theorem oracle_cons_box
    (HO : ∀ i, BoxTypeChange family k (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, BoxTypeChange family (k + 1) (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (HO i).liftN (by omega)

variable [Params]

/-- Typed recovery transports between actually convertible contexts when
their oracle types differ recursively through Pi and Box structure. The new
output is related by BoxTypeChange, including changes to domains and projected field types.
Conversion uses the equality obtained by replaying both recovery certificates;
it does not assume comparison or recovery completeness. -/
theorem proofErase_recovery_recursive_box
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections family infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hcBox : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, BoxTypeChange family k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ BoxTypeChange family k out out' := by
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
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_box HO)
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
    obtain rfl := BoxTypeChange.sort BA
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_box HO)
    obtain rfl := BoxTypeChange.sort BB
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), .refl⟩
  | @proj Δ m s info ls doms result j args hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    rcases HB.const_spine with E | ⟨a, b, rfl, rfl, rfl, rfl, HP⟩
    · rw [E] at HR
      exact ⟨_, .proj hi HT hj hlen HR, .refl⟩
    · cases henv.ordered.projections_unique hi hiBox
      have hj0 : j = 0 := by have := HT.numFields; omega
      subst j
      exact ⟨_, .proj (args := [b]) hiBox HT hj (by simpa using hlen) HR, by
        simpa only [BoxCarrierAlignment.projection_recipe hpBox hfBox hshapeBox HT] using HP⟩
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
    obtain ⟨out'', RS, HS⟩ := HB.compute hstep hhead hsubst hiBox hcBox hinert hΓ HAB EA EB
      (by simpa only [EΓ] using RC)
    have RS' := RS.defeqCtx hsubst (by trivial) W
    exact ⟨out'', HR.convert RS', HS⟩

end Lean4Lean.VEnv.Strengthening
