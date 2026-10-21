import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangeLaws

/-! # Recovery transport from local type-relation laws

All recovery constructors are handled, including dependent projection recipes
and computation of the recovered type. Actual typing replay supplies the
equality needed by the computation law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem oracle_cons_related (L : TypeChangeLaws Step Rel)
    (HO : ∀ i, Rel k (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, Rel (k + 1) (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact L.refl
  | succ i => exact L.shift (HO i)

/-- Local type-relation laws transport typed recovery through convertible
contexts with related oracles. The output may change within the relation.
This theorem supplies recovery transport; it is not a premise of the laws. -/
theorem proofErase_recovery_type_change
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (L : TypeChangeLaws Step Rel)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, Rel k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ Rel k out out' := by
  induction R generalizing Γ Γ' e T k with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, L.refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, L.refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨out', HR, HB⟩ := ih (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_related L HO)
    exact ⟨_, .lam (by simpa only [proofEraseCtx, ← EAt, EA] using HR), L.pi L.refl HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨A', B', rfl, _, HC⟩ := L.pi_inv HB
    exact ⟨_, .app HR, L.inst HC⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    obtain rfl := L.sort_inv BA
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_related L HO)
    obtain rfl := L.sort_inv BB
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), L.refl⟩
  | @proj Δ m s info ls doms result j args hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain ⟨args', Eout, hlen'⟩ := L.record hi HB
    rw [Eout] at HR HB
    exact ⟨_, .proj hi HT hj (hlen'.trans hlen) HR, L.field hi HT HB j hj _⟩
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
    obtain ⟨out'', RS, HS⟩ := L.compute HB hΓ HAB EA EB
      (by simpa only [EΓ] using RC)
    have RS' := RS.defeqCtx hsubst (by trivial) W
    exact ⟨out'', HR.convert RS', HS⟩

end Lean4Lean.VEnv.Strengthening
