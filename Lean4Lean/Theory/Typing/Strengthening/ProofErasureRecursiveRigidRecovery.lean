import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeChange

/-! # Recovery under recursively changed rigid type oracles

Actual context conversion permits primitive computations to move. Recovery
results may change through RigidTypeChange, whose typed inversion retains
related application domains and exact projection carriers. No semantic head exposure
or general carrier-domain re-synthesis is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem oracle_cons_change
    (HO : ∀ i, RigidTypeChange (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, RigidTypeChange (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (HO i).liftN

private theorem recovery_outputs_equal
    (hstep : ErasedScopedPrimitiveDescent Step)
    (R : ScopedTypeRecovery Step Δ source out)
    (R' : ScopedTypeRecovery Step (proofEraseCtx Γ') source out')
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ') :
    ∃ X Y u, env.HasType univs Γ X (.sort u) ∧ env.IsDefEqU univs Γ X Y ∧
      proofErase Γ X = out ∧ proofErase Γ Y = out' := by
  obtain ⟨X, heX, EX⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
    (by simpa only [EΓ, Ee] using R)
  have hΓ' := (W.symm henv.ordered).isType
  have ht' := ht.defeqDFC henv W
  have Ee' := (proofErase_defeqCtx hΓ W ht).symm.trans Ee
  obtain ⟨Y, heY', EY'⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ' ht'
    (by simpa only [Ee'] using R')
  have heY := heY'.defeqDFC henv (W.symm henv.ordered)
  obtain ⟨u, hX⟩ := heX.isType henv hΓ
  have EY := (proofErase_defeqCtx hΓ W (heY.isType henv hΓ).choose_spec).trans EY'
  exact ⟨X, Y, u, hX, heX.uniqU henv hΓ heY, EX, EY⟩

/-- Typed recovery survives actual context conversion whose oracles undergo
rigid terminal replacements. Both recovered Pi domains and result types
may change recursively. All recovery constructors, including projection
and arbitrary computation prefixes, are handled. -/
theorem proofErase_recovery_recursive_rigid
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, RigidTypeChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ RigidTypeChange out out' := by
  induction R generalizing Γ Γ' e T with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have EAt := proofErase_defeqCtx hΓ W hA
    obtain ⟨out', HR, HB⟩ := ih (Γ := A :: Γ) (Γ' := A :: Γ') ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (.succ W hA)
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_change HO)
    exact ⟨_, .lam (by simpa only [proofEraseCtx, ← EAt, EA] using HR), .forallE .refl HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨X, Y, u, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ hf EΓ Ef W
    obtain ⟨A', B', rfl, _, HBody⟩ := rigid_type_typed_pi hΓ hX HXY EX EY HB
    exact ⟨_, .app HR, HBody.inst⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep RA HA hΓ hA EΓ EA W
    obtain rfl := rigid_type_typed_sort hΓ hX HXY EX EY BA
    have EAt := proofErase_defeqCtx hΓ W hA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have EΓA := congr (congrArg List.cons EA) EΓ
    change proofEraseCtx (A :: Γ) = _ at EΓA
    have WA := IsDefEqCtx.succ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') hΓA hB EΓA EB WA
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_change HO)
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep RB HB hΓA hB EΓA EB WA
    obtain rfl := rigid_type_typed_sort hΓA hX HXY EX EY BB
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), .refl⟩
  | @proj Δ m s info ls doms result j args hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ :=
      recovery_outputs_equal hstep R HR hΓ hm.hasType.2 EΓ Em W
    obtain rfl := rigid_type_typed_record hi hΓ hX HXY EX EY HB
    exact ⟨_, .proj hi HT hj hlen HR, .refl⟩
  | convert R RC ih =>
    obtain ⟨out', HR, HB⟩ := ih hΓ ht EΓ Ee W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ ht EΓ Ee W
    obtain ⟨out'', RS, HS⟩ := HB.compute hstep hhead hsubst hΓ (HXY.of_l henv hΓ hX) EX EY
      (by simpa only [EΓ] using RC)
    exact ⟨out'', HR.convert (RS.defeqCtx hsubst (by trivial) W), HS⟩

end Lean4Lean.VEnv.Strengthening
