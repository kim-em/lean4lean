import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidResultChange

/-! # Recovery under context changes with rigid terminal replacements

Actual context conversion permits primitive computations to move. Recovery
results may change through RigidResultChange, whose typed inversion retains
exact application domains and projection carriers. No semantic head exposure
or general carrier-domain re-synthesis is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem oracle_cons_change
    (HO : ∀ i, RigidResultChange (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, RigidResultChange (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
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
rigid terminal replacements. Displayed Pi domains stay fixed; lambda result
types may change recursively. All recovery constructors, including projection
and arbitrary computation prefixes, are handled. -/
theorem proofErase_recovery_rigid_oracles
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, RigidResultChange (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ RigidResultChange out out' := by
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
    exact ⟨_, .lam (by simpa only [proofEraseCtx, ← EAt, EA] using HR), .forallE HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨X, Y, u, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ hf EΓ Ef W
    obtain ⟨B', rfl, HBody⟩ := rigid_result_typed_pi hΓ hX HXY EX EY HB
    exact ⟨_, .app HR, HBody.inst⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep RA HA hΓ hA EΓ EA W
    obtain rfl := rigid_result_typed_sort hΓ hX HXY EX EY BA
    have EAt := proofErase_defeqCtx hΓ W hA
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have EΓA := congr (congrArg List.cons EA) EΓ
    change proofEraseCtx (A :: Γ) = _ at EΓA
    have WA := IsDefEqCtx.succ W hA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) (Γ' := A :: Γ') hΓA hB EΓA EB WA
      (by simpa only [proofEraseCtx, ← EAt, EA] using oracle_cons_change HO)
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep RB HB hΓA hB EΓA EB WA
    obtain rfl := rigid_result_typed_sort hΓA hX HXY EX EY BB
    exact ⟨_, .forallE HA (by simpa only [proofEraseCtx, ← EAt, EA] using HB), .refl⟩
  | @proj Δ m s info ls doms result j args hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ :=
      recovery_outputs_equal hstep R HR hΓ hm.hasType.2 EΓ Em W
    obtain rfl := rigid_result_typed_record hi hΓ hX HXY EX EY HB
    exact ⟨_, .proj hi HT hj hlen HR, .refl⟩
  | convert R RC ih =>
    obtain ⟨out', HR, HB⟩ := ih hΓ ht EΓ Ee W HO
    have RC' := RC
    rw [← EΓ] at RC'
    obtain ⟨out'', RS, HS⟩ := HB.compute hhead RC'
    exact ⟨out'', HR.convert (RS.defeqCtx hsubst (by trivial) W), HS⟩

/-- Pi recovery under these oracle changes retains the exact original domain.
Only its codomain may change. This is sufficient to reuse an argument guard
once that guard has been transported to the new context. -/
theorem proofErase_recovery_rigid_oracles_pi
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, RigidResultChange (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (.forallE A B)) :
    ∃ B', ScopedTypeRecovery Step (proofEraseCtx Γ') (proofErase Γ e) (.forallE A B') := by
  obtain ⟨out', HR, HB⟩ := proofErase_recovery_rigid_oracles hstep hhead hsubst R hΓ ht rfl rfl W HO
  obtain ⟨X, Y, _, hX, HXY, EX, EY⟩ := recovery_outputs_equal hstep R HR hΓ ht rfl rfl W
  obtain ⟨B', rfl, _⟩ := rigid_result_typed_pi hΓ hX HXY EX EY HB
  exact ⟨B', HR⟩

/-- Replacing one actual binder type by an equal closed rigid type preserves
every recovered Pi domain in its body. The recovered codomain is allowed to
change. The same original expression is used in the new actual context. -/
theorem proofErase_closed_binder_pi_recovery
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.const family []) (.sort u))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) e) (.forallE D B)) :
    ∃ B', ScopedTypeRecovery Step (proofEraseCtx (.const family [] :: Γ))
      (proofErase (.const family [] :: Γ) e) (.forallE D B') := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.const family [] :: Γ) := .succ (.refl hΓ) HE
  have HO : ∀ i, RigidResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.const family [] :: Γ)) i) := by
    intro i
    cases i with
    | zero =>
      change RigidResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.const family [])).liftN 1)
      rw [show proofErase Γ (.const family []) = .const family [] from
        if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
      exact .closed hr
    | succ i => exact .refl
  obtain ⟨B', HR⟩ := proofErase_recovery_rigid_oracles_pi hstep hhead hsubst hΓA ht W HO R
  rw [proofErase_defeqCtx hΓA W ht] at HR
  exact ⟨B', HR⟩

/-- Certified primitives discharge all recovery-transport premises for a
closed rigid binder replacement. No lower-stage beta hypothesis or general
semantic head-exposure principle is added. -/
theorem proofErase_certified_closed_binder_pi_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.const family []) (.sort u))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) (.forallE domain body)) :
    ∃ body', ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx (.const family [] :: Γ))
      (proofErase (.const family [] :: Γ) e) (.forallE domain body') :=
  proofErase_closed_binder_pi_recovery (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hr hΓ HE ht R

end Lean4Lean.VEnv.Strengthening
