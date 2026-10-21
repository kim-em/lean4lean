import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixGuardReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqComputedPrefixArity

/-! # Five-argument Eq guard readout after argument computation

The first head primitive may see computed proposition indices and a computed
motive. Typed descent reconstructs a whole lower prefix, while the separately
recorded argument paths align its indices with the original propositions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_sort_inv ProofShape.liftN_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

/-- Arbitrary component computations before a five-argument general Eq
singleton primitive still prove equality of the original propositions below
the inserted front block. Source computation and guard comparison may use
different primitive relations; only their respective descent laws are needed. -/
theorem proofErase_singleton_eq_prop_computed_five_descend
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourcehead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargethead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Target Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)) args)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ')
      (mkApps (.const ``Eq.rec [v,.succ .zero]) args) out) :
    env.IsDefEqU univs Γ P Q := by
  simp only [List.map_cons, List.map_nil] at HA
  cases HA with | cons RS HA =>
    cases HA with | cons RP HA =>
      cases HA with | cons RM HA =>
        cases HA with | cons Rm HA =>
          cases HA with | cons RQ HA =>
            cases HA
            have ES : proofErase Γ (.sort .zero) = .sort .zero :=
              if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
            simp only [ES, ProofShape.liftN] at RS
            cases RS.sort_fixed hsourcehead
            rename_i rp rM rm rq
            have R : ScopedCompute Source (proofEraseCtx Γ')
                ((proofErase Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q)).liftN n)
                (ProofShape.eqRecBeforeMajor v (.succ .zero) (.sort .zero) rp rM rm rq) := by
              rw [eqRecBeforeMajor, proofErase_const_spine hΓ (args := [.sort .zero,P,M,m,Q]) ht hn]
              simp only [List.map_cons, List.map_nil, ProofShape.mkApps, ProofShape.liftN, ES]
              exact .app (.app (.app (.app (.app .refl RS) RP) RM) Rm) RQ
            obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ' W ht rfl R
            obtain ⟨αraw, praw, mraw, xraw, qraw, Er, Eα, EP, EM, Em, EQ⟩ :=
              ProofShape.liftN_eqRecBeforeMajor_inv Ee'
            obtain rfl := ProofShape.liftN_sort_inv Eα
            obtain ⟨α, P', M', m', Q', rfl, Eα, EP', EM', Em', EQ'⟩ := proofErase_eqRecBeforeMajor_inv Er
            obtain rfl := erase_sort_inv Eα
            obtain ⟨_, _, _, hP, _, _, hQ⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
            obtain ⟨_, _, _, hP', _, _, hQ'⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, HE.hasType.2⟩
            have HPP' : env.IsDefEqU univs Γ P P' := by
              rw [← EP, ← EP'] at RP
              exact (proofErase_joint_compare_descend (mode := true) hsource hΓ hΓ' W rfl hP hP'
                (JointCheck.compute RP .refl (JointCheck.leaf .refl))).1 ⟨_, HasType.sort (by trivial)⟩
            have HQQ' : env.IsDefEqU univs Γ Q Q' := by
              rw [← EQ, ← EQ'] at RQ
              exact (proofErase_joint_compare_descend (mode := true) hsource hΓ hΓ' W rfl hQ hQ'
                (JointCheck.compute RQ .refl (JointCheck.leaf .refl))).1 ⟨_, HasType.sort (by trivial)⟩
            have Hlift := HE.hasType.2.weakN henv W
            have Hprim : SingletonPrimitiveWith (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ')
                (proofErase Γ' ((eqRecBeforeMajor v (.succ .zero) (.sort .zero) P' M' m' Q').liftN n)) out := by
              rw [proofErase_liftN hΓ hΓ' W HE.hasType.2, Ee']
              exact H
            simp only [eqRecBeforeMajor, VExpr.liftN_mkApps, VExpr.liftN, List.map_cons, List.map_nil] at Hlift Hprim
            have HPQ := proofErase_singleton_eq_prop_five_descend heq htarget htargethead hinert
              hΓ hΓ' W hP' hQ' Hlift Hprim
            exact (HPP'.trans henv hΓ HPQ).trans henv hΓ HQQ'.symm

/-- Every general singleton alternative in the first-head witness of a
lifted Prop-carrier Eq.rec probe forces equality of the original propositions.
The witness may choose any prefix of the six raw arguments, including the
proof marker; valid code and guard exclusion force exactly five arguments. -/
theorem proofErase_singleton_eq_prop_computed_prefix_descend
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourcehead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargethead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Target Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((([VExpr.sort .zero,P,M,m,Q].map (proofErase Γ)).map (fun e : ProofShape => e.liftN n) ++ [ProofShape.proof]).take k) args)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ')
      (mkApps (.const ``Eq.rec [v,.succ .zero]) args) out) :
    env.IsDefEqU univs Γ P Q := by
  have hb := H.eq_rec_arity_le heq
  have hl := HA.length_eq
  simp only [List.length_take, List.length_append, List.length_map,
    List.length_cons, List.length_nil] at hl
  have hk : k ≤ 5 := by omega
  rw [List.take_append_of_le_length (by simpa only [List.length_map,
    List.length_cons, List.length_nil] using hk)] at HA
  have ht' := ht.weakN henv W
  have hn' : ¬ IsProof Γ' ((eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q).liftN n) :=
    fun hp => hn ((isProof_liftN hΓ hΓ' W ht).1 hp)
  have hargs := (mkApps_arguments_wf henv hΓ (show VExpr.WF env univs Γ
    (VExpr.mkApps (.const ``Eq.rec [v,.succ .zero]) [.sort .zero,P,M,m,Q]) from ⟨_, ht⟩)).2
  have Eargs : (([.sort .zero,P,M,m,Q].map (·.liftN n)).map (proofErase Γ')) =
      ([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨A, hA⟩ := hargs a ha
    exact proofErase_liftN hΓ hΓ' W hA
  simp only [eqRecBeforeMajor, VExpr.liftN_mkApps, List.map_cons, List.map_nil, VExpr.liftN] at ht' hn'
  have HA' := HA
  rw [← Eargs] at HA'
  simp only [List.map_cons, List.map_nil, VExpr.liftN] at HA'
  have hk5 := proofErase_singleton_eq_prop_computed_prefix_arity heq hsource hsourcehead
    htarget htargethead hinert hΓ' hk ht' hn' HA' H
  subst k
  have HA5 : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)) args := by
    simpa only [List.take_of_length_le (show
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)).length ≤ 5 by simp)] using HA
  exact proofErase_singleton_eq_prop_computed_five_descend heq hsource hsourcehead
    htarget htargethead hinert hΓ hΓ' W ht hn HA5 H

end Lean4Lean.VEnv.Strengthening
