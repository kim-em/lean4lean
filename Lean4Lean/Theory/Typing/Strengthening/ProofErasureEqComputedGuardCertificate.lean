import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqComputedGuardReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertificateStrengthening

/-! # Retaining comparison certificates when reading computed Eq guards

The general singleton guard is decoded beneath its generated proof major.
Exact certificate descent removes that binder and any inserted front block;
the original index computations are retained by the checking compute rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_sort_inv ProofShape.liftN_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

/-- A general five-argument Eq prefix retains a lower comparison certificate,
not just semantic equality, below the inserted block and fresh proof major. -/
theorem proofErase_singleton_eq_prop_five_certificate
    (heq : env.HasCanonicalEq)
    (hcert : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (ht : env.HasType univs Γ'
      (eqRecBeforeMajor v (.succ .zero) (.sort .zero) (P.liftN n) M m (Q.liftN n)) T)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ')
      (proofErase Γ' (eqRecBeforeMajor v (.succ .zero) (.sort .zero)
        (P.liftN n) M m (Q.liftN n))) out) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
  have hPw := hP.weakN henv W
  have hQw := hQ.weakN henv W
  have hE := HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hPw hQw
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n) :: Γ')
      (env.IsType univs) := ⟨hΓ', _, hE⟩
  have HC := proofErase_singleton_eq_prop_five_readout heq hcert.descent hhead hinert hΓ' ht H
  simp only [lift, liftN_liftN] at HC
  rw [proofErase_liftN hΓ hΓE W.cons0 hP, proofErase_liftN hΓ hΓE W.cons0 hQ] at HC
  exact (proofErase_joint_compare_certificate_descend hcert hΓ hΓE W.cons0 rfl hP hQ HC).1
    ⟨_, HasType.sort (by trivial)⟩

/-- Computed five-argument guards retain their endpoint comparison certificate
below the block. Exact lower index paths restore the original endpoints. -/
theorem proofErase_singleton_eq_prop_computed_five_certificate
    (heq : env.HasCanonicalEq)
    (hcert : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)) args)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ')
      (mkApps (.const ``Eq.rec [v,.succ .zero]) args) out) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
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
            cases RS.sort_fixed hhead
            rename_i rp rM rm rq
            have R : ScopedCompute Step (proofEraseCtx Γ')
                ((proofErase Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q)).liftN n)
                (ProofShape.eqRecBeforeMajor v (.succ .zero) (.sort .zero) rp rM rm rq) := by
              rw [eqRecBeforeMajor, proofErase_const_spine hΓ (args := [.sort .zero,P,M,m,Q]) ht hn]
              simp only [List.map_cons, List.map_nil, ProofShape.mkApps, ProofShape.liftN, ES]
              exact .app (.app (.app (.app (.app .refl RS) RP) RM) Rm) RQ
            obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_descend hcert.descent hΓ hΓ' W ht rfl R
            obtain ⟨αraw, praw, mraw, xraw, qraw, Er, Eα, EP, EM, Em, EQ⟩ :=
              ProofShape.liftN_eqRecBeforeMajor_inv Ee'
            obtain rfl := ProofShape.liftN_sort_inv Eα
            obtain ⟨α, P', M', m', Q', rfl, Eα, EP', EM', Em', EQ'⟩ := proofErase_eqRecBeforeMajor_inv Er
            obtain rfl := erase_sort_inv Eα
            obtain ⟨_, _, _, hP, _, _, hQ⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
            obtain ⟨_, _, _, hP', _, _, hQ'⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, HE.hasType.2⟩
            have RPP' : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P') := by
              rw [← EP, ← EP'] at RP
              obtain ⟨P'', _, RP'', EP''⟩ := proofErase_scoped_compute_certificate_descend
                hcert hΓ hΓ' W hP rfl RP
              have EE : proofErase Γ P'' = proofErase Γ P' := ProofShape.lift'_inj
                (ρ := .consN (.skipN .refl n) 0) (by simpa only [ProofShape.lift'_consN_skipN] using EP'')
              exact EE ▸ RP''
            have RQQ' : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ Q) (proofErase Γ Q') := by
              rw [← EQ, ← EQ'] at RQ
              obtain ⟨Q'', _, RQ'', EQ''⟩ := proofErase_scoped_compute_certificate_descend
                hcert hΓ hΓ' W hQ rfl RQ
              have EE : proofErase Γ Q'' = proofErase Γ Q' := ProofShape.lift'_inj
                (ρ := .consN (.skipN .refl n) 0) (by simpa only [ProofShape.lift'_consN_skipN] using EQ'')
              exact EE ▸ RQ''
            have Hlift := HE.hasType.2.weakN henv W
            have Hprim : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ')
                (proofErase Γ' ((eqRecBeforeMajor v (.succ .zero) (.sort .zero) P' M' m' Q').liftN n)) out := by
              rw [proofErase_liftN hΓ hΓ' W HE.hasType.2, Ee']
              exact H
            simp only [eqRecBeforeMajor, VExpr.liftN_mkApps, VExpr.liftN, List.map_cons, List.map_nil] at Hlift Hprim
            have HPQ := proofErase_singleton_eq_prop_five_certificate heq hcert hhead hinert
              hΓ hΓ' W hP' hQ' Hlift Hprim
            exact .compute RPP' RQQ' HPQ

/-- Every general singleton in a first-head witness retains the original
proposition comparison below the inserted block. Argument computations may
change both indices and the motive; no comparison transitivity is used. -/
theorem proofErase_singleton_eq_prop_computed_prefix_certificate
    (heq : env.HasCanonicalEq)
    (hcert : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      ((([VExpr.sort .zero,P,M,m,Q].map (proofErase Γ)).map (fun e : ProofShape => e.liftN n) ++ [ProofShape.proof]).take k) args)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ')
      (mkApps (.const ``Eq.rec [v,.succ .zero]) args) out) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
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
  have hk5 := proofErase_singleton_eq_prop_computed_prefix_arity heq hcert.descent hhead
    hcert.descent hhead hinert hΓ' hk ht' hn' HA' H
  subst k
  have HA5 : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ'))
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)) args := by
    simpa only [List.take_of_length_le (show
      (([.sort .zero,P,M,m,Q].map (proofErase Γ)).map (·.liftN n)).length ≤ 5 by simp)] using HA
  exact proofErase_singleton_eq_prop_computed_five_certificate heq hcert hhead hinert hΓ hΓ' W ht hn HA5 H

end Lean4Lean.VEnv.Strengthening
