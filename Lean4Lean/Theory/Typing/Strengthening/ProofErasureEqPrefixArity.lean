import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEarlyGuard

/-! # The only usable general singleton prefix of the Prop-carrier Eq probe

Valid code bounds the arity by five. At a typed prefix of the probe the
shorter guards are impossible, so a general singleton step must supply the
requested endpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- Generation of valid Eq.rec singleton code stops before the proof major.
This bound is independent of the raw arguments, guard, and source typing. -/
theorem ProofShape.SingletonPrimitiveWith.eq_rec_arity_le
    (heq : env.HasCanonicalEq)
    (H : SingletonPrimitiveWith Cmp Δ (mkApps (.const ``Eq.rec ls) args) out) :
    args.length ≤ 5 := by
  generalize Es : mkApps (.const ``Eq.rec ls) args = source at H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨hn, _, hargs⟩ := ProofShape.const_spine_inj Es
    obtain ⟨seed, program, hs, hg⟩ := V.generation
    have hb := (RecursorData.singletonUnfolding_spec hg).1
    have hoff := (V.registered.eqRec_target heq hn.symm).2.1
    rw [hoff, hs, ← ha, ← hargs] at hb
    exact hb

/-- A general singleton primitive on any initial segment of a typed
Prop-carrier five-argument Eq.rec prefix must use all five arguments. -/
theorem proofErase_singleton_eq_prop_prefix_arity
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hk : k ≤ 5)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (H : SingletonPrimitiveWith (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k)) out) : k = 5 := by
  by_cases he : k = 5
  · exact he
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  obtain ⟨_, _, _, hP, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hpref : VExpr.WF env univs Γ
      (VExpr.mkApps (.const ``Eq.rec [v,.succ .zero]) ([.sort .zero,P,M,m,Q].take k)) := by
    apply VExpr.WF.of_mkApps henv.orderedStrong hΓ (args := [.sort .zero,P,M,m,Q].drop k)
    simpa only [← VExpr.mkApps_append, List.take_append_drop] using (show VExpr.WF env univs Γ
      (VExpr.mkApps (.const ``Eq.rec [v,.succ .zero]) [.sort .zero,P,M,m,Q]) from ⟨_, ht⟩)
  generalize Es : mkApps (.const ``Eq.rec [v,.succ .zero])
    (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k) = source at H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨hn, hl, hargs⟩ := ProofShape.const_spine_inj Es
    rw [← hargs] at ha hcalc HG
    rw [hn, hl] at hpref
    rcases hk' with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (V.no_eq_zero_guard heq hstep hhead hinert hn.symm hl.symm hΓ
        (by simpa using ha) hpref hcalc HG)
    · exact False.elim (V.no_eq_prop_one_guard heq hstep hhead hinert hn.symm hl.symm hΓ
        (by simpa using ha) hpref hcalc HG)
    · exact False.elim (V.no_eq_prop_early_guard (rest := []) heq hstep hhead hinert hn.symm hl.symm hΓ hP
        (by simp) (by simpa using ha) hpref hcalc HG)
    · exact False.elim (V.no_eq_prop_early_guard (rest := [M]) heq hstep hhead hinert hn.symm hl.symm hΓ hP
        (by simp) (by simpa using ha) hpref hcalc HG)
    · exact False.elim (V.no_eq_prop_early_guard (rest := [M,m]) heq hstep hhead hinert hn.symm hl.symm hΓ hP
        (by simp) (by simpa using ha) hpref hcalc HG)

end Lean4Lean.VEnv.Strengthening
