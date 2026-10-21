import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqComputedGuardReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Proposition strengthening already follows from semantic sort exposure

The Eq probe has only core or general singleton first-head alternatives.
Core cannot reduce its proof-marker major, while the singleton alternative
contains a comparison of the original endpoints below the inserted context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

omit [Params] in
private theorem constant_motive_lift :
    (constantEqMotive w α a T).liftN n =
      constantEqMotive w (α.liftN n) (a.liftN n) (T.liftN n) := by
  simp [constantEqMotive, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN, VExpr.liftN'_liftN_lo]

private theorem probe_prefix_typed
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) :
    ∃ T, env.HasType univs Γ
        (eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
          (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))) (.sort .zero) Q) T ∧
      ¬ IsProof Γ
        (eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
          (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))) (.sort .zero) Q) := by
  have hα := HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .zero) (by trivial)
  have hT := HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .succ .zero) (by trivial)
  have hM := constantEqMotive_typed henv.ordered heq (by trivial) hα hP hT
  have hr := HasType.eqReflApp heq (by trivial) hα hP
  have hm := (constantEqMotive_app henv heq (by trivial) hΓ hα hP hT hP hr).symm.defeq hα
  have ht := eqRecBeforeMajor_typed heq (by trivial) (by trivial) hα hP hM hm hQ
  refine ⟨_, ht, ?_⟩
  have hEQ := HasType.eqApp heq (by trivial) hα hP hQ
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hEQ⟩
  have hq : env.HasType univs (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) P.lift Q.lift) := .bvar .zero
  have hfull := eqSortProbe_typed heq hΓE (hP.weak henv) (hQ.weak henv) hq
  have hnp := not_isProof_of_sort hΓE hfull
  have hnp' : ¬ IsProof (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
      (.app ((eqRecBeforeMajor (.succ (.succ .zero)) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero))) (.sort .zero) Q).lift) (.bvar 0)) := by
    simp only [eqRecBeforeMajor, VExpr.lift, VExpr.liftN_mkApps,
      List.map_cons, List.map_nil, constant_motive_lift, VExpr.liftN]
    exact hnp
  have hn := not_isProof_fn hΓE (ht.weak henv) hq hnp'
  exact fun hp => hn ((isProof_liftN hΓ hΓE Ctx.LiftN.one ht).2 hp)

private theorem core_computed_probe_prefix_excluded
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HA : List.Forall₂ (ScopedCompute Step Δ) ([α,a,M,m,b,.proof].take k) args) :
    ¬ ErasedIotaPrimitive D (mkApps (.const ``Eq.rec levels) args) out := by
  apply erased_iota_eqRec_no_root hreg hoff hD (constHead_mkApps _ _)
  by_cases hlen : args.length ≤ 5
  · exact .inl ⟨args, levels, rfl, hlen⟩
  have hlen' := HA.length_eq
  simp only [List.length_take, List.length_cons, List.length_nil] at hlen'
  have hk : 6 ≤ k := by omega
  rw [List.take_of_length_le (by simpa only [List.length_cons, List.length_nil] using hk)] at HA
  cases HA with | cons _ HA =>
    cases HA with | cons _ HA =>
      cases HA with | cons _ HA =>
        cases HA with | cons _ HA =>
          cases HA with | cons _ HA =>
            cases HA with | cons HP HA =>
              cases HA
              cases HP.proof_fixed hhead
              exact .inr ⟨_, rfl⟩

/-- Semantic head exposure for a replayable core/general-singleton relation
already implies proposition strengthening. Only its sort component is used.
The guard comparator may be a larger relation with its own descent law. -/
theorem ScopedSemanticHeadExposure.propositionFront_of_core_singleton
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hsourcehead : ∀ {Δ a b}, Source Δ a b → PrimitiveHead a)
    (htarget : ErasedScopedPrimitiveDescent Target)
    (htargethead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ ls args out}, ¬ Target Δ (mkApps (.const ``Eq ls) args) out)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hcover : ∀ {Δ a b}, Source Δ a b → ErasedIotaPrimitive D a b ∨
      SingletonPrimitiveWith (fun Δ => JointCompare Target Δ true) Δ a b)
    (Hheads : ScopedSemanticHeadExposure Source) : PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hPw := hP.weak henv (B := A)
  have hQw := hQ.weak henv (B := A)
  let E := eqApp (.succ .zero) (.sort .zero) P.lift Q.lift
  have hE : env.HasType univs (A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hPw hQw
  have hΓE : OnCtx (E :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hE⟩
  have W : Ctx.LiftN 2 0 Γ (E :: A :: Γ) := Ctx.LiftN.one.cons0
  have hP2 : env.HasType univs (E :: A :: Γ) (P.liftN 2) (.sort .zero) := hP.weakN henv W
  have hQ2 : env.HasType univs (E :: A :: Γ) (Q.liftN 2) (.sort .zero) := hQ.weakN henv W
  have hq : env.HasType univs (E :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 2) (Q.liftN 2)) := by
    have hq : env.HasType univs (E :: A :: Γ) (.bvar 0) E.lift := .bvar .zero
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using hq
  have HPQ2 : env.IsDefEqU univs (E :: A :: Γ) (P.liftN 2) (Q.liftN 2) := by
    obtain ⟨T, HT⟩ := HPQ
    exact ⟨T.lift, by simpa only [VExpr.lift, VExpr.liftN_liftN] using HT.weakN henv (Ctx.LiftN.one (A := E))⟩
  obtain ⟨k, changed, out, _, HA, H⟩ :=
    Hheads.eq_probe_head_occurrence heq hΓE hP2 hQ2 hq HPQ2
  rcases hcover H with Hcore | Hsingleton
  · exact (core_computed_probe_prefix_excluded hsourcehead hreg hoff hD HA Hcore).elim
  obtain ⟨T, ht, hn⟩ := probe_prefix_typed heq hΓ hP hQ
  have hM := constantEqMotive_typed henv.ordered heq (by trivial)
    (HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .zero) (by trivial)) hP
    (HasType.sort (l := .succ .zero) (by trivial))
  have EM : proofErase (E :: A :: Γ)
      (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN 2) (.sort (.succ .zero))) =
      (proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ .zero)))).liftN 2 := by
    rw [← proofErase_liftN hΓ hΓE W hM]
    congr 1
    simpa only [VExpr.liftN] using (constant_motive_lift (n := 2)
      (w := VLevel.succ .zero) (α := VExpr.sort .zero) (a := P) (T := VExpr.sort (.succ .zero))).symm
  rw [proofErase_liftN hΓ hΓE W hP, proofErase_liftN hΓ hΓE W hQ, EM] at HA
  have HS : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  apply proofErase_singleton_eq_prop_computed_prefix_descend heq hsource hsourcehead
    htarget htargethead hinert hΓ hΓE W ht hn (k := k) (H := Hsingleton)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, HS, ProofShape.liftN] using HA

/-- In particular the certified beta/substitution-stable joint relation does
not make semantic head adequacy a smaller sufficient front. For any sound
core excluding Eq and Eq.rec unfolding, its head premise implies PropFront. -/
theorem ScopedSemanticHeadExposure.beta_stable_joint_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D)) : PropositionFront := by
  refine Hheads.propositionFront_of_core_singleton heq (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_joint_union_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    hreg hoff hRec ?_
  intro Δ a b H
  rcases H with H | ⟨_, H⟩
  · exact .inl H
  · exact .inr (H.mono BetaStableFamily.base)

end Lean4Lean.VEnv.Strengthening
