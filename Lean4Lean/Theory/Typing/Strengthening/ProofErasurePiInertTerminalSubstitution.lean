import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUnusedBodyComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta

/-! # Terminal-image substitution retaining stage-zero Pi-inert certificates

The outer source-head restriction survives substitution. Native recovery may
instead follow a terminal path; its selected lambda domain is exposed using
Pi-inert component paths. The complete recursive checker stays at stage zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Stage-zero primitive substitution preserves the Pi-inert source-head test.
No native-image premise is needed for the computation roots themselves. -/
theorem pi_inert_zero_primitive_substitution :
    ErasedPrimitiveSubstitutionTo (PiInertStage D 0) (PiInertStage D 0) := by
  intro Γ Γ₀ σ τ e T out hΓ₀ W ES ht H
  rw [proofErase_subst_with hΓ₀ W ht ES]
  obtain ⟨HR, HH⟩ := H
  have HH' : PrimitiveHead ((proofErase Γ e).subst τ) ∨
      ∃ u, (proofErase Γ e).subst τ = .sort u := by
    rcases HH with HH | ⟨u, HH⟩
    · exact .inl HH.subst
    · exact .inr ⟨u, by rw [HH]; rfl⟩
  apply ScopedCompute.base
  refine ⟨?_, HH'⟩
  rcases HR with HR | HR
  · exact .inl (erased_level_core_subst HR)
  · exact .inr (HR.subst_typed W.wf ht rfl rfl (ContextSubstitution.of_typed hΓ₀ W ES))

/-- With no Pi-root primitive and context-independent stage zero, both Pi
components retain exact paths in the original contexts. -/
theorem ProofShape.ScopedCompute.pi_inert_zero_pi_parts
    (R : ScopedCompute (PiInertStage D 0) Δ (.forallE A B) out) :
    ∃ X Y, out = .forallE X Y ∧ ScopedCompute (PiInertStage D 0) Δ A X ∧
      ScopedCompute (PiInertStage D 0) (A :: Δ) B Y := by
  generalize E : ProofShape.forallE A B = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing A B with
  | refl => exact ⟨A, B, E.symm, .refl, .refl⟩
  | base HR => exact (pi_inert_stage_no_pi (E ▸ HR)).elim
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨X, Y, EX, RA, RB⟩ := ih₁ E
    obtain ⟨X', Y', EY, RA', RB'⟩ := ih₂ EX.symm
    exact ⟨X', Y', EY, RA.trans RA', RB.trans (RB'.recontext_independent (fun H => H))⟩
  | forallE RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | beta | app | proj | lam => cases E

/-- Actual representatives accompany stage-zero Pi component readout; the
codomain path remains in the initial annotation context. -/
theorem proofErase_pi_inert_zero_pi_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.forallE X Y)) :
    ∃ A' B', env.IsDefEq univs Γ A A' (.sort u) ∧
      env.HasType univs (A' :: Γ) B' (.sort v) ∧
      proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
      ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ A) X ∧
      ScopedCompute (PiInertStage D 0) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y := by
  obtain ⟨_, _, E, RA, RB⟩ := R.pi_inert_zero_pi_parts
  cases E
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) := ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize @hd hΓ hA rfl rfl RA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨B', HB, EB⟩ := proofErase_scoped_compute_realize @hd hΓA hB rfl rfl RB
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (A' :: Γ) := .succ .zero HA
  exact ⟨A', B', HA, HB.hasType.2.defeqDFC henv HC, EA,
    (proofErase_defeqCtx hΓA HC HB.hasType.2).symm.trans EB, RA, RB⟩

/-- A recovery path ending in an actual terminal image, with the exact
assigned type retained at every node. Conversion carries both ordinary type
equality and a stage-zero forward computation. This is not universal coverage
of native recovery or of arbitrary substitution images. -/
inductive PiInertZeroTerminalPath (D : PureObservation.Definitions) :
    List VExpr → VExpr → VExpr → Nat → Prop where
  | terminal : TerminalImage Γ e → env.HasType univs Γ e T → PiInertZeroTerminalPath D Γ e T 0
  | lam : env.HasType univs Γ A (.sort u) → PiInertZeroTerminalPath D (A :: Γ) b B n →
      PiInertZeroTerminalPath D Γ (.lam A b) (.forallE A B) (n + 1)
  | app : PiInertZeroTerminalPath D Γ f (.forallE A B) n → env.HasType univs Γ a A →
      PiInertZeroTerminalPath D Γ (.app f a) (B.inst a) (n + 1)
  | convert : PiInertZeroTerminalPath D Γ e T n → env.IsDefEq univs Γ T U (.sort u) →
      ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
        (proofErase Γ T) (proofErase Γ U) → PiInertZeroTerminalPath D Γ e U (n + 1)

/-- Each path includes an actual typing at its selected output. -/
theorem PiInertZeroTerminalPath.hasType (H : PiInertZeroTerminalPath D Γ e T n) :
    env.HasType univs Γ e T := by
  induction H with
  | terminal _ ht => exact ht
  | lam hA _ ih => exact .lam hA ih
  | app _ ha ih => exact .app ih ha
  | convert _ HE _ ih => exact HE.defeq ih

/-- Ordinary typed substitution preserves the path rank and its exact actual
assigned type, including conversion histories through constant expansions. -/
theorem PiInertZeroTerminalPath.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertZeroTerminalPath D Γ e T n)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) :
    PiInertZeroTerminalPath D Γ₀ (e.subst σ) (T.subst σ) n := by
  induction H generalizing Γ₀ σ τ with
  | terminal HT ht => exact .terminal (HT.subst hΓ₀ W) (ht.subst henv.orderedStrong W hΓ₀)
  | lam hA H ih =>
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    exact .lam hA' (ih ⟨hΓ₀, _, hA'⟩ (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA))
  | app H ha ih =>
    simpa only [VExpr.subst, VExpr.subst_inst] using
      PiInertZeroTerminalPath.app (ih hΓ₀ W ES) (ha.subst henv.orderedStrong W hΓ₀)
  | convert H HE R ih =>
    apply PiInertZeroTerminalPath.convert (ih hΓ₀ W ES) (HE.subst henv.orderedStrong W hΓ₀)
    have RR := proofErase_scoped_compute_subst_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
      pi_inert_zero_primitive_substitution hΓ₀ W ES HE.hasType.1 R
    simpa only [proofErase_subst_with hΓ₀ W HE.hasType.2 ES] using RR

/-- A typed terminal path either remains terminal or beta-exposes a lambda
whose body has a strictly smaller path. The exact selected type is reached
from that lambda's written Pi at stage zero. This handles applications by
instantiating a smaller body path and its retained codomain computation. -/
theorem PiInertZeroTerminalPath.expose
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertZeroTerminalPath D Γ e T n) (hΓ : OnCtx Γ (env.IsType univs)) :
    TerminalImage Γ e ∨ ∃ A b B m u, m < n ∧ env.HasType univs Γ A (.sort u) ∧
      PiInertZeroTerminalPath D (A :: Γ) b B m ∧ VExpr.BetaRed e (.lam A b) ∧
      ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
        (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ T) := by
  induction n using Nat.strongRecOn generalizing Γ e T with
  | ind n ih =>
    cases H with
    | terminal HT _ => exact .inl HT
    | lam hA HB =>
      apply Or.inr
      refine ⟨_, _, _, _, _, by omega, hA, HB, .refl, ?_⟩
      have hPi := (HasType.lam hA HB.hasType).isType henv hΓ |>.choose_spec
      rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
      exact .refl
    | @convert Γ e T k U u H HE R =>
      rcases ih k (by omega) H hΓ with HT | ⟨A, b, B, m, v, hm, hA, HB, RB, RP⟩
      · exact .inl HT
      · exact .inr ⟨A, b, B, m, v, by omega, hA, HB, RB, RP.trans R⟩
    | @app Γ f C E k a HF ha =>
      rcases ih k (by omega) HF hΓ with HT | ⟨A, b, B, m, u, hm, hA, HB, RF, RP⟩
      · exact (HT.not_function hΓ HF.hasType).elim
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
      have hF := HF.hasType
      have hEq := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hF
      have hLam := HasType.lam hA HB.hasType
      have hF' := (hEq.toU.of_r henv hΓ hLam).hasType.1
      have haA := argument_at_displayed_domain hΓ hF hF' ha
      obtain ⟨v, hB⟩ := HB.hasType.isType henv hΓA
      obtain ⟨w, hCE⟩ := hF.isType henv hΓ
      rw [show proofErase Γ (.forallE C E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hCE)] at RP
      obtain ⟨_, _, _, _, _, _, _, RBody⟩ := proofErase_pi_inert_zero_pi_components heq hs hΓ hA hB RP
      have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA haA
      have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one a)
          (ProofShape.Subst.one (proofErase Γ a)) := erasedSubstAgreement_one hΓA haA
      have HInst : PiInertZeroTerminalPath D Γ (b.inst a) (B.inst a) m := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst heq hs hΓ W ES
      have RInst := proofErase_scoped_compute_subst_typed
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
        pi_inert_zero_primitive_substitution hΓ W ES hB RBody
      obtain ⟨⟨q, hC⟩, r, hE⟩ := hCE.forallE_inv henv
      have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, q, hC⟩
      have RInst' : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
          (proofErase Γ (B.inst a)) (proofErase Γ (E.inst a)) := by
        rw [proofErase_instN hΓC ha Ctx.InstN.zero hE]
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
          ProofShape.Subst.liftN] using RInst
      have RB : VExpr.BetaRed (.app f a) (b.inst a) := (VExpr.BetaRed.app RF .refl).trans .beta
      have hEq' := RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ (HasType.app hF ha)
      have hBInst : env.HasType univs Γ (B.inst a) (.sort v) := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN, VExpr.subst] using hB.subst henv.orderedStrong W hΓ
      have HT := (HInst.hasType.uniqU henv hΓ hEq'.hasType.2).of_l henv hΓ hBInst
      rcases ih (m + 1) (by omega) (HInst.convert HT RInst') hΓ with
        HTerm | ⟨A', b', B', j, v', hj, hA', HB', RF', RP'⟩
      · exact .inl (HTerm.back hΓ hEq')
      · exact .inr ⟨A', b', B', j, v', by omega, hA', HB', RB.trans RF', RP'⟩

/-- A retained function with a typed terminal path computes to a lambda at
its exact selected domain. The terminal branch is excluded by actual function
typing; Pi readout supplies the annotation computation in the other branch. -/
theorem PiInertZeroTerminalPath.selected_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertZeroTerminalPath D Γ f T n) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (ET : proofErase Γ T = .forallE X Y) :
    ∃ body, ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.lam X body) := by
  rcases H.expose heq hs hΓ with HT | ⟨A, b, B, m, u, _, hA, HB, RF, RP⟩
  · exact (HT.not_function hΓ hf).elim
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨v, hB⟩ := HB.hasType.isType henv hΓA
  rw [ET] at RP
  obtain ⟨_, _, _, _, _, _, RA, _⟩ := proofErase_pi_inert_zero_pi_components heq hs hΓ hA hB RP
  have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ hf
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have RB := proofErase_beta_forward hΓ hf RF
  rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn'] at RB
  exact ⟨_, (ScopedCompute.beta RB).trans (.lam RA .refl)⟩

open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Each retained image either recovers the exact substituted lookup type or
has terminal typing. Terminal images need no recovery at their assigned type. -/
def PiInertZeroTerminalImages (D : PureObservation.Definitions)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (PiInertStage D 0) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨ TerminalImage Γ₀ (σ i)

/-- The image condition extends under arbitrary typed binders. -/
theorem PiInertZeroTerminalImages.cons
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hA : env.HasType univs Γ A (.sort u))
    (H : PiInertZeroTerminalImages D Γ Γ₀ σ τ) :
    PiInertZeroTerminalImages D (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := PiInertStage D 0)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | HT
    · apply Or.inl
      have RL := R.rename (pi_inert_stage_rename heq hs 0)
        (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, subst_bvar_liftN,
        contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · have HW := substEq_of_thinning hΓ₀ (Ctx.Lift'.skip (A := A.subst σ) .refl)
      have HH := HT.subst hΓA HW
      apply Or.inr
      simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift', VExpr.Subst.lift] using HH

/-- Every native constructor retains exact recovery or an actual typed
terminal path at the exact substituted output. This includes conversion through
constant expansions and excludes retained projections of terminal paths. -/
theorem pi_inert_zero_recovery_subst_terminal_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (PiInertStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : PiInertZeroTerminalImages D Γ Γ₀ σ τ) :
    ScopedTypeRecovery (PiInertStage D 0) (proofEraseCtx Γ₀)
      (source.subst τ) (out.subst τ) ∨
    ∃ T' n, PiInertZeroTerminalPath D Γ₀ (e.subst σ) T' n ∧ proofErase Γ₀ T' = out.subst τ := by
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with RN | HT
    · exact .inl (EΓ ▸ RN)
    · refine .inr ⟨A.subst σ, 0, .terminal HT (W.lookup hl).hasType.1, ?_⟩
      rw [proofErase_subst_with hΓ₀ W ((HasType.bvar hl).isType henv W.wf |>.choose_spec) ES]
      rw [← EΓ, proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl]
  | sort hu => exact .inl (.sort hu)
  | const hc hw hn =>
    apply Or.inl
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    rcases ih hΓA (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA) hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (HI.cons heq hs hΓ₀ W ES hA) with RN | ⟨C, n, HP, EC⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam RN
    · refine .inr ⟨.forallE (A.subst σ) C, n+1, .lam hA' HP, ?_⟩
      obtain ⟨_, hC⟩ := HP.hasType.isType henv hΓA
      rw [show proofErase Γ₀ (.forallE _ _) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ₀ (HasType.forallE hA' hC)), EC,
        proofErase_subst_with hΓ₀ W hA ES, EA]
      rfl
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with RN | ⟨T', n, HP, ET⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]; exact .app RN
    · change proofErase Γ₀ T' = .forallE _ _ at ET
      obtain ⟨C, E, rfl, _, EC, EE⟩ := erase_forallE_inv ET
      have ha' := argument_at_displayed_domain hΓ₀
        (hf.subst henv.orderedStrong W hΓ₀) HP.hasType (ha.subst henv.orderedStrong W hΓ₀)
      refine .inr ⟨E.inst (a.subst σ), n+1, .app HP ha', ?_⟩
      obtain ⟨_, hPi⟩ := HP.hasType.isType henv hΓ₀
      obtain ⟨⟨u, hC⟩, _, hE⟩ := hPi.forallE_inv henv
      have hΓC : OnCtx (C :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hC⟩
      rw [proofErase_instN hΓC ha' Ctx.InstN.zero hE, EE,
        proofErase_subst_with hΓ₀ W ha ES, Ea, ProofShape.subst_inst]
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (PiInertStage D 0)
        (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', ht', ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    have ht'' : env.HasType univs Γ₀ (e.subst σ) (.sort (.imax u v)) :=
      ht'.subst henv.orderedStrong W hΓ₀
    refine .inr ⟨.sort (.imax u v), 0, .terminal (.type ht'') ht'', ?_⟩
    exact if_neg (not_isProof_of_sort hΓ₀ (ht''.isType henv hΓ₀ |>.choose_spec))
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with RN | ⟨C, n, HP, _⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) RN
    · rcases HP.expose heq hs hΓ₀ with HTerm | ⟨A, b, B, j, u, _, hA, HB, RF, _⟩
      · exact (HTerm.not_projection hΓ₀ (ht.subst henv.orderedStrong W hΓ₀)
          (mt (isProof_subst hΓ₀ W ht).1 hn)).elim
      · have hm' := hm.hasType.2.subst henv.orderedStrong W hΓ₀
        have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ₀ _ hm'
        have hLam := HasType.lam hA HB.hasType
        have HC := hLam.uniqU henv hΓ₀ HE.hasType.2
        simp only [VExpr.subst_mkApps, VExpr.subst] at HC
        obtain ⟨_, hPi⟩ := hLam.isType henv hΓ₀
        exact (henv.headInversion.forallE_rigid hΓ₀ (henv.projectionRigid hjInfo)
          (HC.typeChain henv hΓ₀ hPi)).elim
  | convert R RC ih =>
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := heA.isType henv W.wf
    have RC' := RC.subst_typed hstep pi_inert_zero_primitive_substitution W.wf hA EΓ EA
      (by rw [← EΓ]; exact ContextSubstitution.of_typed hΓ₀ W ES)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with RN | ⟨C, n, HP, EC⟩
    · exact .inl (.convert RN RC')
    · obtain ⟨_, hC⟩ := HP.hasType.isType henv hΓ₀
      rw [← EC] at RC'
      obtain ⟨U, HE, EU⟩ := proofErase_scoped_compute_realize hstep hΓ₀ hC rfl rfl RC'
      exact .inr ⟨U, n+1, HP.convert HE (by simpa only [EU] using RC'), EU⟩


/-- Interpreted substitutions with exact native or terminal retained images. -/
def PiInertZeroTerminalSubstitution (D : PureObservation.Definitions)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      PiInertZeroTerminalImages D Γ Γ₀ σ τ

/-- Forgetting image classification gives an ordinary interpreted substitution. -/
theorem PiInertZeroTerminalSubstitution.interpretation (W : PiInertZeroTerminalSubstitution D Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- Interpreted terminal substitutions extend through typed binders. -/
theorem PiInertZeroTerminalSubstitution.cons
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : PiInertZeroTerminalSubstitution D Δ Δ' τ) :
    PiInertZeroTerminalSubstitution D (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB,
      ES.lift hΓ₀ WS hB, HI.cons heq hs hΓ₀ WS ES hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One typed source realization supplies the interpreted image condition. -/
theorem PiInertZeroTerminalSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : PiInertZeroTerminalImages D Γ Γ₀ σ τ) :
    PiInertZeroTerminalSubstitution D (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Every comparison and carrier constructor transports under terminal-image
substitution at the unchanged expansion base. Native application uses exact
recovery or the proved selected-domain exposure; no body-check or application
repair premise remains. This theorem does not assert transport at later stages. -/
theorem ProofShape.ComputedJointCheck.transport_pi_inert_zero_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (PiInertStage D 0) Δ kind sa sb) :
    ComputedJointTransportResult (PiInertZeroTerminalSubstitution D)
      (PiInertStage D 0) Δ kind sa sb := by
  apply H.transport (PiInertZeroTerminalSubstitution D)
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
    (fun W => W.cons heq hs) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R hΓ ht EΓ Ee W => R.subst_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
      pi_inert_zero_primitive_substitution hΓ ht EΓ Ee W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  rcases pi_inert_zero_recovery_subst_terminal_images heq hs R hΓ₀ WS ES hf rfl rfl HI with
    RN | ⟨T, n, HP, ET⟩
  · exact .inl (EΓ₀ ▸ RN)
  · have HL := HP.selected_domain heq hs hΓ₀ (hf.subst henv.orderedStrong WS hΓ₀)
      (mt (isProof_subst hΓ₀ WS hf).1 hn) ET
    exact .inr (by simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HL)

/-- Any terminal typed value can replace its assigned binder in a whole
stage-zero body comparison. The assigned type need not compute from the type
certifying terminality, and both comparison modes are preserved. -/
theorem pi_inert_zero_compare_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := P)).substEq hΓP hp
  have HI : PiInertZeroTerminalImages D (P :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := by
    intro i T hl _
    cases hl with
    | zero => exact .inr HT
    | succ hl =>
      apply Or.inl
      simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
      exact .bvar
  have HR := H.transport_pi_inert_zero_terminal heq hs hΓP ha hb rfl rfl rfl
    (PiInertZeroTerminalSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓP hp) HI)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha, proofErase_instN hΓP hp Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR

/-- Ordinary conversion of a terminal-valued binder supplies an interpreted
terminal substitution in the expansion base, without annotation computation. -/
theorem PiInertZeroTerminalSubstitution.terminal_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A) :
    PiInertZeroTerminalSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply PiInertZeroTerminalSubstitution.of_typed hΓB W ES
  intro i T hl _
  cases hl with
  | zero => exact .inr (HA.convert hΓ HAB)
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    exact .bvar

/-- Full stage-zero body comparisons transport across ordinarily equal
terminal-valued binders. In particular either direction of conversion between
a universe and any equal binder is allowed. Endpoints and mode remain exact. -/
theorem pi_inert_zero_compare_terminal_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_pi_inert_zero_terminal heq hs hΓA ha hb rfl rfl rfl
    (PiInertZeroTerminalSubstitution.terminal_context hΓ HAB HA)


open private lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private eta_inst_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta

private theorem terminal_body_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (Ef : proofErase Γ f = .lam A a) (Eg : proofErase Γ g = .lam B b)
    (H : ComputedJointCompare (PiInertStage D 0) (A :: proofEraseCtx Γ) false a b) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (a.inst (proofErase Γ p)) (b.inst (proofErase Γ p)) := by
  obtain ⟨A₀, a₀, rfl, _, EA, Ea⟩ := erase_lam_inv Ef
  obtain ⟨B₀, b₀, rfl, _, EB, Eb⟩ := erase_lam_inv Eg
  obtain ⟨u, C, hA, _, ha, hb, Ectx⟩ := lambda_common_context hΓ hf hg
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA ha) hp
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HC := pi_inert_zero_compare_inst_terminal heq hs hΓ hpA HT ha hb
    (by simpa only [proofEraseCtx, EA, Ea, ← Ectx, Eb] using H)
  rw [proofErase_instN hΓA hpA Ctx.InstN.zero ha,
    proofErase_instN hΓA hpA Ctx.InstN.zero hb] at HC
  simpa only [Ea, ← Ectx, Eb] using HC

/-- Every terminal inferred lambda rule can be instantiated at a terminal
actual argument, even if both bodies depend on it and their written domains
differ. Both body-scope orientations and the proof-marker eta case are covered. -/
theorem InferredLambdaTerminal.pi_inert_zero_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (Ef : proofErase Γ f = .lam A a) (Eg : proofErase Γ g = .lam B b)
    (H : InferredLambdaTerminal (PiInertStage D 0) (proofEraseCtx Γ) A a B b) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (a.inst (proofErase Γ p)) (b.inst (proofErase Γ p)) := by
  rcases H.body_cases with ⟨_, rfl⟩ | HL | HR | HE
  · exact .leaf .refl
  · exact terminal_body_inst heq hs hΓ hp HT hf hg Ef Eg HL
  · exact .symm (terminal_body_inst heq hs hΓ hp HT hg hf Eg Ef (.symm HR))
  · rcases HE with HE | HE
    · exact .compute (.beta (eta_inst_typed hΓ hp hf hg (by simpa only [Ef, Eg] using HE) Ef Eg))
        .refl (.leaf .refl)
    · exact .compute .refl
        (.beta (eta_inst_typed hΓ hp hg hf (by simpa only [Ef, Eg] using HE) Eg Ef)) (.leaf .refl)

/-- Stage-zero lambda computation retains both component paths in their
original scopes; context independence handles changing written annotations. -/
theorem ProofShape.ScopedCompute.pi_inert_zero_lam_parts
    (R : ScopedCompute (PiInertStage D 0) Δ (.lam A a) out) :
    ∃ X x, out = .lam X x ∧ ScopedCompute (PiInertStage D 0) Δ A X ∧
      ScopedCompute (PiInertStage D 0) (A :: Δ) a x := by
  generalize E : ProofShape.lam A a = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing A a with
  | refl => exact ⟨A, a, E.symm, .refl, .refl⟩
  | base HR => exact (pi_inert_stage_no_lam (E ▸ HR)).elim
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨X, x, EX, RA, RB⟩ := ih₁ E
    obtain ⟨X', x', EY, RA', RB'⟩ := ih₂ EX.symm
    exact ⟨X', x', EY, RA.trans RA', RB.trans (RB'.recontext_independent (fun H => H))⟩
  | lam RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | beta | app | proj | forallE => cases E

/-- An inferred comparison with one displayed lambda survives contraction at
a terminal argument. The opposite function is arbitrary and its body may
depend on that argument. The resulting checker remains Pi-inert stage zero;
no forward beta-closure hypothesis or target lambda shape is assumed. -/
theorem proofErase_pi_inert_zero_terminal_lambda_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ (.lam A a) (.forallE P T))
    (hg : env.HasType univs Γ g (.forallE P T)) (hnf : ¬ IsProof Γ (.lam A a))
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ g)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (a.inst p)) (.app (proofErase Γ g) (proofErase Γ p)) := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  obtain ⟨⟨u, hA⟩, C, ha⟩ := hf.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA ha) hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EF : proofErase Γ (.lam A a) = .lam (proofErase Γ A) (proofErase (A :: Γ) a) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨X, x, Y, y, RF, RG, HC⟩ := HR.pi_inert_lambda_cut
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize @hd hΓ hf rfl EF RF
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize @hd hΓ hg rfl rfl RG
  have HI := HC.pi_inert_zero_inst_terminal heq hs hΓ hp HT HF.hasType.2 HG.hasType.2 Ef Eg
  obtain ⟨_, _, EE, _, RB⟩ := RF.pi_inert_zero_lam_parts
  cases EE
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hpA
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hpA
  have RI := proofErase_scoped_compute_subst_typed @hd pi_inert_zero_primitive_substitution
    hΓ W ES ha RB
  have RI' : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (a.inst p)) (x.inst (proofErase Γ p)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RI
  exact .compute RI' ((ScopedCompute.app RG .refl).trans (.beta .beta)) HI

/-- A constant function with a nonproof payload can be removed from an inferred
application comparison at a terminal target argument. The other function and
its body are arbitrary; only its actual typing is supplied. No argument
comparison, displayed target lambda or target binder-independence is needed. -/
theorem proofErase_pi_inert_zero_constant_function_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (ha : env.HasType univs Γ a T) (hna : ¬ IsProof Γ a)
    (hp : env.HasType univs Γ p A) (HT : TerminalImage Γ p)
    (hg : env.HasType univs Γ g G)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a.lift)) (proofErase Γ g)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ (.app g p)) := by
  have hf : env.HasType univs Γ (.lam A a.lift) (.forallE A T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A a.lift) p) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A)) hp
  have hnapp : ¬ IsProof Γ (.app (.lam A a.lift) p) :=
    mt (isProof_congr hΓ Hbeta).1 hna
  have hnf := not_isProof_fn hΓ hf hp hnapp
  have EF : proofErase Γ (.lam A a.lift) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) a.lift) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨_, _, _, _, _, RG, _⟩ := HR.pi_inert_lambda_cut
  have hng : ¬ IsProof Γ g := by
    intro hproof
    rw [proofErase_eq_proof.2 hproof] at RG
    cases RG.pi_inert_proof_fixed
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have HE := (proofErase_computed_joint_compare_reflect @hd hΓ hf hg H).2 rfl hnf hng
  have hgPi := (HE.of_l henv hΓ hf).hasType.2
  have HApp : env.IsDefEq univs Γ (.app (.lam A a.lift) p) (.app g p) T := by
    simpa only [VExpr.inst_lift] using IsDefEq.appDF (HE.of_l henv hΓ hf) hp
  have hngp := mt (isProof_congr hΓ HApp).2 hnapp
  have EG : proofErase Γ (.app g p) = .app (proofErase Γ g) (proofErase Γ p) :=
    if_neg hngp
  have HC := proofErase_pi_inert_zero_terminal_lambda_application heq hs hΓ hp HT hf hgPi hnf H
  simpa only [VExpr.inst_lift, EG] using HC

end Lean4Lean.VEnv.Strengthening
