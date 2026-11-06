import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPrior

/-! # Pi-inert interpretation of recursive computation and comparison certificates

These refinements retain the outer primitive heads of the existing construction.
Guard comparisons use their original complete finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- Computation retains an actual typed output and directed full-core
commutation. Comparison retains checks at every pair of core residuals. -/
def PiInertInterpret (D : Definitions) (n : Nat) (kind : CoreFamilyKind)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  match kind with
  | .compute => TypedSource Δ b ∧ ∀ {a'}, ProofShape.Compute (ErasedLevelCore D) a a' →
      ∃ shared, ScopedCompute (PiInertStage D n) Δ a' shared ∧
        ProofShape.Compute (ErasedLevelCore D) b shared
  | .compare mode => ∀ {a' b'}, ProofShape.Compute (ErasedLevelCore D) a a' →
      ProofShape.Compute (ErasedLevelCore D) b b' →
      ComputedJointCompare (PiInertStage D n) Δ mode a' b'

/-- One induction proves the two interpretations. In the join case the common
output has an actual typed realization, and only ordinary core confluence at
that realization joins the two residual output paths. -/
theorem CoreFamilyCast.pi_inert_interpret
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n kind Δ a b) : PiInertInterpret D n kind Δ a b := by
  induction H with
  | prior H => exact fun RA RB => H.pi_inert_forward heq hs hl hcon hc hreg hoff hD RA RB
  | core hΓ ht R =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ ht rfl rfl (R.scoped (fun H => .base H))
    refine ⟨⟨_, _, _, hΓ, rfl, HE.hasType.2, EE⟩, ?_⟩
    intro a' RA
    obtain ⟨shared, RL, RR⟩ := hc hΓ ht RA R
    exact ⟨shared, RL.in_pi_inert_stage, RR⟩
  | castConsumer hu hΓ hX hY hq hx ht _ ih =>
    refine ⟨⟨_, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero hx, rfl⟩, ?_⟩
    intro a' RA
    exact pi_inert_cast_consumer_core_commute heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx ht (fun RX RY => (ih RX RY).mono pi_inert_stage_embed) RA .refl
  | trans _ _ ih₁ ih₂ =>
    refine ⟨ih₂.1, ?_⟩
    intro a' RA
    obtain ⟨middle, RL, RM⟩ := ih₁.2 RA
    obtain ⟨shared, RT, RR⟩ := ih₂.2 RM
    exact ⟨shared, RL.trans RT, RR⟩
  | join _ _ ih₁ ih₂ =>
    intro a' b' RA RB
    obtain ⟨left, RL, CL⟩ := ih₁.2 RA
    obtain ⟨right, RR, CR⟩ := ih₂.2 RB
    obtain ⟨Γ, e, T, hΓ, _, ht, E⟩ := ih₁.1
    obtain ⟨shared, LC, RC⟩ := hc hΓ ht (E ▸ CL) (E ▸ CR)
    exact .compute (RL.trans LC.in_pi_inert_stage) (RR.trans RC.in_pi_inert_stage) (.leaf .refl)
  | annotation hΓ hA hC hb ht _ ih =>
    exact fun RA RB => pi_inert_annotation_consumer_core heq hs hc hΓ hA hC hb ht
      (fun RX RY => ih RX RY) RA RB
  | lamCommon _ ih =>
    intro a' b' RA RB
    obtain ⟨A', body, rfl, RD, RL⟩ := RA.level_core_lam_inv
    obtain ⟨C', body', rfl, _, RR⟩ := RB.level_core_lam_inv
    have HB := ih (ContextSubstitution.core_binder hs RD) (a' := body) (b' := body')
    simp only [ProofShape.subst_id] at HB
    exact .lamCommon (HB RL RR)
  | lamSorted SA SC _ _ ihA ihB =>
    intro a' b' RA RB
    obtain ⟨A', body, rfl, RD, RL⟩ := RA.level_core_lam_inv
    obtain ⟨C', body', rfl, RC, RR⟩ := RB.level_core_lam_inv
    have HB := ihB (ContextSubstitution.core_binder hs RD) (a' := body) (b' := body')
    simp only [ProofShape.subst_id] at HB
    exact .lamSorted (SA.level_core hs RD) (SC.level_core hs RC) (ihA RD RC) (HB RL RR)
  | forallSorted SA SC SB SE _ _ ihA ihB =>
    intro a' b' RA RB
    obtain ⟨A', body, rfl, RD, RL⟩ := RA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨C', body', rfl, RC, RR⟩ := RB.pi_parts (fun H => erased_level_core_no_pi H)
    have HB := ihB (ContextSubstitution.core_binder hs RD) (a' := body) (b' := body')
    have SL := ContextSubstitution.sort (ContextSubstitution.core_binder hs RD) (SB.level_core hs RL)
    have SR := ContextSubstitution.sort (ContextSubstitution.core_binder hs RD) (SE.level_core hs RR)
    simp only [ProofShape.subst_id] at HB SL SR
    exact .forallSorted (SA.level_core hs RD) (SC.level_core hs RC) (ihA RD RC) SL SR (HB RL RR)
  | prefixes _ _ _ ih₁ ih₂ ih =>
    intro a' b' RA RB
    obtain ⟨left, RL, CL⟩ := ih₁.2 RA
    obtain ⟨right, RR, CR⟩ := ih₂.2 RB
    exact .compute RL RR (ih CL CR)
  | reducts _ RL RR ih => exact fun RA RB => ih (RL.trans RA) (RR.trans RB)
  | symm _ ih => exact fun RA RB => .symm (ih RB RA)
  | @raise n m kind Δ a b hle _ ih =>
    cases kind with
    | compute =>
      refine ⟨ih.1, ?_⟩
      intro a' RA
      obtain ⟨shared, RL, RR⟩ := ih.2 RA
      exact ⟨shared, RL.mono (fun H => pi_inert_stage_mono hle H), RR⟩
    | compare mode =>
      exact fun RA RB => (ih RA RB).mono (fun H => pi_inert_stage_mono hle H)
  | @weaken Γ Γ' count k n kind a b hΓ hΓ' W _ ih =>
    have WR := ContextRenaming.of_liftN hΓ hΓ' W
    cases kind with
    | compute =>
      refine ⟨?_, ?_⟩
      · simpa only [subst_bvar_liftN] using ih.1.subst WR.interpretation
      · intro a' RA
        obtain ⟨a₀, RA₀, rfl⟩ := RA.level_core_lift_inv
        obtain ⟨shared, RL, RR⟩ := ih.2 RA₀
        refine ⟨shared.liftN count k, ?_, RR.liftN level_lift⟩
        simpa only [subst_bvar_liftN] using RL.rename (pi_inert_stage_rename heq hs n) WR
    | compare mode =>
      intro a' b' RA RB
      obtain ⟨a₀, RA₀, rfl⟩ := RA.level_core_lift_inv
      obtain ⟨b₀, RB₀, rfl⟩ := RB.level_core_lift_inv
      simpa only [JointCheckKind.subst, subst_bvar_liftN] using
        (ih RA₀ RB₀).rename (pi_inert_stage_rename heq hs n) WR

/-- Computation readout retains its ordinary output tail for later composition. -/
theorem CoreFamilyCast.pi_inert_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n .compute Δ a b) (RA : ProofShape.Compute (ErasedLevelCore D) a a') :
    ∃ shared, ScopedCompute (PiInertStage D n) Δ a' shared ∧
      ProofShape.Compute (ErasedLevelCore D) b shared :=
  (H.pi_inert_interpret heq hs hl hcon hc hreg hoff hD).2 RA

/-- Comparison readout covers independent full-core paths in either mode. -/
theorem CoreFamilyCast.pi_inert_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n (.compare mode) Δ a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a') (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (PiInertStage D n) Δ mode a' b' :=
  H.pi_inert_interpret heq hs hl hcon hc hreg hoff hD RA RB

end Lean4Lean.VEnv.Strengthening
