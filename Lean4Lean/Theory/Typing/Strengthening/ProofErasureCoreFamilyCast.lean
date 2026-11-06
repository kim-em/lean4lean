import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualCastGuard

/-! # Recursive computation joins stable under the full ordinary core

Computation certificates retain an ordinary core path from their output after
commuting a source path. Sequential computation and joins can therefore feed
new comparisons and casts without confluence of any guarded stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- Computation and the two comparison modes have separate interpretations. -/
inductive CoreFamilyKind where
  | compute
  | compare (mode : Bool)

/-- A finite recursive grammar alternating full-core stable computations and
comparisons. Every new cast consumes a smaller comparison child; joins consume
smaller computation children. No constructor assumes stability as an oracle. -/
inductive CoreFamilyCast (D : Definitions) :
    Nat → CoreFamilyKind → List ProofShape → ProofShape → ProofShape → Prop where
  | prior : ContextualCastGuard D n mode Δ a b → CoreFamilyCast D n (.compare mode) Δ a b
  | core (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
      (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) out) :
      CoreFamilyCast D n .compute (proofEraseCtx Γ) (proofErase Γ e) out
  | castConsumer (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
      (H : CoreFamilyCast D n (.compare true) (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y)) :
      CoreFamilyCast D (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x))
  | trans : CoreFamilyCast D n .compute Δ a b → CoreFamilyCast D n .compute Δ b c →
      CoreFamilyCast D n .compute Δ a c
  | join : CoreFamilyCast D n .compute Δ a shared → CoreFamilyCast D n .compute Δ b shared →
      CoreFamilyCast D n (.compare mode) Δ a b
  | annotation (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
      (hb : env.HasType univs (A :: Γ) b B) (ht : env.HasType univs (.forallE A B :: Γ) t T)
      (H : CoreFamilyCast D n (.compare false) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
      CoreFamilyCast D n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b)))
  | prefixes : CoreFamilyCast D n .compute Δ a a' → CoreFamilyCast D n .compute Δ b b' →
      CoreFamilyCast D n (.compare mode) Δ a' b' → CoreFamilyCast D n (.compare mode) Δ a b
  | reducts : CoreFamilyCast D n (.compare mode) Δ a b →
      ProofShape.Compute (ErasedLevelCore D) a a' → ProofShape.Compute (ErasedLevelCore D) b b' →
      CoreFamilyCast D n (.compare mode) Δ a' b'
  | symm : CoreFamilyCast D n (.compare mode) Δ a b → CoreFamilyCast D n (.compare mode) Δ b a
  | raise (hle : n ≤ m) : CoreFamilyCast D n kind Δ a b → CoreFamilyCast D m kind Δ a b
  | weaken (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
      (W : Ctx.LiftN count k Γ Γ') (H : CoreFamilyCast D n kind (proofEraseCtx Γ) a b) :
      CoreFamilyCast D n kind (proofEraseCtx Γ') (a.liftN count k) (b.liftN count k)

/-- Computation retains an actual typed output and directed full-core
commutation. Comparison retains checks at every pair of core residuals. -/
def CoreFamilyCast.Interpret (D : Definitions) (n : Nat) (kind : CoreFamilyKind)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  match kind with
  | .compute => TypedSource Δ b ∧ ∀ {a'}, ProofShape.Compute (ErasedLevelCore D) a a' →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a' shared ∧
        ProofShape.Compute (ErasedLevelCore D) b shared
  | .compare mode => ∀ {a' b'}, ProofShape.Compute (ErasedLevelCore D) a a' →
      ProofShape.Compute (ErasedLevelCore D) b b' →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ mode a' b'

/-- One induction proves the two interpretations. In the join case the common
output has an actual typed realization, and only ordinary core confluence at
that realization joins the two residual output paths. -/
theorem CoreFamilyCast.interpret
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n kind Δ a b) : CoreFamilyCast.Interpret D n kind Δ a b := by
  induction H with
  | prior H => exact fun RA RB => H.forward heq hs hl hcon hc hreg hoff hD RA RB
  | core hΓ ht R =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ ht rfl rfl (R.scoped (fun H => .base H))
    refine ⟨⟨_, _, _, hΓ, rfl, HE.hasType.2, EE⟩, ?_⟩
    intro a' RA
    obtain ⟨shared, RL, RR⟩ := hc hΓ ht RA R
    exact ⟨shared, RL.in_static_stage, RR⟩
  | castConsumer hu hΓ hX hY hq hx ht _ ih =>
    refine ⟨⟨_, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero hx, rfl⟩, ?_⟩
    intro a' RA
    exact contextual_cast_consumer_core_commute heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx ht (fun RX RY => ih RX RY) RA .refl
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
    exact .compute (RL.trans LC.in_static_stage) (RR.trans RC.in_static_stage) (.leaf .refl)
  | annotation hΓ hA hC hb ht _ ih =>
    exact fun RA RB => contextual_annotation_consumer_core heq hs hc hΓ hA hC hb ht
      (fun RX RY => ih RX RY) RA RB
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
      exact ⟨shared, RL.mono (fun H => erased_static_structure_eta_expansion_stage_mono hle H), RR⟩
    | compare mode =>
      exact fun RA RB => (ih RA RB).mono (fun H => erased_static_structure_eta_expansion_stage_mono hle H)
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
        simpa only [subst_bvar_liftN] using RL.rename (erased_static_structure_eta_expansion_stage_rename heq hs n) WR
    | compare mode =>
      intro a' b' RA RB
      obtain ⟨a₀, RA₀, rfl⟩ := RA.level_core_lift_inv
      obtain ⟨b₀, RB₀, rfl⟩ := RB.level_core_lift_inv
      simpa only [JointCheckKind.subst, subst_bvar_liftN] using
        (ih RA₀ RB₀).rename (erased_static_structure_eta_expansion_stage_rename heq hs n) WR

/-- Computation readout retains its ordinary output tail for later composition. -/
theorem CoreFamilyCast.commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n .compute Δ a b) (RA : ProofShape.Compute (ErasedLevelCore D) a a') :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ a' shared ∧
      ProofShape.Compute (ErasedLevelCore D) b shared :=
  (H.interpret heq hs hl hcon hc hreg hoff hD).2 RA

/-- Comparison readout covers independent full-core paths in either mode. -/
theorem CoreFamilyCast.forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D n (.compare mode) Δ a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a') (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ mode a' b' :=
  H.interpret heq hs hl hcon hc hreg hoff hD RA RB

end Lean4Lean.VEnv.Strengthening
