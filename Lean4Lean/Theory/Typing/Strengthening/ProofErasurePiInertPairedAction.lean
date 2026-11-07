import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRenamingAction

/-! # Paired image evidence and dependent evaluation

Two substitution images retain carrier evidence and cross application action
at both substituted native types. Identity, renaming, swapping and supplied
binder images preserve this data. The dependent evaluation lambda consumes
the cross action explicitly; it does not extract it from carrier histories.
No coverage theorem for arbitrary strong bodies or arbitrary lambdas is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Symmetry keeps the carrier and exact-renaming future restriction. -/
theorem PiInertRenamingHistory.symm (H : PiInertRenamingHistory D n Δ C a b) :
    PiInertRenamingHistory D n Δ C b a := by
  refine ⟨fun RC RA RB => .carrierSymm (H.base RC RB RA), ?_⟩
  intro Δ' τ W C' a' b' RC RA RB
  exact .carrierSymm (H.future W RC RB RA)

/-- Certified ordinary endpoint prefixes preserve renaming histories. The
input computations already have full interpreted evidence; this does not
give arbitrary substitution closure to the returned carrier history. -/
theorem PiInertRenamingHistory.prefixes
    (RA : PiInertEvidence D n .compute Δ a a') (RB : PiInertEvidence D n .compute Δ b b')
    (H : PiInertRenamingHistory D n Δ C a' b') : PiInertRenamingHistory D n Δ C a b :=
  ⟨PiInertCarrierResidual.prefixes RA.base RB.base H.base,
    fun W => PiInertCarrierResidual.prefixes (RA.future W.interpretation)
      (RB.future W.interpretation) (H.future W)⟩

/-- A raw variable is reflexive at every carrier through all core residuals
and exact renamings. This needs no action for an arbitrary substituted image. -/
theorem pi_inert_variable_renaming_history :
    PiInertRenamingHistory D 0 Δ C (.bvar i) (.bvar i) := by
  have localHistory {Δ C i} : PiInertCarrierResidual D 0 Δ C (.bvar i) (.bvar i) := by
    intro C' a b _ RA RB
    obtain rfl := RA.level_core_bvar_fixed
    obtain rfl := RB.level_core_bvar_fixed
    exact .carrierChecked (.leaf .refl)
  refine ⟨localHistory, ?_⟩
  intro Δ' τ W
  obtain ⟨j, Ej, _⟩ := W.lookup i
  intro C' a' b' RC RA RB
  simp only [ProofShape.subst, Ej] at RA RB
  exact localHistory RC RA RB

/-- Cross action for a pair of images at a chosen native type, including
every actual computed Pi exposure after exact renaming. This is additional
image evidence, not a consequence of carrier evidence for the same pair. -/
structure PiInertPairedImageAction (D : Definitions) (Δ : List ProofShape)
    (a b T : ProofShape) : Prop where
  expose : ∀ {Δ' τ stage A B}, ContextRenaming Δ Δ' τ →
    ScopedCompute (PiInertStage D stage) Δ' (T.subst τ) (.forallE A B) →
    PiInertRenamingAction D Δ' A B (a.subst τ) (b.subst τ)

/-- A retained single-image action supplies the diagonal paired action. -/
theorem PiInertImageAction.paired (H : PiInertImageAction D Δ a T) :
    PiInertPairedImageAction D Δ a a T := ⟨H.expose⟩

/-- The Pi exposure remains in the final world; only exact renamings compose. -/
theorem PiInertPairedImageAction.rename
    (H : PiInertPairedImageAction D Δ a b T) (W : ContextRenaming Δ Δ' τ) :
    PiInertPairedImageAction D Δ' (a.subst τ) (b.subst τ) (T.subst τ) := by
  refine ⟨?_⟩
  intro Δ'' υ stage A B V R
  have R' : ScopedCompute (PiInertStage D stage) Δ'' (T.subst (τ.comp υ)) (.forallE A B) := by
    simpa only [ProofShape.subst_subst] using R
  have HA := H.expose (W.compose V) R'
  simpa only [ProofShape.subst_subst] using HA

/-- A pair retains histories at both native carriers and action in both
orientations. Carriers and finite stages may differ. Retaining both directions
avoids synthesizing a new strong symmetry proof for recursive interpretation. -/
structure PiInertImagePair (D : Definitions) (Δ : List ProofShape)
    (a b T U : ProofShape) : Prop where
  leftHistory : ∃ n, PiInertRenamingHistory D n Δ T a b
  rightHistory : ∃ n, PiInertRenamingHistory D n Δ U a b
  leftAction : PiInertPairedImageAction D Δ a b T
  rightAction : PiInertPairedImageAction D Δ b a U

/-- Swapping images swaps the already retained carrier/action components. -/
theorem PiInertImagePair.swap (H : PiInertImagePair D Δ a b T U) :
    PiInertImagePair D Δ b a U T := by
  obtain ⟨n, HL⟩ := H.leftHistory
  obtain ⟨m, HR⟩ := H.rightHistory
  exact ⟨⟨m, HR.symm⟩, ⟨n, HL.symm⟩, H.rightAction, H.leftAction⟩

/-- Both native carriers and both actions move under the same exact renaming. -/
theorem PiInertImagePair.rename (H : PiInertImagePair D Δ a b T U)
    (W : ContextRenaming Δ Δ' τ) :
    PiInertImagePair D Δ' (a.subst τ) (b.subst τ) (T.subst τ) (U.subst τ) := by
  obtain ⟨n, HL⟩ := H.leftHistory
  obtain ⟨m, HR⟩ := H.rightHistory
  exact ⟨⟨n, HL.rename W⟩, ⟨m, HR.rename W⟩, H.leftAction.rename W, H.rightAction.rename W⟩

/-- Identity images construct the whole pair, not merely its carrier field. -/
theorem pi_inert_native_variable_image_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    PiInertImagePair D Δ (.bvar i) (.bvar i) (contextOracle Δ i) (contextOracle Δ i) :=
  ⟨⟨0, pi_inert_variable_renaming_history⟩, ⟨0, pi_inert_variable_renaming_history⟩,
    (pi_inert_native_variable_image_action heq hs).paired,
    (pi_inert_native_variable_image_action heq hs).paired⟩

/-- A paired environment has two ordinary typed interpretations into the same
target context and explicit relational image evidence. Ordinary typings alone
do not fill the image field. General composition and strong-body coverage
remain separate obligations. -/
structure PiInertPairedSubstitution (D : Definitions)
    (Δ Δ' : List ProofShape) (σ τ : ProofShape.Subst) : Prop where
  leftTyped : ContextSubstitution Δ Δ' σ
  rightTyped : ContextSubstitution Δ Δ' τ
  images : ∀ i, PiInertImagePair D Δ' (σ i) (τ i)
    ((contextOracle Δ i).subst σ) ((contextOracle Δ i).subst τ)

/-- The paired identity environment follows from the constructed native
variable pairs, including their action components. -/
theorem PiInertPairedSubstitution.identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    PiInertPairedSubstitution D Δ Δ ProofShape.Subst.id ProofShape.Subst.id := by
  refine ⟨ContextRenaming.identity.interpretation, ContextRenaming.identity.interpretation, ?_⟩
  intro i
  rw [ProofShape.subst_id]
  exact pi_inert_native_variable_image_pair heq hs

/-- Pair symmetry uses the retained reverse components, without a recursive
call at an increased derivation rank. -/
theorem PiInertPairedSubstitution.swap (H : PiInertPairedSubstitution D Δ Δ' σ τ) :
    PiInertPairedSubstitution D Δ Δ' τ σ :=
  ⟨H.rightTyped, H.leftTyped, fun i => (H.images i).swap⟩

/-- Renaming the common target preserves both ordinary interpretations and
every relational image, with each native carrier substituted independently. -/
theorem PiInertPairedSubstitution.rename
    (H : PiInertPairedSubstitution D Δ Δ' σ τ) (W : ContextRenaming Δ' Δ'' υ) :
    PiInertPairedSubstitution D Δ Δ'' (σ.comp υ) (τ.comp υ) := by
  refine ⟨ContextSubstitution.comp H.leftTyped W.interpretation,
    ContextSubstitution.comp H.rightTyped W.interpretation, ?_⟩
  intro i
  simpa only [ProofShape.Subst.comp, ProofShape.subst_subst] using (H.images i).rename W

/-- A supplied argument pair extends the original body environment. The
actual binder interpretations and the entire pair relation are required
explicitly. Tail native types cancel their lifts against the new head images. -/
theorem PiInertPairedSubstitution.cons
    (H : PiInertPairedSubstitution D Δ Δ' σ τ)
    (WL : ContextSubstitution (T::Δ) Δ' (σ.cons x))
    (WR : ContextSubstitution (T::Δ) Δ' (τ.cons y))
    (HP : PiInertImagePair D Δ' x y (T.subst σ) (T.subst τ)) :
    PiInertPairedSubstitution D (T::Δ) Δ' (σ.cons x) (τ.cons y) := by
  refine ⟨WL, WR, ?_⟩
  intro i
  cases i with
  | zero => simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using HP
  | succ i => simpa only [contextOracle, TypeOracle.cons, ProofShape.Subst.cons,
      ProofShape.lift_subst_cons] using H.images i

/-- Cross image action consumes a genuinely typed shared argument at the
actual dependent result carrier. Proof-valued applications use proof erasure;
other applications reconstruct erasure and use the retained action directly.
No whole-function history is promoted to action. -/
theorem PiInertPairedImageAction.apply_actual
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : PiInertPairedImageAction D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B))) :
    ∃ n, PiInertRenamingHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  have hfx := hf.app hx
  have hgx := hg.app hx
  by_cases hp : IsProof Γ (.app f x)
  · have hq := isProof_of_common_type hΓ hfx hgx hp
    have HR : PiInertEvidence D 0 .compute (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (proofErase Γ (.app f x)) := .core hs hc hΓ hfx .refl
    have HH := (HR.join hc HR).carrier_history (C := proofErase Γ (B.inst x))
    rw [proofErase_eq_proof.2 hp] at HH
    exact ⟨0, by simpa only [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hq]
      using HH.renaming_history⟩
  have hq : ¬ IsProof Γ (.app g x) := fun hq => hp (isProof_of_common_type hΓ hgx hfx hq)
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨w, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  have R : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      ((proofErase Γ (.forallE A B)).subst ProofShape.Subst.id)
      (.forallE (proofErase Γ A) (proofErase (A::Γ) B)) := by
    rw [ProofShape.subst_id, EP]
    exact .refl
  have HA := H.expose ContextRenaming.identity R
  simp only [ProofShape.subst_id] at HA
  have RX : PiInertEvidence D 0 .compute (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ x) :=
    .core hs hc hΓ hx .refl
  have HX := (RX.join hc RX).carrier_history (C := proofErase Γ A)
  obtain ⟨n, HN⟩ := HA.act ContextRenaming.identity
    (by simpa only [ProofShape.subst_id] using HX.renaming_history)
  simp only [ProofShape.Subst.id_lift, ProofShape.subst_id] at HN
  refine ⟨n, ?_⟩
  rw [show proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) from if_neg hp,
    show proofErase Γ (.app g x) = .app (proofErase Γ g) (proofErase Γ x) from if_neg hq,
    proofErase_instN hΓA hx Ctx.InstN.zero hB]
  exact HN

/-- The dependent evaluation lambda `fun h => h x` accepts a function pair
with retained cross action. Both beta prefixes preserve the exact carrier
B.inst x and every renaming/core-residual clause. This closes the evaluator
test with explicit action input; it does not claim action for arbitrary
carrier-related function arguments or arbitrary lambda bodies. -/
theorem pi_inert_evaluation_of_paired_action
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : PiInertPairedImageAction D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B))) :
    ∃ n, PiInertRenamingHistory D n (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app (.lam (.forallE A B) (.app (.bvar 0) x.lift)) f))
      (proofErase Γ (.app (.lam (.forallE A B) (.app (.bvar 0) x.lift)) g)) := by
  obtain ⟨n, HN⟩ := H.apply_actual hs hc hΓ hf hg hx
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  let T := VExpr.forallE A B
  let ev := VExpr.lam T (.app (.bvar 0) x.lift)
  have heval : env.HasType univs Γ ev (.forallE T (B.inst x).lift) := by
    apply HasType.lam hPi
    have hv : env.HasType univs (T::Γ) (.bvar 0) T.lift := .bvar .zero
    have happ := hv.app (hx.weak henv)
    simpa only [T, VExpr.lift, VExpr.liftN, ← VExpr.liftN_inst_hi] using happ
  have beta {h} (hh : env.HasType univs Γ h T) :
      Compute (ErasedLevelCore D) (proofErase Γ (.app ev h)) (proofErase Γ (.app h x)) := by
    have R := proofErase_beta_forward hΓ (heval.app hh) (show VExpr.BetaRed (.app ev h)
      ((VExpr.app (.bvar 0) x.lift).inst h) from .beta)
    exact .beta (by simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using R)
  exact ⟨n, HN.prefixes (PiInertEvidence.core hs hc hΓ (heval.app hf) (beta hf))
    (PiInertEvidence.core hs hc hΓ (heval.app hg) (beta hg))⟩

/-- The weaker future discipline retains the original strengthening readout.
A renaming history relating distinct raw variables at the lifted Eq type
probe already forces carrier exposure, and the proved recognizer descends the
original propositions. No arbitrary-substitution history is needed here.
Constructing this history from the relevant strong derivation remains open. -/
theorem PiInertRenamingHistory.type_probe_descend
    (H : PiInertRenamingHistory D stage (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe u (S.liftN count) (P.liftN count) (Q.liftN count) q))
      (.bvar i) (.bvar j)) (hne : i ≠ j)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count 0 Γ Γ') (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN count) (Q.liftN count))) :
    env.IsDefEqU univs Γ P Q := by
  rcases (H.base .refl .refl .refl).checked_or_exposed with HC | ⟨out, R, HE, _⟩
  · exact (hne HC.pi_inert_bvar_injective).elim
  · exact pi_inert_type_probe_descend heq hs hreg hoff hRec hΓ hΓ' W hS hP hQ hq R HE

end Lean4Lean.VEnv.Strengthening
