import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedTerminalConsumption
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeRecovery

/-! # Native domains of the empty pair constructor prefix

Recovery of the constructor itself starts at its declared telescope. Pi
component readout therefore records a computation from the literal first
universe to any selected eta domain. A fresh variable under one such computed
universe can recover every other such domain exactly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- Any native Pi selected from the empty pair constructor prefix has a domain
computed from its declared first universe. The history is derived from the
actual recovery certificate, not inferred from ordinary type equality. -/
theorem pi_inert_pair_constructor_domain_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (hΓ : OnCtx Γ (env.IsType univs))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (proofEraseCtx Γ) (.const info.ctorName []) (.forallE A B)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.sort (.succ .zero)) A := by
  have hc := henv.ordered.projectionConstructor hi
  have hf : env.HasType univs [] (.const info.ctorName []) (info.ctorType.instL []) :=
    .const hc (by simp) (by simpa only [List.length_nil] using hu.symm)
  obtain ⟨v, hT⟩ := hf.isType henv (by trivial)
  have EC := proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ
  have hfΓ : env.HasType univs Γ (.const info.ctorName []) (info.ctorType.instL []) :=
    .const hc (by simp) (by simpa only [List.length_nil] using hu.symm)
  obtain ⟨v', hTΓ'⟩ := hfΓ.isType henv hΓ
  rw [hshape] at hTΓ'
  obtain ⟨⟨w, hU⟩, z, hC⟩ := hTΓ'.forallE_inv henv
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase [] (info.ctorType.instL [])) (.forallE A B) :=
    (RN.const_compute hc).mono (fun H => ⟨k, H⟩)
  rw [← EC, hshape] at RP
  have EP : proofErase Γ (.forallE (.sort (.succ .zero)) C) =
      .forallE (proofErase Γ (.sort (.succ .zero)))
        (proofErase (.sort (.succ .zero) :: Γ) C) :=
    if_neg (not_isProof_of_sort hΓ hTΓ')
  rw [EP] at RP
  obtain ⟨a, b, HA, HB, EA, EB, RA, RB⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hU hC RP
  simpa only [show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero)
    from if_neg (not_isProof_of_sort hΓ hU)] using RA

/-- A fresh variable below a computed universe recovers any domain computed
from the same universe in that enlarged context. Sort return gives its native
starting certificate; the second directed history supplies exact conversion. -/
theorem pi_inert_computed_sort_fresh_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (hv : v.WF univs)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.sort v) A)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ) (.sort v) B) :
    ∃ k, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (A :: Δ) (.bvar 0) B := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  have RBack := static_structure_computed_sort_returns heq hs hΓ hv
    (by simpa only [EΓ] using RA)
  have RL := RBack.rename (erased_static_structure_eta_expansion_stage_rename heq hs 0)
    (ContextRenaming.of_liftN hΓ hΓa Ctx.LiftN.one)
  have RL' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (A :: Δ)
      (A.liftN 1) (.sort v) := by
    simpa only [subst_bvar_liftN, proofEraseCtx, Ea, EΓ, ProofShape.liftN] using RL
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (A :: Δ) (.bvar 0) (.sort v) :=
    (ScopedTypeRecovery.bvar (i := 0)).convert RL'
  exact ((RN.mono (fun H => ⟨0, H⟩)).convert RB).finite_stage
    (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)

/-- Two empty-prefix eta recoveries derive the exact native certificate for
the original fresh type-field variable at the nested eta domain. Neither
arbitrary type-argument coverage nor forward binder transport is assumed. -/
theorem pi_inert_pair_fresh_field_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D m) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B')) :
    ∃ k, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (A :: Δ) (.bvar 0) A' := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  have RA := pi_inert_pair_constructor_domain_history heq hs hi hu hshape hΓ
    (by simpa only [EΓ] using RN)
  have RB := pi_inert_pair_constructor_domain_history heq hs hi hu hshape hΓa
    (by simpa only [proofEraseCtx, Ea, EΓ] using RN')
  apply pi_inert_computed_sort_fresh_native heq hs
    (SD := ⟨Γ, a, hΓ, EΓ, ha, Ea⟩) (v := .succ .zero) (by trivial)
  · simpa only [EΓ] using RA
  · simpa only [proofEraseCtx, Ea, EΓ] using RB

/-- A domain computed from a literal universe has a non-proof eta slot. This
uses actual sort uniqueness after realizing the directed domain history. -/
theorem pi_inert_computed_sort_eta_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (hv : v.WF univs)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.sort v) A) :
    etaArgument u = .bvar 0 := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  have hU : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs)
    hΓ hU EΓ (if_neg (not_isProof_of_sort hΓ hU)) RA
  have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ a').liftN 0) u := by
    simpa only [ProofShape.liftN_zero, EA, EΓ] using
      (show DomainSort Δ A u from ⟨Γ, a, hΓ, EΓ, ha, Ea⟩)
  have ha' := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) HA.hasType.2
  have HE := (HA.hasType.2.uniqU henv hΓ ha').sort_inv henv hΓ
  unfold etaArgument
  split
  · rename_i hz
    have HH := VLevel.equiv_def.1 (HE.trans hz) []
    simp [VLevel.eval] at HH
  · rfl

/-- The actual eta slot introduced at the empty pair constructor prefix is
the literal fresh variable. Its proof/non-proof classification is derived
from that same recovery and declared domain history. -/
theorem pi_inert_pair_constructor_eta_slot
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
      (.const info.ctorName []) (.forallE A B)) : etaArgument u = .bvar 0 := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  have RA := pi_inert_pair_constructor_domain_history heq hs hi hu hshape hΓ
    (by simpa only [EΓ] using RN)
  exact pi_inert_computed_sort_eta_argument heq hs
    (SD := ⟨Γ, a, hΓ, EΓ, ha, Ea⟩) (v := .succ .zero) (by trivial)
    (by simpa only [EΓ] using RA)

end Lean4Lean.VEnv.Strengthening
