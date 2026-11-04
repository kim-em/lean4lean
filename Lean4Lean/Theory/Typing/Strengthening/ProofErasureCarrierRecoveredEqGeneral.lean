import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqFamilyGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnion

/-! # Recovered-carrier comparisons enable generated Eq computation

The compatible comparison relates the literal reconstructed and requested Eq
families. Weakening under the fresh proof major gives the actual generated
family guard. No arbitrary carrier decoder or substitution assumption is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A common-typed recovered-carrier comparison supplies exactly the family comparison
of the canonical generated Eq prefix, including its fresh proof-major context.
The primitive relation is preserved, in particular at any fixed finite stage. -/
theorem proofErase_carrier_recovered_eq_family_guard_with
    (heq : env.HasCanonicalEq)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : w.WF univs)
    (hα : env.HasType univs Γ α (.sort w)) (ha : env.HasType univs Γ a α)
    (hb : env.HasType univs Γ b α)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E)
    (H : CarrierRecoveredCompare Step (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => CarrierRecoveredCompare Step Δ true))
      Γ data [v,w] [α,a,M,m,b] (canonicalEqPrefixProgram v w α a M m b reconstructed) S E := by
  apply (eqRec_family_guard_iff heq hr hn hz hS hE).2
  have hP := HasType.eqApp heq hw hα ha ha
  have hQ := HasType.eqApp heq hw hα ha hb
  have hΓQ : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have HP : CarrierRecoveredCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (eqApp w α a a)) (proofErase Γ (eqApp w α a b)) := by
    rw [proofErase_eqProofType heq hw hΓ hα ha ha,
      proofErase_eqProofType heq hw hΓ hα ha hb]
    exact .app (.base (.leaf .refl)) H
  have HL := HP.rename hrename
    (ContextRenaming.of_liftN hΓ hΓQ Ctx.LiftN.one)
  change CarrierRecoveredCompare Step (proofEraseCtx (eqApp w α a b :: Γ)) true
    (proofErase (eqApp w α a b :: Γ) (eqApp w α a a).lift)
    (proofErase (eqApp w α a b :: Γ) (eqApp w α a b).lift)
  rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hP, proofErase_liftN hΓ hΓQ Ctx.LiftN.one hQ]
  simpa only [subst_bvar_liftN] using HL

/-- A common-typed recovered-carrier comparison supplies the actual generated
Eq singleton primitive, with the exact erased source and output. -/
theorem proofErase_carrier_recovered_eq_general
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (H : CarrierRecoveredCompare Step (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  obtain ⟨hv, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hz := hr.eqRec_source_zero henv heq hn hΓ ⟨_, ht⟩
  have hl := hr.eqRec_large heq hn
  obtain ⟨_, _, _, hrest, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  obtain ⟨i, ho, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hpat := hr.patEquation_of_empty henv hrest hgen
  have hlevels : ∀ l ∈ [v,w], l.WF univs := by simp_all
  have hlen : [v,w].length = data.uvars := by simp [(hr.eqRec_target heq hn).1]
  obtain ⟨S, E, hS, hE, _⟩ := RecursorData.propElim_wf henv hr hl hz hlevels hlen ⟨i, ho⟩
  have hg := eqRec_prefix_generated (U := univs) (α := α) (a := a) (M := M) (m := m) (b := b)
    heq hr hn hz hS hE
  have habU := (proofErase_carrier_recovered_compare_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) rfl ha hb (by simpa only [List.length_nil, ProofShape.liftN_zero] using H)).1
    ⟨_, hα⟩
  have hab := habU.of_l henv hΓ ha
  have HC := canonicalEqPrefixProgram_check henv heq hΓ hpat ⟨_, ht⟩ ⟨_, hab⟩
  have HG := proofErase_carrier_recovered_eq_family_guard_with (M := M) (m := m)
    (reconstructed := eqReflApp w α.lift a.lift) heq hrename hΓ hw hα ha hb hr hn hz hS hE H
  obtain ⟨recType, hrec⟩ := hr.recursorType_exists
  let args := [α,a,M,m,b]
  let program := canonicalEqPrefixProgram v w α a M m b (eqReflApp w α.lift a.lift)
  let C : SingletonPrefixCode := ⟨data, [v,w], args.length, recType,
    program.equation, program.equationBody, S, E⟩
  obtain ⟨_, _, _, _, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  have V : C.Valid := ⟨hn ▸ hregistry.trans hlookup, hr, hl, hz, hlevels, hrec,
    heqn, hbody, hS, hE, args, program, rfl, hg⟩
  have HC : UnfoldingCheck env univs Γ (mkApps (.const data.name [v,w]) args) program := by
    simpa only [hn, args, program, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using HC
  have hnp : ¬ IsProof Γ (mkApps (.const data.name [v,w]) args) := by simpa only [hn, args, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using hnp
  have HE := proofErase_const_spine hΓ HC.source_typed hnp
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const data.name [v,w]) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, HC.source_typed, HE⟩
  change CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ)
    (proofErase Γ (mkApps (.const ``Eq.rec [v,w]) args)) (proofErase Γ program.rhs)
  rw [← hn, HE, V.output_eq heq hΓ hg HC hnp]
  exact ⟨HT, .intro V (by simp only [List.length_map, C])
    (V.telescope_eq hΓ hg ⟨_, HC.source_typed⟩) ((V.guardWith_iff heq hΓ hg ⟨_, HC.source_typed⟩).2 HG)⟩

/-- A recovered-carrier comparison at stage n enables the canonical Eq prefix
at stage n+1 through its generated family guard. The whole-proof case erases
to identity. This uses the enlarged comparison, not an old carrier decoder. -/
theorem proofErase_carrier_recovered_eq_stage_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : CarrierRecoveredCompare (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    ScopedCompute (ErasedCarrierRecoveredStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  by_cases hp : IsProof Γ (eqRecBeforeMajor v w α a M m b)
  · obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := (proofErase_carrier_recovered_compare_descend
      (erased_carrier_recovered_stage_descent heq hs stage) hΓ hΓ
      (Ctx.LiftN.zero []) rfl ha hb (by simpa only [List.length_nil, ProofShape.liftN_zero] using H)).1 ⟨_, hα⟩
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · exact .base (.inr (.inl (proofErase_carrier_recovered_eq_general heq
      (erased_carrier_recovered_stage_descent heq hs stage)
      (erased_carrier_recovered_stage_rename heq hs stage) hregistry hΓ ht hp H)))

/-- The closed union feeds its own recovered-carrier comparison back into
canonical Eq computation, preserving the literal source and result. -/
theorem proofErase_carrier_recovered_eq_union_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) true
      (proofErase Γ a) (proofErase Γ b)) :
    ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨stage, H⟩ := H.finite_stage erased_carrier_recovered_stage_mono
  exact (proofErase_carrier_recovered_eq_stage_forward heq hs hregistry hΓ ht H).mono
    (fun H => ⟨stage + 1, H⟩)

/-- Two related images of one typed body may control an actual canonical Eq
prefix. No common reduct of the images is required, and all computations used
by their certificates may themselves use recovered-carrier singleton guards. -/
theorem proofErase_carrier_recovered_eq_inst_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hq : env.HasType univs (A :: Γ) q B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) false
      (proofErase Γ x) (proofErase Γ y))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α (q.inst x) M m (q.inst y)) T) :
    ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α (q.inst x) M m (q.inst y)))
      (proofErase Γ (.lam (eqApp w α (q.inst x) (q.inst y)) m.lift)) :=
  proofErase_carrier_recovered_eq_union_forward heq hs hregistry hΓA.1 ht
    (proofErase_carrier_recovered_inst_images (erased_carrier_recovered_union_rename heq hs)
      hΓA hq hx hy H).common

end Lean4Lean.VEnv.Strengthening
