import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureEtaBypass
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLambdaCountReadout

/-! # Global primitive minima for pair projection readout

Changing lambda annotations can increase the finite guard stage. The residual
function-eta case therefore needs a minimum over all stages, while its source
history and final field tail may use independently chosen finite stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A reachable constructor function-eta case with a major computation that
is minimum over every finite stage. Its counted field tail also retains the
minimum of the full projection, allowing competing majors to change. The source and field histories retain
their own finite stages. The function-eta continuation is still unresolved;
this minimum permits body replay at a larger stage without losing the measure. -/
def GlobalPairFunctionEtaProjection (D : Definitions) (Γ : List VExpr)
    (family : Name) (info : VProjectionInfo) (source out : ProofShape) : Prop :=
  ∃ m field value major result stage,
    env.HasType univs Γ m (.const family []) ∧
    (∃ reachStage, ScopedCompute (PiInertStage D reachStage) (proofEraseCtx Γ) source (proofErase Γ m)) ∧
    proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
    RigidSpineEtaCut D stage (proofEraseCtx Γ) info.ctorName [] [field, value] major
      (fun k levels pre pending target =>
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) (proofEraseCtx Γ)
          (ProofShape.mkApps (.const info.ctorName levels) pre) target ∧
        pre.length < 2 ∧ pending ≠ [] ∧ ∀ rest, pending ≠ .proof :: rest) ∧
    (∃ cost, ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ) (proofErase Γ m) major ∧
      (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
        (proofErase Γ m) major → cost ≤ j) ∧
      ∃ tailCost, ScopedComputeCount (PiInertStage D stage) tailCost (proofEraseCtx Γ) result out ∧
        ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
          (.proj family 0 (proofErase Γ m)) out → cost + 1 + tailCost ≤ j) ∧
    Primitive D (.proj family 0 major) result ∧
    ∃ tailStage, ScopedCompute (PiInertStage D tailStage) (proofEraseCtx Γ) result out

/-- A source prefix can use a different finite stage; only its combined source
history is raised to a common bound. The globally minimal cut is unchanged. -/
theorem GlobalPairFunctionEtaProjection.prefix
    (H : GlobalPairFunctionEtaProjection D Γ family info middle out)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) source middle) :
    GlobalPairFunctionEtaProjection D Γ family info source out := by
  obtain ⟨m, field, value, major, result, stage, hm, ⟨reachStage, RM⟩, EM, HC, HM, RI, RT⟩ := H
  exact ⟨m, field, value, major, result, stage, hm,
    ⟨max n reachStage, (R.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).trans
      (RM.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))⟩, EM, HC, HM, RI, RT⟩

/-- A selected type projection either reads its original field with strictly
fewer primitive occurrences at some finite stage, or has a globally minimal
function-eta witness at a reachable pair. Whole-record structure eta is
eliminated by strong induction on the supplied count. Competing paths can use
larger stages; common finite bounds preserve their exact primitive counts. -/
theorem proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedComputeCount (PiInertStage D n) bound (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    (∃ later j, j < bound ∧ ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) field out) ∨
    GlobalPairFunctionEtaProjection D Γ family info (proofErase Γ m) out := by
  induction bound using Nat.strongRecOn generalizing n m field with
  | ind bound ih =>
    obtain ⟨stage, cost, RC, Hmin⟩ := R.minimal_across_stages
    have hcost := Hmin _ _ R
    have hd : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
      ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs stage)
    have hprim : ∀ {Δ a b}, Primitive D a b → PiInertStage D stage Δ a b :=
      fun H => pi_inert_stage_core (.inl (.inl (.inl H)))
    have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
    have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
      ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    obtain ⟨major, result, cp, ct, hsplit, RM, RS, RF⟩ :=
      pi_inert_sorted_projection_selection_count heq hs HT hout hproj RC
    have HmajorMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
        (proofErase Γ m) major → cp ≤ j := by
      intro later j RJ
      have Ralt : ScopedComputeCount (PiInertStage D (max later stage)) (j + 1 + ct)
          (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) out :=
        ((ScopedComputeCount.proj (RJ.mono (pi_inert_stage_mono (Nat.le_max_left _ _)))).trans
          (.base (pi_inert_stage_mono (Nat.le_max_right _ _) (hprim RS)))).trans
          (RF.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))
      have HH := Hmin _ _ Ralt
      omega
    have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
      cases RS with
      | projIota =>
        intro A b rest E
        have HH := congrArg ProofShape.constHead E
        simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
        cases HH
    obtain ⟨value, EM⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hm RI
    have HTM : TypedSource (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
    rcases pi_inert_counted_rigid_spine_readout_or_eta_cut heq hs (henv.projectionCtorRigid hi)
        hD HTM hmajor (EM ▸ RM) with ⟨levels, args, ca, hca, EO, HL, HA⟩ | HC
    · cases HL
      cases HA with | cons RA HA =>
        cases HA with | cons _ HA =>
          cases HA
          rename_i cA A cV v RV
          have RI' : Primitive D (.proj family 0 major) A := by
            rw [EO]
            exact .projIota hi (by simp [hp, hf]) (by simp [hp])
          have E := RI'.projection_deterministic RS
          exact .inl ⟨stage, _, by omega, (E ▸ RA).trans RF⟩
    · have HC' := RigidSpineEtaCut.closed_record (ls := []) (args := [field, value])
        heq hs hi hΓ hm EM hmajor HC
      obtain ⟨mc, levels, pre, pending, target, before, after,
        RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE⟩ := HC'
      have hmc := HMmin _ (EM ▸ RM)
      rcases HE with ⟨HE, hlen, hne, hproof⟩ | ⟨HE, hlen, EP⟩
      · exact .inr ⟨m, field, value, major, result, stage, hm, ⟨stage, .refl⟩, EM,
          ⟨mc, levels, pre, pending, target, before, after,
            RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE,
            by simpa using hlen, hne, hproof⟩,
          ⟨cp, RM, HmajorMin, ct, RF, fun later j RJ => by
            have HH := Hmin later j RJ
            omega⟩, RS, ⟨stage, RF.forget⟩⟩
      · subst pending
        simp only [List.append_nil, ProofShape.mkApps] at RP RT
        have RPactual : ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
            (proofErase Γ m) (ProofShape.mkApps (.const info.ctorName levels) pre) := EM ▸ RP
        obtain ⟨mid, HM, EMid⟩ := proofErase_scoped_compute_realize @hd hΓ hm rfl rfl RPactual.forget
        have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
          erased_static_structure_eta_expansion_stage_descent heq hs k
        have htMid := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ HM.hasType.2).1
        have RIeta : Primitive D (.proj family 0 target) (.proj family 0 (proofErase Γ mid)) :=
          proofErase_closed_structure_type_projection_primitive @hguard hi (by omega)
            hΓ HM.hasType.2 htMid (EMid ▸ HE)
        have Rroot : ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ) (proofErase Γ mid) target :=
          .base (EMid ▸ HR)
        obtain ⟨expanded, HEta, EExpanded⟩ :=
          proofErase_scoped_compute_realize @hd hΓ HM.hasType.2 rfl rfl Rroot
        have Rnext : ScopedComputeCount (PiInertStage D stage) (after + 1 + ct) (proofEraseCtx Γ)
            (.proj family 0 target) out :=
          ((ScopedComputeCount.proj RT).trans (.base (hprim RS))).trans RF
        have hnext : after + 1 + ct < bound := by omega
        rcases ih _ hnext HEta.hasType.2 (EExpanded ▸ RIeta) (EExpanded ▸ Rnext) with
          ⟨later, j, hj, RJ⟩ | Hnext
        · have RPproj : ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
              (.proj family 0 (proofErase Γ m)) (.proj family 0 (proofErase Γ mid)) := by
            rw [EMid]
            exact .proj RPactual
          have Hcontra := Hmin _ _ ((RPproj.mono
            (pi_inert_stage_mono (Nat.le_max_right later stage))).trans
            (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later stage))))
          omega
        · have Rreach : ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ)
              (proofErase Γ m) (proofErase Γ expanded) := by
            rw [EExpanded]
            exact RPactual.forget.trans (.base HR)
          exact .inr (Hnext.prefix Rreach)

end Lean4Lean.VEnv.Strengthening
