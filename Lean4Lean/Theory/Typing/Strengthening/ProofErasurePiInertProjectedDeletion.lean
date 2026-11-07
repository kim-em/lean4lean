import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertAdministrativeProjectionRelay

/-! # Administrative deletion through an actual projection observer

A sorted projection reaching an exposed output selects a constructor. At that
constructor a tracked major deletion is already equality. This lets counted
deletion simulation cross the final observer and exclude administrative roots
from body/application/projection minima without substituting guarded paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- Pending applications preserve a finite administrative deletion trace. -/
theorem AdministrativeHeadDeletion.mkApps (H : AdministrativeHeadDeletion e lower)
    (args : List ProofShape) :
    AdministrativeHeadDeletion (ProofShape.mkApps e args) (ProofShape.mkApps lower args) := by
  induction H with
  | refl => exact .refl
  | constant H => exact .constant (H.mkApps args)
  | identity H => exact .identity (H.mkApps args)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [Params] {D : Definitions}

/-- Deleting tracked administrative wrappers from a major preserves sorted
projection readout at an exposed output with no greater primitive count. The
actual selected constructor cannot retain a deletion at its head, so the final
ordinary projection primitive and its output are unchanged. -/
theorem AdministrativeHeadDeletion.projection_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : AdministrativeHeadDeletion e lower)
    (HT : ControlTyping Δ (.proj family index e) (.sort u))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ (.proj family index e) out) :
    ∃ k, k ≤ cost ∧ ScopedComputeCount (PiInertStage D n) k Δ (.proj family index lower) out := by
  have HTmajor : TypedSource Δ e := by
    obtain ⟨Γ, actual, hΓ, EΓ, ht, Ee⟩ := HT
    exact (ScopedHole.proj family index .hole).typed ⟨Γ, actual, _, hΓ, EΓ, ht, Ee⟩
  obtain ⟨major, cm, RM, HF⟩ := pi_inert_sorted_projection_count_terminal heq hs HT hout R
  rcases HF with ⟨EO, _⟩ | ⟨RI, HC⟩
  · exact (hproj major EO).elim
  · have hmajor : ∀ A b args, major ≠ ProofShape.mkApps (.lam A b) args := by
      cases RI with
      | projIota =>
        intro A b args E
        have HH := congrArg ProofShape.constHead E
        simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
        cases HH
    obtain ⟨major', j, hj, RJ, HJ⟩ := H.compute heq hs HTmajor RM
    have E := HJ.eq_of_nonlambda hmajor
    have RJ' : ScopedComputeCount (PiInertStage D n) j Δ lower major := E ▸ RJ
    exact ⟨j+1, by omega,
      RJ'.proj.trans (.base (pi_inert_stage_core (.inl (.inl (.inl RI)))))⟩

/-- Simulate a major deletion through the actual endpoint map, application
suffix and final sorted projection. All guarded computations are simulated in
their own scopes; only the raw endpoint deletion is substituted. -/
theorem pi_inert_projected_application_deletion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HD : AdministrativeHeadDeletion endpoint lower)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HSort : ControlTyping Δ (.proj family index major) (.sort u))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family index major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major) :
    ∃ k, k ≤ cs+ck ∧ PiInertApplicationContinuation D Δ τ pending
      (PiInertProjectionContinuation D Δ family index out) lower k := by
  obtain ⟨major', j, hj, RJ, HJ⟩ := ((HD.subst τ).mkApps pending).compute heq hs HNext RNext
  obtain ⟨k, hk, RK⟩ := HJ.projection_readout heq hs HSort hout hproj RObserve
  exact ⟨j+k, by omega, nextStage, j, major', k, rfl, RJ, observerStage, RK⟩

/-- A deleted administrative root at any function prefix cannot survive a
globally minimum body/application/projection execution with an exposed sorted
observer. Removing its charged occurrence strictly improves the full budget. -/
theorem pi_inert_projected_frame_minimum_no_administrative
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Ξ (ProofShape.mkApps target bodyPending))
    (RP : ScopedComputeCount (PiInertStage D bodyStage) cp Ξ original
      (ProofShape.mkApps source bodyPending))
    (RT : ScopedComputeCount (PiInertStage D bodyStage) ct Ξ
      (ProofShape.mkApps target bodyPending) endpoint)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HSort : ControlTyping Δ (.proj family index major) (.sort u))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family index major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+cs+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Ξ original endpoint' →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family index out) endpoint' k → cost ≤ j+k) :
    ¬ AdministrativeHeadDeletion target source := by
  intro HD
  obtain ⟨lower, j, hj, RJ, HJ⟩ := (HD.mkApps bodyPending).compute heq hs HT RT
  obtain ⟨k, hk, HK⟩ := pi_inert_projected_application_deletion heq hs HJ HNext RNext HSort
    RObserve hout hproj
  have HH := HM bodyStage (cp+j) lower k (RP.trans RJ) HK
  omega

/-- An actual closed pair computation followed by an interpreted endpoint map
has no pending arguments. Its later major is again a closed pair, so the final
type-field projection has its exact sort assignment. No raw constructor shape
at the body endpoint or substituted guarded computation is required. -/
theorem proofErase_closed_pair_frame_observer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RBody : ScopedComputeCount (PiInertStage D bodyStage) cb (proofEraseCtx Γ)
      (proofErase Γ m) endpoint)
    (W : ContextSubstitution (proofEraseCtx Γ) Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major) :
    pending = [] ∧ ControlTyping Δ (.proj family 0 major) (.sort (.succ .zero)) := by
  obtain ⟨body, HB, EB⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs bodyStage))
    hΓ hm rfl rfl RBody.forget
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ rfl
  have hb : env.HasType univs Γ₀ (body.subst σ) (.const family []) :=
    HB.hasType.2.subst henv.orderedStrong HS hΓ₀
  have EI : proofErase Γ₀ (body.subst σ) = endpoint.subst τ :=
    (proofErase_subst_with hΓ₀ HS HB.hasType.2 ES).trans (congrArg (fun e => e.subst τ) EB)
  have EP := TypedSource.closed_record_pending_nil hi hΓ₀ EΓ₀ hb (EI ▸ HNext)
  rw [EP] at RNext
  change ScopedComputeCount (PiInertStage D nextStage) cs Δ (endpoint.subst τ) major at RNext
  have RN : ScopedComputeCount (PiInertStage D nextStage) cs (proofEraseCtx Γ₀)
      (proofErase Γ₀ (body.subst σ)) major := by
    rw [EΓ₀, EI]
    exact RNext
  obtain ⟨actualMajor, HM, EM⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs nextStage))
    hΓ₀ hb rfl rfl RN.forget
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ₀ HM.hasType.2).1
  refine ⟨EP, Γ₀, .proj family 0 actualMajor, hΓ₀, EΓ₀, ht, ?_⟩
  exact (show proofErase Γ₀ (.proj family 0 actualMajor) = .proj family 0 (proofErase Γ₀ actualMajor)
    from if_neg (not_isProof_of_sort hΓ₀ ht)).trans (congrArg (ProofShape.proj family 0) EM)

/-- The actual non-level root at a rigid constructor in a projected frame
minimum is function eta or structure eta with an earlier native guard. Constant
and identity expansions are excluded by deletion through the complete observer;
the other primitive forms are excluded by constructor rigidity. -/
theorem pi_inert_projected_frame_constructor_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Ξ original)
    (RP : ScopedComputeCount (PiInertStage D bodyStage) cp Ξ original
      (ProofShape.mkApps (.const c levels) (pre ++ bodyPending)))
    (HR : PiInertStage D bodyStage Ξ (ProofShape.mkApps (.const c levels) pre) target)
    (HN : ¬ LevelPrimitive univs (ProofShape.mkApps (.const c levels) pre) target)
    (RT : ScopedComputeCount (PiInertStage D bodyStage) ct Ξ
      (ProofShape.mkApps target bodyPending) endpoint)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HSort : ControlTyping Δ (.proj family index major) (.sort u))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family index major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+cs+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Ξ original endpoint' →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family index out) endpoint' k → cost ≤ j+k) :
    ConstructorEtaBodyRoot D bodyStage Ξ (ProofShape.mkApps (.const c levels) pre) target := by
  have RP' : ScopedComputeCount (PiInertStage D bodyStage) cp Ξ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c levels) pre) bodyPending) := by
    simpa only [ProofShape.mkApps_append] using RP
  have HTtarget := (HT.pi_inert_compute heq hs RP'.forget).pi_inert_compute heq hs
    (((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).forget)
  have HD := pi_inert_projected_frame_minimum_no_administrative heq hs HTtarget RP' RT HNext
    RNext HSort RObserve hout hproj hcost HM
  rcases static_structure_rigid_expansion_root heq hc HR.1 (ProofShape.constHead_mkApps _ _) with
    H | H | ⟨k, hk, H | H | H⟩
  · rcases H with H | H
    · exact (erased_iota_primitive_no_rigid hc hD H (ProofShape.constHead_mkApps _ _)).elim
    · exact (HN H).elim
  · cases H with | intro _ => exact (HD (.constant .drop)).elim
  · cases H with | intro _ => exact (HD (.identity .drop)).elim
  · exact ⟨k, hk, .inl H⟩
  · exact ⟨k, hk, .inr H⟩

/-- For the actual tail after native structure eta, only another function or
structure eta can remain at the later constructor root. The observer's sort
assignment is derived from the actual closed-pair path and endpoint map. The
same counted field ancestry, root and smaller continuation minimum are retained;
this theorem does not yet read the field through those remaining eta cases. -/
theorem pi_inert_native_structure_tail_smaller_failure_or_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (HRoot : PiInertStage D bodyStage (proofEraseCtx Γ) (proofErase Γ m) target)
    (RBody : ScopedComputeCount (PiInertStage D bodyStage) cb (proofEraseCtx Γ) target endpoint)
    (W : PiInertEndpointMap (proofEraseCtx Γ) Δ τ)
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Δ (.proj family 0 major) out)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HM : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ) (proofErase Γ m) endpoint' →
      PiInertApplicationContinuation D Δ τ pending
        (PiInertProjectionContinuation D Δ family 0 out) endpoint' k → 1+cb+cs+ck ≤ j+k) :
    (pending = [] ∧ cs+ck < 1+cb+cs+ck ∧ ∃ field value',
      endpoint = ProofShape.mkApps (.const info.ctorName []) [field, value'] ∧
      PiInertPairProjectionBudgetFailure D Δ family info
        (field.subst τ) (value'.subst τ) out (cs+ck)) ∨
    (∃ value pre bodyPending rootTarget cp ct ca,
      target = ProofShape.mkApps (.const info.ctorName []) [.proj family 0 (proofErase Γ m), value] ∧
      cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D bodyStage) (proofEraseCtx Γ) ca
        [.proj family 0 (proofErase Γ m), value] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D bodyStage) cp (proofEraseCtx Γ) target
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D bodyStage (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ConstructorEtaBodyRoot D bodyStage (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      PiInertObservedBodyRoot D Δ family 0 out (1+cb+cs+ck) bodyStage (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ¬ LevelPrimitive univs (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ScopedComputeCount (PiInertStage D bodyStage) ct (proofEraseCtx Γ)
        (ProofShape.mkApps rootTarget bodyPending) endpoint ∧
      ct+cs+ck < 1+cb+cs+ck ∧
      PiInertProjectionContinuationMinimum D Δ family 0 out (proofEraseCtx Γ)
        (ProofShape.mkApps rootTarget bodyPending) (ct+cs+ck)) := by
  have RWhole := (ScopedComputeCount.base HRoot).trans RBody
  obtain ⟨_, HSort⟩ := proofErase_closed_pair_frame_observer heq hs hi hp hf hz hadm hshape
    hΓ hm RWhole W.interpretation HNext RNext
  have HTObserve : TypedSource Δ (.proj family 0 major) := by
    obtain ⟨Γ₀, e, hΓ₀, EΓ₀, ht, Ee⟩ := HSort
    exact ⟨Γ₀, e, _, hΓ₀, EΓ₀, ht, Ee⟩
  rcases pi_inert_native_structure_tail_smaller_failure_or_root heq hs hstep hi hp hf hz hadm
    hshape hΓ hm H HRoot RBody W HNext RNext HTObserve RObserve hout HM with HF |
    ⟨value, pre, bodyPending, rootTarget, cp, ct, ca, ET, hcut, hca, HA, RP, HR, HN, RT, hsmall, HMinimum⟩
  · exact .inl HF
  · have HT : TypedSource (proofEraseCtx Γ) (proofErase Γ m) := ⟨Γ, m, _, hΓ, rfl, hm, rfl⟩
    have HRootEta := pi_inert_projected_frame_constructor_root heq hs
      (henv.projectionCtorRigid hi) hD HT ((ScopedComputeCount.base HRoot).trans RP) HR HN RT
      HNext RNext HSort RObserve hout hproj (by omega) HM
    have RPrefix := (ScopedComputeCount.base HRoot).trans RP
    have HK : PiInertProjectionContinuationRun D Δ family 0 out (proofEraseCtx Γ)
        (PiInertApplicationContinuation D Δ τ pending (PiInertProjectionContinuation D Δ family 0 out))
        endpoint (cs+ck) :=
      .application (HT.pi_inert_compute heq hs RWhole.forget) W HNext RNext
        (.projection (HNext.pi_inert_compute heq hs RNext.forget) HTObserve RObserve)
    have HO : PiInertObservedBodyRoot D Δ family 0 out (1+cb+cs+ck) bodyStage (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget := by
      refine ⟨bodyPending, ct, endpoint, cs+ck, _, by omega, ?_, HR, RT, HK, ?_⟩
      · simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RPrefix.forget
      · intro later j endpoint' k RJ RK
        have RJ' : ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
            (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) endpoint' := by
          simpa only [ProofShape.mkApps_append] using RJ
        have RAlt := (RPrefix.mono (pi_inert_stage_mono (Nat.le_max_left bodyStage later))).trans
          (RJ'.mono (pi_inert_stage_mono (Nat.le_max_right bodyStage later)))
        have HH := HM _ _ endpoint' k RAlt RK
        omega
    exact .inr ⟨value, pre, bodyPending, rootTarget, cp, ct, ca, ET, hcut, hca, HA, RP, HR,
      HRootEta, HO, HN, RT, hsmall, HMinimum⟩

end Lean4Lean.VEnv.Strengthening
