import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectedDeletion

/-! # Sorted projection observers through arbitrary eta frames

Retain the actual final observer's sort assignment while eta descent adds
consuming or retained-binder frames. Administrative deletion then simulates
the whole execution without changing its competitor predicate or increasing
its count. This eliminates administrative roots at arbitrary frame depth;
field readout through the remaining eta roots is still open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- Retaining a lambda body preserves a finite administrative deletion trace. -/
theorem AdministrativeHeadDeletion.lam (H : AdministrativeHeadDeletion e lower) :
    AdministrativeHeadDeletion (.lam A e) (.lam A lower) := by
  induction H with
  | refl => exact .refl
  | constant H => exact .constant (.lam H)
  | identity H => exact .identity (.lam H)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [Params] {D : Definitions}

/-- The actual projection continuation with its final sort assignment retained.
Application and retained-binder frames are exactly the existing frames; only
the selected execution's terminal typing is enriched. Raw competitors still
satisfy the same untyped continuation predicate. -/
inductive PiInertSortedProjectionContinuationRun (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape) (observerSort : VLevel) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Prop where
  | projection : TypedSource Ω e → ControlTyping Ω (.proj family index e) (.sort observerSort) →
      ScopedComputeCount (PiInertStage D n) ck Ω (.proj family index e) out →
      PiInertSortedProjectionContinuationRun D Ω family index out observerSort Ω
        (PiInertProjectionContinuation D Ω family index out) e ck
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertSortedProjectionContinuationRun D Ω family index out observerSort Θ K e' ck →
      PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ
        (PiInertApplicationContinuation D Θ τ args K) e (cs+ck)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K
        (ProofShape.mkApps (.lam A' body) args) ck →
      PiInertSortedProjectionContinuationRun D Ω family index out observerSort (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck

/-- Forget only the observer's sort, retaining the exact execution and raw
competitor predicate. -/
theorem PiInertSortedProjectionContinuationRun.forget
    (H : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K e ck) :
    PiInertProjectionContinuationRun D Ω family index out Δ K e ck := by
  induction H with
  | projection HT HS R =>
    obtain ⟨Γ, actual, hΓ, EΓ, ht, Ee⟩ := HS
    exact .projection HT ⟨Γ, actual, _, hΓ, EΓ, ht, Ee⟩ R
  | application HT W HNext RNext _ ih => exact .application HT W HNext RNext ih
  | retained HT SD RD WI _ ih => exact .retained HT SD RD WI ih

/-- Administrative major deletion survives every actual consuming and retained
frame. The original typed sources justify simulation, while the final sorted
observer provides exact exposed readout. No competitor typing is required. -/
theorem PiInertSortedProjectionContinuationRun.administrative_deletion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K e ck)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (HD : AdministrativeHeadDeletion e lower) :
    ∃ k, k ≤ ck ∧ K lower k := by
  induction H generalizing lower with
  | projection _ HT R =>
    obtain ⟨k, hk, RK⟩ := HD.projection_readout heq hs HT hout hproj R
    exact ⟨k, hk, _, RK⟩
  | @application Δ e Θ τ args n cs e' K ck HT W HNext RNext HK ih =>
    obtain ⟨endpoint', j, hj, RJ, HJ⟩ := ((HD.subst τ).mkApps args).compute heq hs HNext RNext
    obtain ⟨k, hk, RK⟩ := ih HJ
    exact ⟨j+k, by omega, n, j, endpoint', k, rfl, RJ, RK⟩
  | retained _ _ _ _ _ ih => exact ih (HD.lam.mkApps _)

/-- A minimum carrying a sorted actual observer through all its frames.
Its count and competitor quantification are those of the existing projection
minimum; the final sort certificate is additional selected-execution data. -/
def PiInertSortedProjectionContinuationMinimum (D : Definitions) (Ω : List ProofShape)
    (family : Name) (index : Nat) (out : ProofShape) (observerSort : VLevel)
    (Δ : List ProofShape) (source : ProofShape) (cost : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck ∧
    cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- The enriched minimum implies the existing projection minimum with the same
source, observer, count and unconstrained raw competitors. -/
theorem PiInertSortedProjectionContinuationMinimum.forget
    (H : PiInertSortedProjectionContinuationMinimum D Ω family index out observerSort Δ source cost) :
    PiInertProjectionContinuationMinimum D Ω family index out Δ source cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, RB, HK.forget, hc, HM⟩

/-- Deleting a charged administrative root strictly improves a minimum even
when arbitrary consuming and retained-binder frames remain before the sorted
projection observer. All the chosen suffix computations retain their scope. -/
theorem pi_inert_sorted_frames_minimum_no_administrative
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ target)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original source)
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ target endpoint)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ¬ AdministrativeHeadDeletion target source := by
  intro HD
  obtain ⟨lower, j, hj, RJ, HJ⟩ := HD.compute heq hs HT RT
  obtain ⟨k, hk, RK⟩ := HK.administrative_deletion heq hs hout hproj HJ
  have HH := HM n (cp+j) lower k (RP.trans RJ) RK
  omega

/-- At arbitrary frame depth, a non-level rigid constructor root in a sorted
observed minimum is genuine function or structure eta. The full actual
continuation is preserved when excluding constant and identity roots. -/
theorem pi_inert_sorted_frames_constructor_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ original)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const c levels) (pre ++ pending)))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const c levels) pre) target)
    (HN : ¬ LevelPrimitive univs (ProofShape.mkApps (.const c levels) pre) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) endpoint)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ConstructorEtaBodyRoot D n Δ (ProofShape.mkApps (.const c levels) pre) target := by
  have RP' : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c levels) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using RP
  have HTtarget := (HT.pi_inert_compute heq hs RP'.forget).pi_inert_compute heq hs
    (((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))).forget)
  have HD := pi_inert_sorted_frames_minimum_no_administrative heq hs HTtarget RP' RT HK
    hout hproj hcost HM
  rcases static_structure_rigid_expansion_root heq hc HR.1 (ProofShape.constHead_mkApps _ _) with
    H | H | ⟨k, hk, H | H | H⟩
  · rcases H with H | H
    · exact (erased_iota_primitive_no_rigid hc hD H (ProofShape.constHead_mkApps _ _)).elim
    · exact (HN H).elim
  · cases H with | intro _ => exact (HD ((AdministrativeHeadDeletion.constant .drop).mkApps pending)).elim
  · cases H with | intro _ => exact (HD ((AdministrativeHeadDeletion.identity .drop).mkApps pending)).elim
  · exact ⟨k, hk, .inl H⟩
  · exact ⟨k, hk, .inr H⟩

/-- The actual eta cut preserves the sorted observer execution in both
branches. For consumption, its newly retained suffix-source typing supplies
the application constructor. For a surviving lambda, the old execution types
the enclosing long endpoint and body computation types its new input. -/
theorem CountedEtaContinuationCut.sorted_projection_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : CountedEtaContinuationCut D n Δ f A u args endpoint ct ck cost K)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck) :
    ∃ smaller, smaller < cost ∧
      PiInertSortedProjectionContinuationMinimum D Ω family index out observerSort (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  obtain ⟨SD, H⟩ := H
  rcases H with
    ⟨A', body', args', cf, ca, _, EO, _, _, _, cd, cb, m, _, hsmall, HT, RD, RB, _, HM⟩ |
    ⟨body', x', xs', cb, cs, m, hsmall, HT, WI, RB, RS, HTnext, _, _, HM⟩
  · have HR : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K
        (ProofShape.mkApps (.lam A' body') args') ck := by simpa only [EO] using HK
    refine ⟨cb+ck, hsmall, (fun body k => K (ProofShape.mkApps (.lam A' body) args') k),
      m, cb, ck, body', HT, RB, ?_, rfl, HM⟩
    exact .retained (HT.pi_inert_compute heq hs RB.forget) SD RD
      (pi_inert_retained_frame_interpretation heq hs SD RD) HR
  · have RT : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') endpoint := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have Hnext : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    refine ⟨cb+(cs+ck), by omega,
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs' K,
      m, cb, cs+ck, body', HT, RB, ?_, rfl, ?_⟩
    · exact .application (HT.pi_inert_compute heq hs RB.forget) (.inst WI) Hnext RT HK
    · intro later j endpoint' k RJ RK
      have HH := HM later j endpoint' k RJ RK
      omega

/-- The actual native eta induction step retains the final sorted observer
and strictly decreases the same global count. The required new application
source typing is derived in the cut theorem, not supplied by the caller. -/
theorem pi_inert_eta_sorted_projection_continuation_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    ∃ smaller, smaller < cost ∧
      PiInertSortedProjectionContinuationMinimum D Ω family index out observerSort (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller :=
  (pi_inert_eta_continuation_cut heq hs hguard HT RN SD RP HR RT HK.forget.holds hcost hmin).sorted_projection_frames heq hs HK


/-- Seed sorted eta descent from a global minimum of the full projected computation.
Unlike a minimum to a fixed major, this allows a competitor to change the
major provided its projection still computes to the same observed output. -/
theorem pi_inert_eta_sorted_projected_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (HTproj : ControlTyping Δ (.proj family index original) (.sort observerSort))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app (f.liftN 1) (etaArgument u))) args) endpoint)
    (RF : ScopedComputeCount (PiInertStage D tailStage) ck Δ (.proj family index endpoint) out)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family index original) out → cost ≤ j) :
    ∃ smaller, smaller < cost ∧
      PiInertSortedProjectionContinuationMinimum D Δ family index out observerSort (A :: Δ)
        (.app (f.liftN 1) (etaArgument u)) smaller := by
  have Reta := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := args))
  have HTend := HT.pi_inert_compute heq hs (Reta.trans RT).forget
  have HTobs := HTproj.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    ((RP.trans Reta).trans RT).proj.forget
  apply pi_inert_eta_sorted_projection_continuation_frames heq hs hguard HT RN SD RP HR RT
    (PiInertSortedProjectionContinuationRun.projection HTend HTobs RF) hcost
  rintro later j endpoint' k RJ ⟨observerStage, RK⟩
  have RC := (RJ.mono (pi_inert_stage_mono (Nat.le_max_left later observerStage))).proj.trans
    (RK.mono (pi_inert_stage_mono (Nat.le_max_right later observerStage)))
  exact hmin _ _ RC

/-- Seed the sorted frame invariant from the actual global pair-projection
alternative. The native pair assignment supplies the observer's sort, and the
same selected constructor eta supplies a strictly smaller body minimum. This
retains every original pair-cut witness and the unchanged raw competitors. -/
theorem GlobalPairFunctionEtaProjection.sorted_observed_body_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : GlobalPairFunctionEtaProjection D Γ family info source out) :
    PairProjectionEtaMinimum D Γ family info source out
      (PiInertSortedProjectionContinuationMinimum D (proofEraseCtx Γ) family 0 out (.succ .zero)) := by
  obtain ⟨m, field, value, major, result, stage, hm, Rreach, EM, HC,
    ⟨globalCost, RG, _, tailCost, RF, Hfull⟩, RI, _⟩ := H
  obtain ⟨cost, levels, pre, pending, target, before, after,
    _, Hmin, HB, HL, ⟨HA, _⟩, RP, _, HR, RT, k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have hcost := Hmin _ (EM ▸ RG)
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HTproj : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
  have Rtail : ScopedComputeCount (PiInertStage D stage) (1 + tailCost) (proofEraseCtx Γ)
      (.proj family 0 major) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RF
  have Rfull : ScopedComputeCount (PiInertStage D stage) (globalCost + 1 + tailCost)
      (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) out := by
    simpa only [Nat.add_assoc] using RG.proj.trans Rtail
  cases HE with
  | intro RN SD =>
    rename_i A B u
    obtain ⟨smaller, hsmall, HM⟩ := pi_inert_eta_sorted_projected_minimum heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole HTproj RN SD
      (by simpa only [EM, ProofShape.mkApps_append] using RP) HR RT Rtail
      (cost := globalCost + 1 + tailCost) (by omega) Hfull
    exact ⟨m, field, value, pre, pending, A, B, u, stage, before, globalCost + 1 + tailCost,
      smaller, hm, Rreach, EM, hpre, hne, hproof, HA, RP, ⟨k, hk, RN⟩, SD, Rfull, Hfull, hsmall, HM⟩

/-- A classified constructor root gives a strictly smaller sorted observed
minimum at arbitrary frame depth. Function eta enters its actual body; structure
eta has no pending arguments and drops its charged root. The field invariant
needed to close readout through these smaller minima remains unresolved. -/
theorem pi_inert_sorted_frames_constructor_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ original)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const c levels) (pre ++ pending)))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const c levels) pre) target)
    (HN : ¬ LevelPrimitive univs (ProofShape.mkApps (.const c levels) pre) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (ProofShape.mkApps target pending) endpoint)
    (HK : PiInertSortedProjectionContinuationRun D Ω family index out observerSort Δ K endpoint ck)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family index major)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint' →
      K endpoint' k → cost ≤ j+k) :
    (∃ A innerU smaller, smaller < cost ∧
      PiInertSortedProjectionContinuationMinimum D Ω family index out observerSort (A :: Δ)
        (.app ((ProofShape.mkApps (.const c levels) pre).liftN 1) (etaArgument innerU)) smaller) ∨
    (∃ guardStage, guardStage < n ∧
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
        (ProofShape.mkApps (.const c levels) pre) target ∧ pending = [] ∧ ct+ck < cost ∧
      PiInertSortedProjectionContinuationMinimum D Ω family index out observerSort Δ target (ct+ck)) := by
  obtain ⟨guardStage, hg, HE⟩ := pi_inert_sorted_frames_constructor_root heq hs hc hD HT RP
    HR HN RT HK hout hproj hcost HM
  have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D guardStage) :=
    erased_static_structure_eta_expansion_stage_descent heq hs guardStage
  have RP' : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c levels) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using RP
  have HTwhole := HT.pi_inert_compute heq hs RP'.forget
  rcases HE with HE | HE
  · cases HE with
    | intro RN SD =>
      obtain ⟨smaller, hsmall, HMinimum⟩ := pi_inert_eta_sorted_projection_continuation_frames
        heq hs hguard HTwhole RN SD RP' HR RT HK hcost HM
      exact .inl ⟨_, _, smaller, hsmall, HMinimum⟩
  · have EP := TypedSource.structure_eta_pending_nil hguard HTwhole HE
    subst pending
    have RPrefixRoot : ScopedComputeCount (PiInertStage D n) (cp+1) Δ original target :=
      RP'.trans (.base HR)
    refine .inr ⟨guardStage, hg, HE, rfl, by omega, K, n, ct, ck, endpoint,
      HT.pi_inert_compute heq hs RPrefixRoot.forget, RT, HK, rfl, ?_⟩
    intro later j endpoint' k RJ RK
    have RAlt := (RPrefixRoot.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ endpoint' k RAlt RK
    omega

/-- The actual exposed pair-projection problem supplies field readout or the
stronger eta-body minimum with a sorted final observer. No caller assumes the
new frame invariant: it is derived from the original pair assignment and path. -/
theorem proofErase_pi_inert_pair_projection_readout_or_sorted_eta_minimum
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
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    (∃ later, ScopedCompute (PiInertStage D later) (proofEraseCtx Γ) field out) ∨
    PairProjectionEtaMinimum D Γ family info (proofErase Γ m) out
      (PiInertSortedProjectionContinuationMinimum D (proofEraseCtx Γ) family 0 out (.succ .zero)) := by
  obtain ⟨bound, RC⟩ := R.count
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj RC with ⟨later, j, _, RJ⟩ | H
  · exact .inl ⟨later, RJ.forget⟩
  · exact .inr (H.sorted_observed_body_minimum heq hs hi hp hf hz hadm hshape hΓ)

end Lean4Lean.VEnv.Strengthening
