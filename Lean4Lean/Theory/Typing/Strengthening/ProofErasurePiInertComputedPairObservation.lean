import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertComputedHeadReplay

/-! # Reattach a lowered constructor function to the actual pair observation

Once the supplied pair is in the observer scope, its computed function history
can be prepended verbatim. Typing rules out extra pending arguments, and all
remaining frames flatten to the exact counted projection path. The reserved
function cost is included in bounded field readout and least-failure transfer.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- Reattach an actual constructor-function history before a same-scope pair
observation. The original constructor applied to the same two fields is typed,
any extra pending arguments are impossible, and the final projected path costs
exactly function plus body plus continuation. No new minimum is assumed. -/
theorem pi_inert_computed_pair_head_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Δ (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const info.ctorName []) short)
    (HNext : TypedSource Δ (ProofShape.mkApps short ([field, value] ++ pending)))
    (RT : ScopedComputeCount (PiInertStage D bodyStage) cb Δ
      (ProofShape.mkApps short ([field, value] ++ pending)) endpoint)
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K endpoint ck frames) :
    pending = [] ∧ TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) ∧
      ∃ stage, ScopedComputeCount (PiInertStage D stage) (cg+cb+ck) Δ
        (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out := by
  have HTall := TypedSource.pi_inert_head_preimage heq hs HT (by intro E; cases E) RF.forget HNext
  rw [ProofShape.mkApps_append] at HTall
  have HTpair : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) :=
    typed_spine_head HTall
  obtain ⟨Γ, pair, hΓ, EΓ, hpair, Epair⟩ :=
    TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HTpair
  have EP := TypedSource.closed_record_pending_nil hi hΓ EΓ hpair (by simpa only [Epair] using HTall)
  subst pending
  simp only [List.append_nil] at RT
  have RHead : ScopedComputeCount (PiInertStage D functionStage) cg Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps short [field, value]) := by
    simpa only [Nat.add_zero] using RF.mkApps (ScopedArgumentsCount.refl (args := [field, value]))
  have RWhole := (RHead.mono (pi_inert_stage_mono (Nat.le_max_left functionStage bodyStage))).trans
    (RT.mono (pi_inert_stage_mono (Nat.le_max_right functionStage bodyStage)))
  obtain ⟨major, HE, EM⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent
      (pi_inert_stage_certificate_descent heq hs (max functionStage bodyStage)))
    hΓ hpair EΓ Epair RWhole.forget
  obtain ⟨observerStage, RO⟩ := HK.forget.closed_record_same_scope heq hs hi rfl hΓ EΓ HE.hasType.2 EM
  exact ⟨rfl, HTpair, _,
    (RWhole.mono (pi_inert_stage_mono (Nat.le_max_left _ observerStage))).proj.trans
      (RO.mono (pi_inert_stage_mono (Nat.le_max_right _ observerStage)))⟩

/-- A computed-pair minimum in the observer scope supplies a projection of
the original pair with its reserved function cost reattached. Its remaining
minimum is used only for its actual path and continuation, so no unrelated
re-minimization or guard transport enters the recombination. -/
theorem PiInertProjectionFrameMinimum.computed_pair_head_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Δ (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const info.ctorName []) short)
    (H : PiInertProjectionFrameMinimum D Δ family 0 out Δ
      (ProofShape.mkApps short [field, value]) cost frames) :
    TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) ∧
      ∃ stage, ScopedComputeCount (PiInertStage D stage) (cg+cost) Δ
        (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out := by
  obtain ⟨K, n, cb, ck, endpoint, HNext, RT, HK, hc, HM⟩ := H
  obtain ⟨_, HTpair, stage, RO⟩ := pi_inert_computed_pair_head_observation
    heq hs hi hp hf hz HT RF (pending := []) HNext RT HK
  exact ⟨HTpair, stage, by simpa only [← hc, Nat.add_assoc] using RO⟩

/-- Bounded readout below a least failure includes the reserved constructor
function history. The resulting field path starts at the supplied type field
itself, even when that argument has no native recovery certificate. -/
theorem PiInertPairFailureBudgetMinimum.computed_pair_head_readout
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Δ (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const info.ctorName []) short)
    (H : PiInertProjectionFrameMinimum D Δ family 0 out Δ
      (ProofShape.mkApps short [field, value]) cost frames)
    (hsmall : cg+cost < budget) :
    ∃ stage j, j ≤ cg+cost ∧ ScopedComputeCount (PiInertStage D stage) j Δ field out := by
  obtain ⟨HTpair, stage, RO⟩ := H.computed_pair_head_observation heq hs hi hp hf hz HT RF
  exact HLeast.readout_below HTpair RO hsmall

/-- A supplied computed-pair minimum strictly below the least failed budget
is contradictory once its original-field and function charges fit that same
budget. This closes the same-scope recombination case without dropping the
reserved eta charge or presuming native typing of the supplied field. -/
theorem PiInertPairProjectionBudgetFailure.no_smaller_computed_head
    (HFail : PiInertPairProjectionBudgetFailure D Δ family info original oldValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (HT : TypedSource Δ (.const info.ctorName []))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const info.ctorName []) short)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Δ original field)
    (H : PiInertProjectionFrameMinimum D Δ family 0 out Δ
      (ProofShape.mkApps short [field, value]) cost frames)
    (hbudget : charge+cg+cost ≤ budget) (hsmall : cg+cost < budget) : False := by
  obtain ⟨HTpair, stage, RO⟩ := H.computed_pair_head_observation heq hs hi hp hf hz HT RF
  have HF := HFail.transfer RField HTpair RO (by omega)
  have HH := HLeast Δ field value (cg+cost) HF
  omega

/-- Close the actual empty-prefix eta branch when its retained full pair is
next consumed by the distinguished type-field supply. The original field
history and the entire lowered function history are both charged. The actual
post-supply run gives the smaller pair observation, contradicting leastness.
The supplied argument needs no native recovery certificate. Applications or
retained binders before that supply remain separate recursive cases. -/
theorem pi_inert_fresh_field_empty_eta_direct_supply_not_failure
    {K : ProofShape → Nat → Prop}
    (HFail : PiInertPairProjectionBudgetFailure D Δ family info original oldValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) [.bvar 0, value]))
    (RP : ScopedComputeCount (PiInertStage D n) cp (A :: Δ) source
      (ProofShape.mkApps (.const info.ctorName []) [.bvar 0, value]))
    (HR : PiInertStage D n (A :: Δ) (.const info.ctorName [])
      (.lam A' (.app (.const info.ctorName []) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        [.bvar 0, value]) endpoint)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending))
    (RNext : ScopedComputeCount (PiInertStage D suffixStage) cs Δ
      (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending) major)
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K major ck frames)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Δ original x)
    (hcost : cp+1+ct+cs+ck ≤ cost) (hbudget : charge+cost < budget)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source tail →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K tail k → cost ≤ j+k) :
    False := by
  have RBody := ((ScopedComputeCount.base HR).mkApps
    (ScopedArgumentsCount.refl (args := [.bvar 0, value]))).trans RT
  have HEndpoint := HT.pi_inert_compute heq hs RBody.forget
  have HFresh : PiInertFreshFieldRun D Δ Δ family out A x []
      (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K)
      endpoint (cs+ck) (frames+1) := .supply HEndpoint W HNext RNext HK
  obtain ⟨short, domain, body, rest, cg, ca, HTshort, RShort, EL, E,
    RArgs, hsplit, hbound, hsmall, HMin⟩ :=
    pi_inert_fresh_field_empty_eta_retained_descent heq hs hi hu hshape SD RN RN' SD'
      HTlower HT RP HR RT HFresh (by omega) HM
  have hlen := RArgs.forget.length_eq
  simp only [List.length_cons, List.length_nil] at hlen
  have hrest : rest.length = 1 := by omega
  have ERest : ∃ slot, rest = [slot] := by
    cases rest with
    | nil => simp at hrest
    | cons slot tail =>
      have ET : tail = [] := List.eq_nil_of_length_eq_zero (by
        simp only [List.length_cons] at hrest
        omega)
      exact ⟨slot, by rw [ET]⟩
  obtain ⟨slot, rfl⟩ := ERest
  have ESupply : ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending =
      ProofShape.mkApps short ([x, slot.subst (ProofShape.Subst.one x)] ++ pending) := by
    rw [E]
    simp only [List.length_nil, Nat.zero_add, ProofShape.subst_mkApps,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
      List.map_cons, List.map_nil, ProofShape.subst, ProofShape.Subst.cons,
      ProofShape.mkApps_append]
  obtain ⟨_, HTpair, stage, RO⟩ := pi_inert_computed_pair_head_observation heq hs hi hp hf hz
    HTlower RShort (by simpa only [ESupply] using HNext) (by simpa only [ESupply] using RNext) HK
  have HF := HFail.transfer RField HTpair RO (by omega)
  have HH := HLeast Δ x (slot.subst (ProofShape.Subst.one x)) (cg+cs+ck) HF
  omega

end Lean4Lean.VEnv.Strengthening
