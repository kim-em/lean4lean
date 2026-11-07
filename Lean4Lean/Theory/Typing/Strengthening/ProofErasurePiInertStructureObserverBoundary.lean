import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertActivatedHeadReplay

/-! # Structure eta must remain above the final observer

At the observer itself, the expanded pair's smaller minimum reads its first
field. That field is the projection of the original pair, so it supplies a
strictly cheaper competing observation of the original source. Arbitrary
identity frames in the tail are included by the same-scope predicate theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The number of actual continuation frames bounds the number of binders
between its current context and the final observer. Identity application
frames may increase the bound; retained or consuming frames remove one binder. -/
theorem PiInertProjectionRunFrames.scope_length_bound
    (H : PiInertProjectionRunFrames D Ω family index out Δ K e ck frames) :
    Δ.length ≤ Ω.length + frames := by
  induction H with
  | projection => omega
  | application HT W HTnext RT HK ih =>
    cases W with
    | identity => omega
    | inst => simp only [List.length_cons]; omega
  | retained HT SD RD WI HK ih => simp only [List.length_cons]; omega

/-- Forget the selected structure root, retaining the original activated
full-pair minimum, its actual frames, and its unrestricted competitors. -/
theorem PiInertActivatedPairStructureMinimum.minimum
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application) :
    PiInertProjectionFrameMinimum D Ω family 0 out (controls ++ Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]) cost frames := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR, ⟨EP, HG⟩, RT, HK, hc, HM, HA⟩ := H
  subst pending
  simp only [List.append_nil] at EArgs
  subst pre
  exact ⟨K, stage, 1+ct, ck, endpoint, HT, (ScopedComputeCount.base HR).trans RT, HK, hc, HM⟩

/-- An activated structure target has a strictly cheaper full-pair minimum
with the exact projection of its original pair as first field. Both its
actual application witness and all raw competitor paths are preserved.
Replaying first-field selection through an upper-scope tail remains open. -/
theorem PiInertActivatedPairStructureMinimum.projected_field_minimum
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family []))) :
    let pair := ProofShape.mkApps (.const info.ctorName []) [field.liftN controls.length, value]
    ControlTyping (controls ++ Ω) (.proj family 0 pair) (.sort (.succ .zero)) ∧
    Primitive D (.proj family 0 pair) (field.liftN controls.length) ∧
    ∃ nextValue smaller, smaller+1 = cost ∧ smaller < cost ∧
      PiInertProjectionFrameMinimum D Ω family 0 out (controls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [.proj family 0 pair, nextValue]) smaller frames ∧
      (application = true → PiInertProjectionApplicationMinimum D Ω family 0 out (controls ++ Ω)
        (ProofShape.mkApps (.const info.ctorName []) [.proj family 0 pair, nextValue]) smaller frames) := by
  obtain ⟨stage, pre, pending, target, endpoint, ct, ck, K, EArgs, HT, HR,
    ⟨EP, guardStage, hg, HE⟩, RT, HK, hc, HM, HA⟩ := H
  subst pending
  simp only [List.append_nil] at EArgs
  subst pre
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HNative : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ) (proofErase Γ m) target := by simpa only [EΓ, Em] using HE
  obtain ⟨HSort, HTtarget, nextValue, ETarget⟩ := proofErase_native_pair_structure_field D
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    hi hp hf hz hadm hshape hΓ hm HNative
  simp only [EΓ, Em] at HSort HTtarget ETarget
  have HTailMin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω)
      target tail → K tail k → ct+ck ≤ j+k := by
    intro later j tail k RJ RK
    have RAlt := (ScopedComputeCount.base
      (pi_inert_stage_mono (Nat.le_max_left stage later) HR)).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
    have HH := HM _ _ tail k RAlt RK
    omega
  refine ⟨HSort, .projIota hi (by simp [hp, hf]) (by simp [hp]), nextValue, ct+ck,
    by omega, by omega, ?_, ?_⟩
  · have HNext : PiInertProjectionFrameMinimum D Ω family 0 out (controls ++ Ω) target (ct+ck) frames :=
      ⟨K, stage, ct, ck, endpoint, HTtarget, RT, HK, rfl, HTailMin⟩
    exact ETarget ▸ HNext
  · intro happ
    have HNext : PiInertProjectionApplicationMinimum D Ω family 0 out (controls ++ Ω) target (ct+ck) frames :=
      ⟨K, stage, ct, ck, endpoint, HTtarget, RT, HA happ, rfl, HTailMin⟩
    exact ETarget ▸ HNext

/-- Structure eta cannot be selected at the final observer in a minimum
whose budget is bounded by a least pair-readout failure. The smaller expanded
pair reads out its projected first field, which is already a strictly cheaper
observation of the original pair. This handles any identity frames in the
actual tail and does not assume a field-selection simulation under binders. -/
theorem PiInertActivatedPairStructureMinimum.not_same_scope
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field [] value cost frames application)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hcost : cost ≤ budget) : False := by
  obtain ⟨_, _, nextValue, smaller, hsplit, hsmall, HNext, _⟩ :=
    H.projected_field_minimum heq hs hi hp hf hz hadm hshape
  have HNext' : PiInertProjectionContinuationMinimum D Ω family 0 out Ω
      (ProofShape.mkApps (.const info.ctorName [])
        [.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]), nextValue]) smaller := by
    simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using HNext.forget
  obtain ⟨later, j, hj, RJ⟩ := HLeast.readout_minimum_below HNext' heq hs hi hp hf hz (by omega)
  have HSource : PiInertProjectionContinuationMinimum D Ω family 0 out Ω
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) cost := by
    simpa only [List.nil_append, List.length_nil, ProofShape.liftN_zero] using H.minimum.forget
  have HT : TypedSource Ω (ProofShape.mkApps (.const info.ctorName []) [field, value]) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := HSource
    exact HT
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HH := (HSource.closed_record_global_minimum heq hs hi hΓ EΓ hm Em).2 later j RJ
  omega

/-- An activated structure residual below a least failure must still be
strictly above the observer and have enough actual frames to discharge that
nonempty telescope. The terminal same-scope structure case is eliminated. -/
theorem PiInertActivatedPairStructureMinimum.nonempty_scope
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hcost : cost ≤ budget) : controls ≠ [] ∧ controls.length ≤ frames ∧ 0 < frames := by
  have hn : controls ≠ [] := by
    intro E
    subst controls
    exact H.not_same_scope HLeast heq hs hi hp hf hz hadm hshape hcost
  obtain ⟨_, _, _, _, _, _, _, HK, _⟩ := H.minimum
  have hlen := HK.scope_length_bound
  simp only [List.length_append] at hlen
  have hpos : 0 < controls.length := List.length_pos_iff.mpr hn
  exact ⟨hn, by omega, by omega⟩

/-- A structure target followed by its last application into the observer
cannot reach that application by component computation alone. Below the least
failure budget it must encounter a new native constructor root in its body.
The exact projected-field ancestry and a strictly smaller observed minimum
are retained; readout through that new root is still open. -/
theorem pi_inert_structure_last_application_native_root
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (HR : PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) target)
    (RB : ScopedComputeCount (PiInertStage D stage) cb Δ target endpoint)
    (W : PiInertEndpointMap Δ Ω τ)
    (HTnext : TypedSource Ω (ProofShape.mkApps (endpoint.subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D nextStage) cs Ω
      (ProofShape.mkApps (endpoint.subst τ) pending) major)
    (HK : PiInertProjectionRunFrames D Ω family 0 out Ω K major ck frames)
    (hbudget : 1+cb+cs+ck ≤ budget)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) tail →
      PiInertApplicationContinuation D Ω τ pending K tail k → 1+cb+cs+ck ≤ j+k) :
    ∃ nextValue pre bodyPending rootTarget cp ct ca,
      target = ProofShape.mkApps (.const info.ctorName [])
        [.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]), nextValue] ∧
      cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D stage) Δ ca
        [.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]), nextValue] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D stage) cp Δ target
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D stage Δ (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ConstructorEtaBodyRoot D stage Δ (ProofShape.mkApps (.const info.ctorName []) pre) rootTarget ∧
      ScopedComputeCount (PiInertStage D stage) ct Δ (ProofShape.mkApps rootTarget bodyPending) endpoint ∧
      ct+cs+ck < 1+cb+cs+ck ∧
      PiInertProjectionFrameMinimum D Ω family 0 out Δ (ProofShape.mkApps rootTarget bodyPending)
        (ct+cs+ck) (frames+1) := by
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HNative : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ) (proofErase Γ m) target := by simpa only [EΓ, Em] using HE
  obtain ⟨HSort, HTtarget, nextValue, ET⟩ := proofErase_native_pair_structure_field D
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) hi hp hf hz hadm hshape hΓ hm HNative
  simp only [EΓ, Em] at HSort HTtarget ET
  have RBody : ScopedComputeCount (PiInertStage D stage) cb Δ
      (ProofShape.mkApps (.const info.ctorName [])
        [.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]), nextValue]) endpoint := ET ▸ RB
  have HRun : PiInertProjectionRunFrames D Ω family 0 out Δ
      (PiInertApplicationContinuation D Ω τ pending K) endpoint (cs+ck) (frames+1) :=
    .application (HTtarget.pi_inert_compute heq hs RB.forget) W HTnext RT HK
  rcases RBody.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, fields, ch, ca, hcounts, EO, HL, RH, HA⟩ |
    ⟨levels, pre, bodyPending, rootTarget, cp, ct, ca, hcut, hca, HL, HA, RP, HRoot, HN, Rtail⟩
  · cases HL
    cases HA with
    | cons RF rest =>
      cases rest with
      | cons RV last =>
        cases last
        subst endpoint
        obtain ⟨_, hsmall, HFail⟩ := pi_inert_projection_frame_run_smaller_failure heq hs hi hp hf hz
          HSort RF (HTtarget.pi_inert_compute heq hs RB.forget) W.interpretation HTnext RT HK.forget
          hout (by omega) HM
        have HH := HLeast _ _ _ _ HFail
        omega
  · cases HL
    have RP' : ScopedComputeCount (PiInertStage D stage) cp Δ target
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) := ET.symm ▸ RP
    have RPrefix := (ScopedComputeCount.base HR).trans RP'
    have HNativeRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi) hD
      HT RPrefix HRoot HN Rtail (HRun.forget.pair_sorted hi hu hp hshape) hout hproj
      (cost := 1+cb+cs+ck) (by omega) HM
    have RRoot := (ScopedComputeCount.base HRoot).mkApps (ScopedArgumentsCount.refl (args := bodyPending))
    rw [← ProofShape.mkApps_append] at RRoot
    have RWhole := RPrefix.trans RRoot
    refine ⟨nextValue, pre, bodyPending, rootTarget, cp, ct, ca, ET, hcut, hca, HA, RP', HRoot,
      HNativeRoot, Rtail, by omega, _, stage, ct, cs+ck, endpoint, ?_, Rtail, HRun, by omega, ?_⟩
    · exact HT.pi_inert_compute heq hs RWhole.forget
    · intro later j tail k RJ RK
      have RAlt := (RWhole.mono (pi_inert_stage_mono (Nat.le_max_left stage later))).trans
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
      have HH := HM _ _ tail k RAlt RK
      omega

/-- Every structure residual of the actual weighted empty-prefix pair cut
still lies strictly above the final observer. The activated telescope is
nonempty; the fresh phase retains its distinguished binder as well. The exact
scope depths are bounded by actual frames, and original-field budgets persist. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_structure_above_observer
    (HFail : PiInertPairProjectionBudgetFailure D Δ family info field value out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTfield : TypedSource Δ field)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (ROuter : ScopedArgumentsCount (PiInertStage D n) Δ outerCost [field, value] args)
    (houter : outerCost ≤ cp)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (REta : PiInertStage D n Δ (.const info.ctorName [])
      (.lam A (.app (.const info.ctorName []) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args major ct
      (ConstructorEtaBodyRoot D))
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    (∃ short nextControls slot later charge' smaller nextFrames nextApplication,
      TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D later) charge' Δ field short ∧
      charge'+smaller < budget ∧
      nextControls ≠ [] ∧ nextControls.length ≤ nextFrames ∧ 0 < nextFrames ∧
      PiInertActivatedPairStructureMinimum D Δ family info out short nextControls slot smaller nextFrames nextApplication) ∨
    (∃ short baseControls A Acontrols slot later charge' smaller nextFrames,
      TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D later) charge' Δ field short ∧
      charge'+smaller < budget ∧
      Acontrols.length + 1 + baseControls.length ≤ nextFrames ∧
      PiInertFreshPairStructureMinimum D Δ (baseControls ++ Δ) family info out A
        (short.liftN baseControls.length) Acontrols slot smaller nextFrames) := by
  rcases H.empty_pair_prefix_weighted_structure_boundary HFail HLeast heq hs hi hu hp hf hz hshape
    hD hout hproj SD RN HTfield HT ROuter houter RP REta HK hcost HM with
    ⟨short, nextControls, slot, later, charge', smaller, nextFrames, nextApplication,
      HTshort, RShort, hsmall, HStructure⟩ |
    ⟨short, baseControls, nextA, Acontrols, slot, later, charge', smaller, nextFrames,
      HTshort, RShort, hsmall, HStructure⟩
  · obtain ⟨hn, hframes, hpos⟩ := HStructure.nonempty_scope HLeast heq hs hi hp hf hz hadm hshape (by omega)
    exact .inl ⟨short, nextControls, slot, later, charge', smaller, nextFrames, nextApplication,
      HTshort, RShort, hsmall, hn, hframes, hpos, HStructure⟩
  · have hframes : Acontrols.length+1+baseControls.length ≤ nextFrames := by
      obtain ⟨_, _, _, _, _, _, _, HK, _⟩ := HStructure.minimum.forget
      have HH := HK.scope_length_bound
      simp only [List.length_append, List.length_cons] at HH
      omega
    exact .inr ⟨short, baseControls, nextA, Acontrols, slot, later, charge', smaller, nextFrames,
      HTshort, RShort, hsmall, hframes, HStructure⟩

end Lean4Lean.VEnv.Strengthening
