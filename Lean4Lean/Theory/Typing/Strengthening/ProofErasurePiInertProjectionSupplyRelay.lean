import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureObserverBoundary

/-! # Projected-field ancestry through successive component supplies

Before each endpoint map, factor the projected field into a major computation
and a zero/one terminal action, modulo administrative deletion. Only the
terminal action crosses that map. The major computation stays in its original
scope. Repeating this construction excludes arbitrarily many component-only
application frames after a structure root in a least failed readout.

Constructor roots and retained binder frames above the observer are not
covered by this relay; they remain the next readout obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- An actual pair continuation whose application computations before reaching
the observer change only the two components. Once in the observer's scope,
the remaining execution is unrestricted. Its predicate is the original raw
continuation predicate, not a restriction to component-only competitors. -/
inductive PiInertPairComponentSupplyRun (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → ProofShape → Nat → Nat → Prop where
  | observer : PiInertProjectionRunFrames D Ω family 0 out Ω K
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) ck frames →
      PiInertPairComponentSupplyRun D Ω family info out Ω K field value ck frames
  | application : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
      PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (.const info.ctorName []) [field.subst τ, value.subst τ]) →
      ScopedArgumentsCount (PiInertStage D n) Θ ca
        [field.subst τ, value.subst τ] [nextField, nextValue] →
      PiInertPairComponentSupplyRun D Ω family info out Θ K nextField nextValue ck frames →
      PiInertPairComponentSupplyRun D Ω family info out Δ
        (PiInertApplicationContinuation D Θ τ [] K) field value (ca+ck) (frames+1)

/-- Forget the component restriction on the chosen execution. No change is
made to the contexts, actual endpoint maps, cost, frames or raw competitors. -/
theorem PiInertPairComponentSupplyRun.forget
    (H : PiInertPairComponentSupplyRun D Ω family info out Δ K field value ck frames) :
    PiInertProjectionRunFrames D Ω family 0 out Δ K
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) ck frames := by
  induction H with
  | observer HK => exact HK
  | application HT W HNext RA _ ih =>
    apply PiInertProjectionRunFrames.application HT W
    · simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        List.map_nil, ProofShape.mkApps] using HNext
    · simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        List.map_nil, Nat.zero_add, ProofShape.mkApps] using
        (ScopedComputeCount.beta (BetaRed.refl (e := .const info.ctorName []))).mkApps RA
    · exact ih

/-- Relay a computed projection field through any finite component-supply
chain. Administrative wrappers may survive at every intermediate field.
Leastness is used only for the final observer-scope pair and the fixed output.
Each guarded major path remains before the endpoint map where it was obtained;
only ordinary terminal selection and deletion syntax cross the map. -/
theorem PiInertPairComponentSupplyRun.projected_field_competitor
    (H : PiInertPairComponentSupplyRun D Ω family info out Δ K field value ck frames)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hbudget : ck < budget)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ
      (.proj family 0 source) lower) :
    ∃ later j major k, j+k ≤ fieldCost+ck ∧
      ScopedComputeCount (PiInertStage D later) j Δ source major ∧ K major k := by
  induction H generalizing source lower fieldStage fieldCost with
  | @observer K field value ck frames HK =>
    have HT := HK.forget.typed
    obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ :=
      TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
    obtain ⟨observerStage, RO⟩ := HK.forget.closed_record_same_scope heq hs hi rfl hΓ EΓ hm Em
    have HP := HK.forget.closed_record_same_scope_predicate heq hs hi rfl hΓ EΓ hm Em
    have RO' : ScopedComputeCount (PiInertStage D observerStage) ck Ω
        (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out := RO
    obtain ⟨later, j, hj, RJ⟩ := HLeast.readout_below HT RO' hbudget
    have HTfield : TypedSource Ω field :=
      (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) value).typed HT
    obtain ⟨k, hk, RK⟩ := HD.readout heq hs HTfield hout RJ
    have RFull := (RF.mono (pi_inert_stage_mono (Nat.le_max_left fieldStage later))).trans
      (RK.mono (pi_inert_stage_mono (Nat.le_max_right fieldStage later)))
    exact ⟨fieldStage, 0, source, fieldCost+k, by omega, .beta .refl,
      (HP source (fieldCost+k)).2 ⟨_, RFull⟩⟩
  | @application Δ field value Θ τ n ca nextField nextValue K ck frames HT W HNext RA HK ih =>
    obtain ⟨major, terminal, cm, HDterminal, RM, HF⟩ :=
      pi_inert_sorted_projection_terminal_frames_count heq hs HSort RF
    have HDimage := ((HD.trans HDterminal).subst τ)
    have HTfield : TypedSource Θ (field.subst τ) :=
      (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) (value.subst τ)).typed HNext
    cases RA with
    | cons RField rest =>
      cases rest with
      | cons RValue last =>
        cases last
        obtain ⟨nextLower, cnext, hcnext, RNext, HDnext⟩ :=
          HDimage.compute heq hs HTfield RField
        have HSortMajor := HSort.compute
          (ErasedScopedPrimitiveCertificateDescent.descent
            (pi_inert_stage_certificate_descent heq hs fieldStage)) RM.proj.forget
        have HSortNext : ControlTyping Θ (.proj family 0 (major.subst τ)) (.sort u) := by
          simpa only [ProofShape.subst] using HSortMajor.subst W.interpretation
        rcases HF with ⟨ET, hcm⟩ | ⟨RI, hcm⟩
        · have RN : ScopedComputeCount (PiInertStage D n) cnext Θ
              (.proj family 0 (major.subst τ)) nextLower := by
            simpa only [ET, ProofShape.subst] using RNext
          obtain ⟨later, j, endpoint, k, hcost, RJ, RK⟩ :=
            ih (by omega) HSortNext HDnext RN
          exact ⟨fieldStage, cm, major, j+k, by omega, RM,
            later, j, endpoint, k, rfl, RJ, RK⟩
        · have RIimage : Primitive D (.proj family 0 (major.subst τ)) (terminal.subst τ) := RI.subst
          have RN : ScopedComputeCount (PiInertStage D n) (1+cnext) Θ
              (.proj family 0 (major.subst τ)) nextLower :=
            (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RIimage))))).trans RNext
          obtain ⟨later, j, endpoint, k, hcost, RJ, RK⟩ :=
            ih (by omega) HSortNext HDnext RN
          exact ⟨fieldStage, cm, major, j+k, by omega, RM,
            later, j, endpoint, k, rfl, RJ, RK⟩

/-- A projected field cannot feed a component-supply chain in a global minimum
when its ancestry plus the remaining run is strictly cheaper. This comparison
retains every raw competitor and every finite stage of the original minimum. -/
theorem PiInertPairComponentSupplyRun.not_projected_field_minimum
    (H : PiInertPairComponentSupplyRun D Ω family info out Δ K field value ck frames)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hbudget : ck < budget)
    (HSort : ControlTyping Δ (.proj family 0 source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ
      (.proj family 0 source) lower)
    (hgap : fieldCost+ck < cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint →
      K endpoint k → cost ≤ j+k) : False := by
  obtain ⟨later, j, major, k, hcost, RJ, RK⟩ := H.projected_field_competitor HLeast
    heq hs hi hp hf hz hout hbudget HSort HD RF
  have HH := HM later j major k RJ RK
  omega

/-- An actual native structure expansion cannot be followed only by component
computation and any number of component-only supplies before reaching the
observer, below a least failed budget. The source pair may be in any temporary
scope and its fields need not descend independently to the observer. Native
recovery supplies the sorted projection ancestry; the minimum supplies the
strict charge for the original structure root. A later constructor root or a
retained binder frame above the observer remains to be handled. -/
theorem pi_inert_native_structure_no_component_supplies
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]) target)
    (HC : ∃ fields, target = ProofShape.mkApps (.const info.ctorName []) fields ∧
      ScopedArgumentsCount (PiInertStage D stage) Δ ca fields [field, value])
    (HK : PiInertPairComponentSupplyRun D Ω family info out Δ K field value ck frames)
    (hbudget : 1+ca+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]) endpoint →
      K endpoint k → 1+ca+ck ≤ j+k) : False := by
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ :=
    TypedSource.closed_constructor_realize hi hp hz (by simp [hf]) HT
  have HNative : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (proofEraseCtx Γ) (proofErase Γ m) target := by simpa only [EΓ, Em] using HE
  obtain ⟨HSort, _, nextValue, ET⟩ := proofErase_native_pair_structure_field D
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage)
    hi hp hf hz hadm hshape hΓ hm HNative
  simp only [EΓ, Em] at HSort ET
  obtain ⟨fields, EF, RA⟩ := HC
  have EFields := (ProofShape.const_spine_inj (EF.symm.trans ET)).2.2
  rw [EFields] at RA
  cases RA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      exact HK.not_projected_field_minimum HLeast heq hs hi hp hf hz hout
        (by omega) HSort .refl RF (by omega) HM

/-- The selected activated structure boundary has a cheaper actual target
execution than every component-supply execution with its same raw continuation
predicate. This connects the relay to the structure witness reached by the
weighted function-eta elimination. The actual target path and frame count are
preserved; the comparison allows arbitrary component stages and frame counts.
Reading the intervening constructor roots or retained frames is still open. -/
theorem PiInertActivatedPairStructureMinimum.component_supply_separation
    (H : PiInertActivatedPairStructureMinimum D Ω family info out field controls value cost frames application)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hbudget : cost ≤ budget) :
    ∃ target K stage cb ck endpoint,
      TypedSource (controls ++ Ω) target ∧
      ScopedComputeCount (PiInertStage D stage) cb (controls ++ Ω) target endpoint ∧
      PiInertProjectionRunFrames D Ω family 0 out (controls ++ Ω) K endpoint ck frames ∧
      1+cb+ck = cost ∧
      (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ Ω) target tail →
        K tail k → cb+ck ≤ j+k) ∧
      (∀ componentStage fields nextField nextValue ca tailCost tailFrames,
        target = ProofShape.mkApps (.const info.ctorName []) fields →
        ScopedArgumentsCount (PiInertStage D componentStage) (controls ++ Ω) ca fields [nextField, nextValue] →
        PiInertPairComponentSupplyRun D Ω family info out (controls ++ Ω) K
          nextField nextValue tailCost tailFrames → cost ≤ ca+tailCost) := by
  obtain ⟨stage, pre, pending, target, endpoint, cb, ck, K, EArgs, HT, HR,
    ⟨EP, guardStage, _, HE⟩, RT, HK, hc, HM, _⟩ := H
  subst pending
  simp only [List.append_nil] at EArgs
  subst pre
  have HTtarget := HT.pi_inert_compute heq hs (ScopedCompute.base HR)
  refine ⟨target, K, stage, cb, ck, endpoint, HTtarget, RT, HK, hc, ?_, ?_⟩
  · intro later j tail k RJ RK
    have RAlt := (ScopedComputeCount.base
      (pi_inert_stage_mono (Nat.le_max_left stage later) HR)).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
    have HH := HM _ _ tail k RAlt RK
    omega
  · intro componentStage fields nextField nextValue ca tailCost tailFrames ET RA HRun
    by_contra hsmall
    apply pi_inert_native_structure_no_component_supplies HLeast heq hs hi hp hf hz
      hadm hshape hout HT HE ⟨fields, ET, RA⟩ HRun (by omega)
    intro later j tail k RJ RK
    have HH := HM later j tail k RJ RK
    omega

/-- The same separation holds before the distinguished field is supplied.
The marked execution, its intermediate supply base, and its exact frame count
are retained. Competing component-supply chains need not preserve that mark;
they still cannot match the cheaper selected structure-target execution. -/
theorem PiInertFreshPairStructureMinimum.component_supply_separation
    (H : PiInertFreshPairStructureMinimum D Ω Δ family info out A x controls value cost frames)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ C b args, out ≠ ProofShape.mkApps (.lam C b) args)
    (hbudget : cost ≤ budget) :
    ∃ target K stage cb ck endpoint,
      TypedSource (controls ++ A :: Δ) target ∧
      ScopedComputeCount (PiInertStage D stage) cb (controls ++ A :: Δ) target endpoint ∧
      PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames ∧
      1+cb+ck = cost ∧
      (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ) target tail →
        K tail k → cb+ck ≤ j+k) ∧
      (∀ componentStage fields nextField nextValue ca tailCost tailFrames,
        target = ProofShape.mkApps (.const info.ctorName []) fields →
        ScopedArgumentsCount (PiInertStage D componentStage) (controls ++ A :: Δ) ca fields [nextField, nextValue] →
        PiInertPairComponentSupplyRun D Ω family info out (controls ++ A :: Δ) K
          nextField nextValue tailCost tailFrames → cost ≤ ca+tailCost) := by
  obtain ⟨stage, guardStage, target, endpoint, cb, ck, K, _, HT, HR, HE, RT, HK, hc, HM⟩ := H
  have HTtarget := HT.pi_inert_compute heq hs (ScopedCompute.base HR)
  refine ⟨target, K, stage, cb, ck, endpoint, HTtarget, RT, HK, hc, ?_, ?_⟩
  · intro later j tail k RJ RK
    have RAlt := (ScopedComputeCount.base
      (pi_inert_stage_mono (Nat.le_max_left stage later) HR)).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
    have HH := HM _ _ tail k RAlt RK
    omega
  · intro componentStage fields nextField nextValue ca tailCost tailFrames ET RA HRun
    by_contra hsmall
    apply pi_inert_native_structure_no_component_supplies HLeast heq hs hi hp hf hz
      hadm hshape hout HT HE ⟨fields, ET, RA⟩ HRun (by omega)
    intro later j tail k RJ RK
    have HH := HM later j tail k RJ RK
    omega

end Lean4Lean.VEnv.Strengthening
