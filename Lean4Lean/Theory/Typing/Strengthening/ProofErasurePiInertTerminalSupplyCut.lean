import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionSupplyRelay

/-! # Split an actual retained projection terminal

The exposed terminal projection forces consumption of the retained lambda.
Component computation in its body enters the existing supply relay. Otherwise
the first non-level body root is native eta and carries a strictly smaller
observed minimum. All comparisons retain arbitrary raw competitors.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

private theorem rebuild_terminal_body
    (RD : ScopedComputeCount (PiInertStage D n) cd Ω A C)
    (RX : ScopedArgumentsCount (PiInertStage D n) Ω ca args (x :: rest))
    (RJ : ScopedComputeCount (PiInertStage D later) j (A :: Ω) body endpoint)
    (HK : PiInertApplicationContinuation D Ω (ProofShape.Subst.one x) rest
      (PiInertProjectionContinuation D Ω family index out) endpoint k) :
    PiInertProjectionContinuation D Ω family index out
      (ProofShape.mkApps (.lam A body) args) (cd+j+ca+k) := by
  obtain ⟨suffixStage, cs, last, ck, hc, RS, observerStage, RO⟩ := HK
  have RLambda := (ScopedComputeCount.lam
    (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
    (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
  have RBeta : ScopedComputeCount (PiInertStage D (max n later)) 0 Ω
      (ProofShape.mkApps (.lam C endpoint) (x :: rest))
      (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) rest) := by
    simpa only [ProofShape.mkApps, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D (max n later))
        (BetaRed.beta (A := C) (b := endpoint) (a := x))).mkApps (ScopedArgumentsCount.refl (args := rest))
  have RPrefix := ((RLambda.trans RBeta).mono
    (pi_inert_stage_mono (Nat.le_max_left (max n later) suffixStage))).trans
    (RS.mono (pi_inert_stage_mono (Nat.le_max_right (max n later) suffixStage)))
  have RFinal := (RPrefix.mono (pi_inert_stage_mono
      (Nat.le_max_left (max (max n later) suffixStage) observerStage))).proj.trans
    (RO.mono (pi_inert_stage_mono (Nat.le_max_right (max (max n later) suffixStage) observerStage)))
  exact ⟨_, by simpa only [Nat.add_zero, Nat.add_assoc, hc] using RFinal⟩

/-- The actual native constructor cut left by one retained terminal. Its
component ancestry and whole prefix remain in the computed annotation context;
its selected consuming tail has one frame. The target minimum is strictly
cheaper than the original terminal. Readout through that native root is the
remaining obligation, not a premise of this record. -/
def PiInertPairTerminalNativeCut (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (out : ProofShape)
    (Ξ : List ProofShape) (field value : ProofShape) (cost : Nat) : Prop :=
  ∃ stage pre pending target cp ct ca K endpoint ck,
      ca ≤ cp ∧ cp+1+ct+ck ≤ cost ∧
      ScopedArgumentsCount (PiInertStage D stage) Ξ ca [field, value] (pre ++ pending) ∧
      ScopedComputeCount (PiInertStage D stage) cp Ξ
        (ProofShape.mkApps (.const info.ctorName []) [field, value])
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) ∧
      PiInertStage D stage Ξ (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ConstructorEtaBodyRoot D stage Ξ (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ScopedComputeCount (PiInertStage D stage) ct Ξ (ProofShape.mkApps target pending) endpoint ∧
      PiInertProjectionRunFrames D Ω family 0 out Ξ K endpoint ck 1 ∧
      ct+ck < cost ∧ PiInertProjectionFrameMinimum D Ω family 0 out Ξ
        (ProofShape.mkApps target pending) (ct+ck) 1

/-- An arbitrary exposed projection of one retained pair lambda either enters
the component-supply relay at no greater primitive cost, or selects an actual
native constructor root in the computed annotation context. The latter keeps
its component ancestry, whole prefix, root, suffix and actual consuming tail,
with a strictly smaller root-target minimum. Native-root readout and nested
retained prefixes remain open; no component-only premise is imposed on the
chosen terminal path. -/
theorem pi_inert_retained_terminal_supply_or_native_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hf : info.numFields = 2) (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HT : TypedSource (A :: Ω) (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (SD : DomainSort Ω A u)
    (RDold : ScopedComputeCount (PiInertStage D domainStage) oldDomainCost Ω A A')
    (WI : ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id)
    (HFull : TypedSource Ω (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args))
    (HProj : TypedSource Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)))
    (RO : ScopedComputeCount (PiInertStage D n) cost Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)) out)
    (HM : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)) out → cost ≤ j) :
    (∃ smaller, smaller ≤ cost ∧ PiInertPairComponentSupplyRun D Ω family info out (A :: Ω)
      (fun body k => PiInertProjectionContinuation D Ω family 0 out
        (ProofShape.mkApps (.lam A' body) args) k) field value smaller 2) ∨
    PiInertPairTerminalNativeCut D Ω family info out (A' :: Ω) field value cost := by
  have HSort := TypedSource.pair_first_projection_sort hi hu hp hshape HProj
  obtain ⟨selected, selectedField, cp, co, hselection, RP, RI, RT⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HSort hout hproj RO
  have HNon : ∀ C b rest, selected ≠ ProofShape.mkApps (.lam C b) rest := by
    cases RI with
    | projIota =>
      intro C b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  rcases RP.pi_inert_lambda_spine_or_beta with ⟨C, b, rest, cf, ca, _, E, _, _⟩ |
    ⟨C, bodyEnd, x, rest, cf, ca, cs, hsplit, RF, RX, RS⟩
  · exact (HNon C b rest E).elim
  have HTlam := typed_spine_head HFull
  have HTbody := (ScopedHole.lamBody A' .hole).typed HTlam
  obtain ⟨v, cd, cb, bodyStage, _, hfun, RDomain, RBody⟩ := typed_lambda_readout heq hs HTlam RF
  have WX : ContextSubstitution (A' :: Ω) Ω (ProofShape.Subst.one x) :=
    typed_lambda_argument_map heq hs HFull RX
  have RBeta : ScopedComputeCount (PiInertStage D n) 0 Ω
      (ProofShape.mkApps (.lam C bodyEnd) (x :: rest))
      (ProofShape.mkApps (bodyEnd.inst x) rest) := by
    simpa only [ProofShape.mkApps, Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D n)
        (BetaRed.beta (A := C) (b := bodyEnd) (a := x))).mkApps (ScopedArgumentsCount.refl (args := rest))
  have HTnext := HFull.pi_inert_compute heq hs ((RF.mkApps RX).trans RBeta).forget
  have HTnext' : TypedSource Ω (ProofShape.mkApps (bodyEnd.subst (ProofShape.Subst.one x)) rest) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
  have RS' : ScopedComputeCount (PiInertStage D n) cs Ω
      (ProofShape.mkApps (bodyEnd.subst (ProofShape.Subst.one x)) rest) selected := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
  have RObserve : ScopedComputeCount (PiInertStage D n) (1+co) Ω (.proj family 0 selected) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RT
  have HK : PiInertProjectionRunFrames D Ω family 0 out (A' :: Ω)
      (PiInertApplicationContinuation D Ω (ProofShape.Subst.one x) rest
        (PiInertProjectionContinuation D Ω family 0 out)) bodyEnd (cs+(1+co)) 1 :=
    .application (HTbody.pi_inert_compute heq hs RBody.forget) (.inst WX) HTnext' RS'
      (.projection (HFull.pi_inert_compute heq hs RP.forget)
        (HProj.pi_inert_compute heq hs RP.proj.forget) RObserve)
  have HMbody : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j (A' :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) endpoint →
      PiInertApplicationContinuation D Ω (ProofShape.Subst.one x) rest
        (PiInertProjectionContinuation D Ω family 0 out) endpoint k → cb+(cs+(1+co)) ≤ j+k := by
    intro later j endpoint k RJ RK
    obtain ⟨last, RLast⟩ := rebuild_terminal_body RDomain RX RJ RK
    have HH := HM last _ RLast
    omega
  rcases RBody.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, fields, ch, cfields, hcounts, EBody, HL, _, HA⟩ |
    ⟨levels, pre, pending, target, before, after, cfields, hcut, hfields, HL, HA, RB, HR, HN, Rtail⟩
  · cases HL
    have EFields : ∃ nextField nextValue, fields = [nextField, nextValue] := by
      cases HA with
      | cons _ tail =>
        cases tail with
        | cons _ last => cases last; exact ⟨_, _, rfl⟩
    obtain ⟨nextField, nextValue, rfl⟩ := EFields
    subst bodyEnd
    have HTend := HTbody.pi_inert_compute heq hs RBody.forget
    have ERest := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HTend WX HTnext'
    subst rest
    have RImage : ScopedComputeCount (PiInertStage D n) (cs+(1+co)) Ω
        (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [nextField.inst x, nextValue.inst x])) out := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.subst_mkApps, ProofShape.subst,
        List.map_cons, List.map_nil, ProofShape.mkApps] using RS.proj.trans RObserve
    obtain ⟨_, HCertificate⟩ := PiInertPairComponentSupplyRun.retained_terminal heq hs hi hp hf hz
      HT SD RDold WI HFull HProj
      (RDomain.mono (pi_inert_stage_mono (Nat.le_max_left n bodyStage)))
      (HA.mono (pi_inert_stage_mono (Nat.le_max_right n bodyStage)))
      (RX.mono (pi_inert_stage_mono (Nat.le_max_left n bodyStage))) RImage
    exact .inl ⟨cd+cfields+ca+(cs+(1+co)), by omega, HCertificate⟩
  · cases HL
    have HRoot := pi_inert_sorted_frames_constructor_root heq hs (henv.projectionCtorRigid hi) hD
      HTbody RB HR HN Rtail (HK.forget.pair_sorted hi hu hp hshape) hout hproj
      (cost := cb+(cs+(1+co))) (by omega) HMbody
    have RRoot := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))
    rw [← ProofShape.mkApps_append] at RRoot
    have RWhole := RB.trans RRoot
    refine .inr ⟨bodyStage, pre, pending, target, before, after, cfields, _, _, cs+(1+co),
      hfields, by omega, HA, RB, HR, HRoot, Rtail, HK, by omega,
      _, bodyStage, after, cs+(1+co), _, HTbody.pi_inert_compute heq hs RWhole.forget,
      Rtail, HK, rfl, ?_⟩
    intro later j endpoint k RJ RK
    have RAlt := (RWhole.mono (pi_inert_stage_mono (Nat.le_max_left bodyStage later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right bodyStage later)))
    have HH := HMbody _ _ endpoint k RAlt RK
    omega

/-- Below a least failed budget, a native structure target whose component
tail reaches one retained projection terminal must encounter another native
constructor root during that terminal's consuming body computation. The
terminal path itself is arbitrary. Global minimality excludes its relay
alternative; the resulting native cut has a strictly smaller target minimum
in the actual computed annotation context. -/
theorem pi_inert_structure_retained_terminal_native_root
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
    (HTsource : TypedSource (A :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage) (A :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]) target)
    (HR : PiInertStage D bodyStage (A :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]) target)
    (HC : ∃ fields, target = ProofShape.mkApps (.const info.ctorName []) fields ∧
      ScopedArgumentsCount (PiInertStage D bodyStage) (A :: Ω) ca fields [field, value])
    (SD : DomainSort Ω A u)
    (RDold : ScopedComputeCount (PiInertStage D domainStage) oldDomainCost Ω A A')
    (WI : ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id)
    (HFull : TypedSource Ω (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args))
    (HProj : TypedSource Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)))
    (RO : ScopedComputeCount (PiInertStage D n) cost Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)) out)
    (hbudget : 1+ca+cost ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j (A :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [originalField, originalValue]) endpoint →
      PiInertProjectionContinuation D Ω family 0 out (ProofShape.mkApps (.lam A' endpoint) args) k →
      1+ca+cost ≤ j+k) :
    PiInertPairTerminalNativeCut D Ω family info out (A' :: Ω) field value cost := by
  have RB : ScopedComputeCount (PiInertStage D bodyStage) ca (A :: Ω) target
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := by
    obtain ⟨fields, ET, RA⟩ := HC
    rw [ET]
    simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps RA
  have RP := (ScopedComputeCount.base HR).trans RB
  have HT := HTsource.pi_inert_compute heq hs RP.forget
  have HMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)) out → cost ≤ j := by
    intro later j RJ
    have HH := HM bodyStage (1+ca) _ j RP ⟨later, RJ⟩
    omega
  rcases pi_inert_retained_terminal_supply_or_native_root heq hs hi hu hp hf hz hshape hD
      hout hproj HT SD RDold WI HFull HProj RO HMin with ⟨smaller, hsmall, HCertificate⟩ | HCut
  · apply False.elim
    apply pi_inert_native_structure_no_component_supplies HLeast heq hs hi hp hf hz hadm
      hshape hout HTsource HE HC HCertificate (by omega)
    intro later j endpoint k RJ RK
    have HH := HM later j endpoint k RJ RK
    omega
  · exact HCut

end Lean4Lean.VEnv.Strengthening
