import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureObserverBoundary

/-! # Projected-field ancestry through successive component supplies

Before each endpoint map, factor the projected field into a major computation
and a zero/one terminal action, modulo administrative deletion. Only the
terminal action crosses that map. The major computation stays in its original
scope. For retained lambdas consumed by the next application, factor ancestry
again in the body context after the actual outer substitution. Rebuild that
second major computation inside the consuming shell, leaving the first major
computation before the retained frame. Repeating these constructions excludes
arbitrarily many such frames after a structure root.

Constructor roots and other retained binder executions above the observer
are not covered by this relay; they remain the next readout obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

private theorem retained_consumption_count
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A C)
    (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) body body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args [x]) :
    ScopedComputeCount (PiInertStage D n) (cd+cb+ca) Δ
      (ProofShape.mkApps (.lam A body) args) (body'.inst x) := by
  have R := ((ScopedComputeCount.lam RD RB).mkApps RX).trans
    (ScopedComputeCount.beta (BetaRed.beta (A := C) (b := body') (a := x)))
  simpa only [ProofShape.mkApps, Nat.add_zero] using R

/-- Factor projected-field ancestry on both sides of an ordinary substitution.
The old major path stays in the source context and the new major path stays in
the target context. Their combined count, plus the final zero/one projection
action, is bounded by the original ancestry and actual target field path.
This transports endpoint syntax and ordinary terminal selection, never a
guarded major computation through the substitution. -/
theorem pi_inert_projection_ancestry_substitution_count
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HSort : ControlTyping Δ (.proj family index source) (.sort u))
    (HD : AdministrativeHeadDeletion field lower)
    (RF : ScopedComputeCount (PiInertStage D fieldStage) fieldCost Δ
      (.proj family index source) lower)
    (W : ContextSubstitution Δ Θ τ)
    (HT : TypedSource Θ (field.subst τ))
    (RT : ScopedComputeCount (PiInertStage D targetStage) targetCost Θ (field.subst τ) nextField) :
    ∃ before after terminal cBefore cAfter terminalCost,
      ScopedComputeCount (PiInertStage D fieldStage) cBefore Δ source before ∧
      ScopedComputeCount (PiInertStage D targetStage) cAfter Θ (before.subst τ) after ∧
      ControlTyping Θ (.proj family index after) (.sort u) ∧
      AdministrativeHeadDeletion nextField terminal ∧
      cBefore+cAfter+terminalCost ≤ fieldCost+targetCost ∧
      ((terminalCost = 0 ∧ terminal = .proj family index after) ∨
        (terminalCost = 1 ∧ Primitive D (.proj family index after) terminal)) := by
  obtain ⟨before, firstTerminal, cBefore, HDfirst, RBefore, HF⟩ :=
    pi_inert_sorted_projection_terminal_frames_count heq hs HSort RF
  obtain ⟨nextLower, cNext, hcNext, RNext, HDnext⟩ :=
    ((HD.trans HDfirst).subst τ).compute heq hs HT RT
  have HSortBefore := HSort.compute
    (ErasedScopedPrimitiveCertificateDescent.descent
      (pi_inert_stage_certificate_descent heq hs fieldStage)) RBefore.proj.forget
  have HSortImage : ControlTyping Θ (.proj family index (before.subst τ)) (.sort u) := by
    simpa only [ProofShape.subst] using HSortBefore.subst W
  have finish (firstCost : Nat) (hfirst : cBefore+firstCost ≤ fieldCost)
      (RFirst : ScopedComputeCount (PiInertStage D targetStage) firstCost Θ
        (.proj family index (before.subst τ)) (firstTerminal.subst τ)) :
      ∃ after terminal cAfter terminalCost,
        ScopedComputeCount (PiInertStage D targetStage) cAfter Θ (before.subst τ) after ∧
        ControlTyping Θ (.proj family index after) (.sort u) ∧
        AdministrativeHeadDeletion nextField terminal ∧
        cBefore+cAfter+terminalCost ≤ fieldCost+targetCost ∧
        ((terminalCost = 0 ∧ terminal = .proj family index after) ∨
          (terminalCost = 1 ∧ Primitive D (.proj family index after) terminal)) := by
    obtain ⟨after, terminal, cAfter, HDlast, RAfter, HL⟩ :=
      pi_inert_sorted_projection_terminal_frames_count heq hs HSortImage (RFirst.trans RNext)
    have HSortAfter := HSortImage.compute
      (ErasedScopedPrimitiveCertificateDescent.descent
        (pi_inert_stage_certificate_descent heq hs targetStage)) RAfter.proj.forget
    rcases HL with ⟨ET, hc⟩ | ⟨RI, hc⟩
    · exact ⟨after, terminal, cAfter, 0, RAfter, HSortAfter, HDnext.trans HDlast,
        by omega, .inl ⟨rfl, ET⟩⟩
    · exact ⟨after, terminal, cAfter, 1, RAfter, HSortAfter, HDnext.trans HDlast,
        by omega, .inr ⟨rfl, RI⟩⟩
  have HX : ∃ after terminal cAfter terminalCost,
      ScopedComputeCount (PiInertStage D targetStage) cAfter Θ (before.subst τ) after ∧
      ControlTyping Θ (.proj family index after) (.sort u) ∧
      AdministrativeHeadDeletion nextField terminal ∧
      cBefore+cAfter+terminalCost ≤ fieldCost+targetCost ∧
      ((terminalCost = 0 ∧ terminal = .proj family index after) ∨
        (terminalCost = 1 ∧ Primitive D (.proj family index after) terminal)) := by
    rcases HF with ⟨ET, hc⟩ | ⟨RI, hc⟩
    · apply finish 0 (by omega)
      simpa only [ET, ProofShape.subst] using
        (ScopedComputeCount.beta (Step := PiInertStage D targetStage) (Δ := Θ)
          (BetaRed.refl (e := .proj family index (before.subst τ))))
    · exact finish 1 hc (.base (pi_inert_stage_core (.inl (.inl (.inl RI.subst)))))
  obtain ⟨after, terminal, cAfter, terminalCost, RAfter, HS, HDlast, hc, HF⟩ := HX
  exact ⟨before, after, terminal, cBefore, cAfter, terminalCost, RBefore, RAfter, HS, HDlast, hc, HF⟩

/-- An actual pair continuation whose application computations before reaching
the observer change only the two components, including retained lambdas consumed
in the next application with component body computation after its outer map.
Once in the observer's scope, the remaining execution is unrestricted. Its
predicate is the original raw predicate, not a restriction on competitors. -/
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
  | retained : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
      DomainSort Δ A u → ScopedComputeCount (PiInertStage D domainStage) oldDomainCost Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      TypedSource Δ (ProofShape.mkApps
        (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args) →
      PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps
        (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift]))
        (args.map (·.subst τ) ++ pending)) →
      ScopedComputeCount (PiInertStage D n) cd Θ (A'.subst τ) C →
      ScopedArgumentsCount (PiInertStage D n) (A'.subst τ :: Θ) cb
        [field.subst τ.lift, value.subst τ.lift] [nextField, nextValue] →
      ScopedArgumentsCount (PiInertStage D n) Θ ca (args.map (·.subst τ) ++ pending) [x] →
      PiInertPairComponentSupplyRun D Ω family info out Θ K (nextField.inst x) (nextValue.inst x) ck frames →
      PiInertPairComponentSupplyRun D Ω family info out (A :: Δ)
        (fun body k => PiInertApplicationContinuation D Θ τ pending K
          (ProofShape.mkApps (.lam A' body) args) k)
        field value (cd+cb+ca+ck) (frames+2)

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
  | @retained A Δ field value u domainStage oldDomainCost A' args Θ τ pending n cd C cb nextField nextValue ca x K ck frames
      HT SD RD WI HWrapped W HFull RDomain RA RX _ ih =>
    have RB : ScopedComputeCount (PiInertStage D n) cb (A'.subst τ :: Θ)
        (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift])
        (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
      simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps RA
    have RAll := retained_consumption_count RDomain RB RX
    have RAll' : ScopedComputeCount (PiInertStage D n) (cd+cb+ca) Θ
        (ProofShape.mkApps
          ((ProofShape.mkApps (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args).subst τ) pending)
        (ProofShape.mkApps (.const info.ctorName []) [nextField.inst x, nextValue.inst x]) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.subst_mkApps, ProofShape.subst,
        List.map_cons, List.map_nil, ProofShape.mkApps_append, ProofShape.mkApps] using RAll
    have HNext : TypedSource Θ (ProofShape.mkApps
        ((ProofShape.mkApps (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args).subst τ) pending) := by
      simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil,
        ProofShape.mkApps_append] using HFull
    have HApp := PiInertProjectionRunFrames.application HWrapped W HNext RAll' ih
    simpa only [Nat.add_assoc] using PiInertProjectionRunFrames.retained HT SD RD WI HApp

/-- An actual consuming retained application enters the relay. Its arguments
may be split between the retained frame and the next application, whose outer
endpoint map is retained, including its action underneath the lambda binder.
Typing the computed full pair forces the post-beta residual arguments to be
empty. The original raw predicate, including that split, is preserved exactly.
The premise on the actual body is component computation; constructor roots
inside that body are not assumed to satisfy it. -/
theorem PiInertPairComponentSupplyRun.retained_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (SD : DomainSort Δ A u)
    (RD : ScopedComputeCount (PiInertStage D domainStage) oldDomainCost Δ A A')
    (WI : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id)
    (HWrapped : TypedSource Δ (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args))
    (W : PiInertEndpointMap Δ Θ τ)
    (HFull : TypedSource Θ (ProofShape.mkApps
      (.lam (A'.subst τ) (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift]))
      (args.map (·.subst τ) ++ pending)))
    (RDomain : ScopedComputeCount (PiInertStage D n) cd Θ (A'.subst τ) C)
    (RA : ScopedArgumentsCount (PiInertStage D n) (A'.subst τ :: Θ) cb
      [field.subst τ.lift, value.subst τ.lift] [nextField, nextValue])
    (RX : ScopedArgumentsCount (PiInertStage D n) Θ ca (args.map (·.subst τ) ++ pending) (x :: rest))
    (HK : PiInertPairComponentSupplyRun D Ω family info out Θ K
      (nextField.inst x) (nextValue.inst x) ck frames) :
    rest = [] ∧ PiInertPairComponentSupplyRun D Ω family info out (A :: Δ)
      (fun body k => PiInertApplicationContinuation D Θ τ pending K
        (ProofShape.mkApps (.lam A' body) args) k)
      field value (cd+cb+ca+ck) (frames+2) := by
  have RB : ScopedComputeCount (PiInertStage D n) cb (A'.subst τ :: Θ)
      (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift])
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
    simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps RA
  have HTbody := (ScopedHole.lamBody (A'.subst τ) .hole).typed (typed_spine_head HFull)
  have HTend := HTbody.pi_inert_compute heq hs RB.forget
  have WX : ContextSubstitution (A'.subst τ :: Θ) Θ (ProofShape.Subst.one x) :=
    typed_lambda_argument_map heq hs HFull RX
  have RLambda := (ScopedComputeCount.lam RDomain RB).mkApps RX
  have RBeta : ScopedComputeCount (PiInertStage D n) 0 Θ
      (ProofShape.mkApps (.lam C (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) (x :: rest))
      (ProofShape.mkApps ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).inst x) rest) := by
    simpa only [ProofShape.mkApps, Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D n)
        (BetaRed.beta (A := C) (b := ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) (a := x))).mkApps
        (ScopedArgumentsCount.refl (args := rest))
  have HNext := HFull.pi_inert_compute heq hs (RLambda.trans RBeta).forget
  have HNext' : TypedSource Θ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).subst (ProofShape.Subst.one x)) rest) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HNext
  have ERest := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HTend WX HNext'
  subst rest
  exact ⟨rfl, .retained HT SD RD WI HWrapped W HFull RDomain RA RX HK⟩

/-- Relay a computed projection field through any finite component-supply
chain. Administrative wrappers may survive at every intermediate field.
Leastness is used only for the final observer-scope pair and the fixed output.
Each guarded major path remains before the endpoint map where it was obtained;
only ordinary terminal selection and deletion syntax cross the map. Retained
consumption factors ancestry before the outer map and again in its target
body context. The second major computation rebuilds the consuming shell while
the first stays before the retained frame. Domain, body and argument costs
remain within their combined original budget. -/
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

  | @retained A Δ field value binderU domainStage oldDomainCost A' args Θ τ pending n cd C cb nextField nextValue ca x K ck frames
      HT SD RD WI HWrapped W HFull RDomain RA RX HK ih =>
    have HTbody := (ScopedHole.lamBody (A'.subst τ) .hole).typed (typed_spine_head HFull)
    have HTfield : TypedSource (A'.subst τ :: Θ) (field.subst τ.lift) :=
      (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) (value.subst τ.lift)).typed HTbody
    have WBody : ContextSubstitution (A :: Δ) (A'.subst τ :: Θ) τ.lift := by
      intro Γ₀ hΓ₀ EΓ₀
      simpa only [ProofShape.Subst.comp, ProofShape.Subst.id, ProofShape.subst] using
        ContextSubstitution.comp WI (ContextSubstitution.cons W.interpretation) hΓ₀ EΓ₀
    have WX : ContextSubstitution (A'.subst τ :: Θ) Θ (ProofShape.Subst.one x) :=
      typed_lambda_argument_map heq hs HFull RX
    let bodyCost := cb
    have hbodyCost : cb = bodyCost := rfl
    cases RA with
    | cons RField rest =>
      cases rest with
      | cons RValue last =>
        cases last
        obtain ⟨before, after, terminal, cBefore, cAfter, terminalCost,
          RBefore, RAfter, HSortAfter, HDafter, hancestry, HF⟩ :=
          pi_inert_projection_ancestry_substitution_count heq hs HSort HD RF WBody HTfield RField
        have HSortNext : ControlTyping Θ (.proj family 0 (after.subst (ProofShape.Subst.one x))) (.sort u) := by
          simpa only [ProofShape.subst] using HSortAfter.subst WX
        have HDimage : AdministrativeHeadDeletion (nextField.inst x) (terminal.subst (ProofShape.Subst.one x)) := by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HDafter.subst (ProofShape.Subst.one x)
        have RTerm : ScopedComputeCount (PiInertStage D n) terminalCost Θ
            (.proj family 0 (after.subst (ProofShape.Subst.one x))) (terminal.subst (ProofShape.Subst.one x)) := by
          rcases HF with ⟨rfl, ET⟩ | ⟨rfl, RI⟩
          · simpa only [ET, ProofShape.subst] using
              (ScopedComputeCount.beta (Step := PiInertStage D n) (Δ := Θ)
                (BetaRed.refl (e := .proj family 0 (after.subst (ProofShape.Subst.one x)))))
          · exact .base (pi_inert_stage_core (.inl (.inl (.inl RI.subst))))
        obtain ⟨later, j, endpoint, k, hcost, RJ, RK⟩ := ih (by omega) HSortNext HDimage RTerm
        have RWrap : ScopedComputeCount (PiInertStage D n) (cd+cAfter+ca) Θ
            (ProofShape.mkApps (.lam (A'.subst τ) (before.subst τ.lift)) (args.map (·.subst τ) ++ pending))
            (after.subst (ProofShape.Subst.one x)) := by
          simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
            retained_consumption_count RDomain RAfter RX
        have RAlt := (RWrap.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
        refine ⟨fieldStage, cBefore, before, cd+cAfter+ca+j+k, by omega, RBefore,
          max n later, cd+cAfter+ca+j, endpoint, k, rfl, ?_, RK⟩
        simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RAlt

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
retained execution outside the certified consuming case remains to be handled. -/
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
Reading intervening constructor roots or other retained executions is still open. -/
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
