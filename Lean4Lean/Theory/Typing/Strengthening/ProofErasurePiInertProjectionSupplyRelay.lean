import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureObserverBoundary

/-! # Projected-field ancestry through successive component supplies

Before each endpoint map, factor the projected field into a major computation
and a zero/one terminal action, modulo administrative deletion. Only the
terminal action crosses that map. The major computation stays in its original
scope. For retained lambdas, factor ancestry again in the body context after
the actual outer substitution. Rebuild the second major computation inside
the actual shell, leaving the first before the retained frame. If the lambda
survives, recurse at its computed body with the new wrapper predicate and one
fewer frame. If it is consumed, recurse after beta. Arbitrary finite alternation
of these cases is excluded after a structure root.

Direct terminal consumption with component body computation also enters the
relay through a zero-cost identity frame and raw predicate equivalence.
Constructor roots, nested retained prefixes, and classification of arbitrary
terminal projection paths still require treatment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_lambda_argument_map typed_lambda_readout
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- Inserting an identity application before a final projection does not change
its predicate at any raw source or count. This includes competitors with no
typing witness: forward composition uses projection congruence, and the reverse
direction takes a zero-cost reflexive body path. -/
theorem pi_inert_projection_identity_application_iff :
    PiInertApplicationContinuation D Ω ProofShape.Subst.id []
      (PiInertProjectionContinuation D Ω family index out) source cost ↔
    PiInertProjectionContinuation D Ω family index out source cost := by
  constructor
  · rintro ⟨n, j, endpoint, k, hc, RJ, later, RK⟩
    have RJ' : ScopedComputeCount (PiInertStage D n) j Ω source endpoint := by
      simpa only [ProofShape.subst_id, ProofShape.mkApps] using RJ
    exact ⟨max n later, hc ▸
      (RJ'.mono (pi_inert_stage_mono (Nat.le_max_left n later))).proj.trans
        (RK.mono (pi_inert_stage_mono (Nat.le_max_right n later)))⟩
  · rintro ⟨n, R⟩
    refine ⟨n, 0, source, cost, by omega, ?_, n, R⟩
    simpa only [ProofShape.subst_id, ProofShape.mkApps] using
      (ScopedComputeCount.beta (Step := PiInertStage D n) (Δ := Ω) (BetaRed.refl (e := source)))

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
the observer change only the two components. Retained lambdas can be consumed
or survive the next application; in the latter case their computed body is
relayed under the new wrapper predicate with one fewer frame. Once in the
observer's scope, the remaining execution is unrestricted. The raw competitor
predicate is unchanged in every case. -/
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
  | delayed : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) [field, value]) →
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
      ScopedArgumentsCount (PiInertStage D n) Θ ca (args.map (·.subst τ) ++ pending) nextArgs →
      PiInertProjectionRunFrames D Ω family 0 out Θ K
        (ProofShape.mkApps (.lam C (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) nextArgs) ck frames →
      PiInertPairComponentSupplyRun D Ω family info out (A'.subst τ :: Θ)
        (fun body k => K (ProofShape.mkApps (.lam C body) nextArgs) k) nextField nextValue ck (frames+1) →
      PiInertPairComponentSupplyRun D Ω family info out (A :: Δ)
        (fun body k => PiInertApplicationContinuation D Θ τ pending K
          (ProofShape.mkApps (.lam A' body) args) k)
        field value (cd+cb+ca+ck) (frames+2)

/-- Relabel a supply certificate by a pointwise equivalent raw predicate.
The equivalence covers every candidate and count; it is not restricted to the
selected typed execution. Primitive cost and certificate frames are unchanged. -/
theorem PiInertPairComponentSupplyRun.congr_predicate
    (H : PiInertPairComponentSupplyRun D Ω family info out Δ K field value ck frames)
    (HE : ∀ e k, K e k ↔ L e k) :
    PiInertPairComponentSupplyRun D Ω family info out Δ L field value ck frames := by
  have E : K = L := by
    funext e k
    exact propext (HE e k)
  exact E ▸ H

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
  | @delayed A Δ field value u domainStage oldDomainCost A' args Θ τ pending n cd C cb nextField nextValue ca nextArgs K ck frames
      HT SD RD WI HWrapped W HFull RDomain RA RX HK _ _ =>
    have RB : ScopedComputeCount (PiInertStage D n) cb (A'.subst τ :: Θ)
        (ProofShape.mkApps (.const info.ctorName []) [field.subst τ.lift, value.subst τ.lift])
        (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
      simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps RA
    have RAll := (ScopedComputeCount.lam RDomain RB).mkApps RX
    have RAll' : ScopedComputeCount (PiInertStage D n) (cd+cb+ca) Θ
        (ProofShape.mkApps
          ((ProofShape.mkApps (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args).subst τ) pending)
        (ProofShape.mkApps (.lam C (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) nextArgs) := by
      simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons,
        List.map_nil, ProofShape.mkApps_append] using RAll
    have HNext : TypedSource Θ (ProofShape.mkApps
        ((ProofShape.mkApps (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args).subst τ) pending) := by
      simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil,
        ProofShape.mkApps_append] using HFull
    have HApp := PiInertProjectionRunFrames.application HWrapped W HNext RAll' HK
    simpa only [Nat.add_assoc] using PiInertProjectionRunFrames.retained HT SD RD WI HApp

/-- A surviving lambda supplies the actual body continuation used by delayed
relay. Typing derives its domain sort and the computed annotation's identity
interpretation. The body stays under the original annotation, its raw
continuation wraps every candidate with the actual new annotation and arguments,
and precisely one retained frame is added to the selected outer tail. -/
theorem pi_inert_retained_survival_body_frames
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A C)
    (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) body nextBody)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K
      (ProofShape.mkApps (.lam C nextBody) nextArgs) ck frames) :
    PiInertProjectionRunFrames D Ω family index out (A :: Δ)
      (fun e k => K (ProofShape.mkApps (.lam C e) nextArgs) k) nextBody ck (frames+1) := by
  have HTlam := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody A .hole).typed HTlam
  obtain ⟨u, _, _, _, SD, _, _, _⟩ := typed_lambda_readout heq hs HTlam
    (ScopedComputeCount.beta (Step := PiInertStage D n) (Δ := Δ)
      (BetaRed.refl (e := .lam A body)))
  exact .retained (HTbody.pi_inert_compute heq hs RB.forget) SD RD
    (pi_inert_retained_frame_interpretation heq hs SD RD) HK

/-- Refocus an actual surviving-lambda minimum at its original body with exact
unspent body-plus-tail cost. The domain and argument paths are fixed only when
reconstructing competitors, so all raw body paths and finite stages remain
available. In a retained-frame/application pair the new frame count is one
smaller, even when all primitive counts are zero. -/
theorem pi_inert_retained_survival_body_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.mkApps (.lam A body) args))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A C)
    (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) body nextBody)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args nextArgs)
    (HK : PiInertProjectionRunFrames D Ω family index out Δ K
      (ProofShape.mkApps (.lam C nextBody) nextArgs) ck frames)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.lam A body) args) endpoint → K endpoint k → cd+cb+ca+ck ≤ j+k) :
    PiInertProjectionFrameMinimum D Ω family index out (A :: Δ) body (cb+ck) (frames+1) := by
  have HTbody := (ScopedHole.lamBody A .hole).typed (typed_spine_head HT)
  refine ⟨(fun e k => K (ProofShape.mkApps (.lam C e) nextArgs) k), n, cb, ck, nextBody,
    HTbody, RB, pi_inert_retained_survival_body_frames heq hs HT RD RB HK, rfl, ?_⟩
  intro later j endpoint k RJ RK
  have RAlt := (ScopedComputeCount.lam
    (RD.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))).mkApps
    (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
  have HH := HM (max n later) (cd+j+ca) (ProofShape.mkApps (.lam C endpoint) nextArgs) k RAlt RK
  omega

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

/-- A retained lambda consumed inside the terminal projection enters the same
supply relay when its body computation changes only the pair components. Its
remaining observer-scope projection path is unrestricted. An identity frame
is inserted at zero primitive cost and then its predicate is relabelled by
the raw equivalence, so the resulting certificate has two frames rather than
the original terminal's one. Structure separation allows arbitrary competing
frame counts, and its primitive-cost comparison is unchanged. Closed-pair
typing derives the absence of residual arguments after the actual beta. -/
theorem PiInertPairComponentSupplyRun.retained_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (HT : TypedSource (A :: Ω) (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (SD : DomainSort Ω A u)
    (RD : ScopedComputeCount (PiInertStage D domainStage) oldDomainCost Ω A A')
    (WI : ContextSubstitution (A :: Ω) (A' :: Ω) ProofShape.Subst.id)
    (HFull : TypedSource Ω (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args))
    (HProj : TypedSource Ω (.proj family 0 (ProofShape.mkApps
      (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)))
    (RDomain : ScopedComputeCount (PiInertStage D n) cd Ω A' C)
    (RA : ScopedArgumentsCount (PiInertStage D n) (A' :: Ω) cb [field, value] [nextField, nextValue])
    (RX : ScopedArgumentsCount (PiInertStage D n) Ω ca args (x :: rest))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) ck Ω
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [nextField.inst x, nextValue.inst x])) out) :
    rest = [] ∧ PiInertPairComponentSupplyRun D Ω family info out (A :: Ω)
      (fun body k => PiInertProjectionContinuation D Ω family 0 out
        (ProofShape.mkApps (.lam A' body) args) k)
      field value (cd+cb+ca+ck) 2 := by
  have RB : ScopedComputeCount (PiInertStage D n) cb (A' :: Ω)
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) := by
    simpa only [Nat.zero_add] using (ScopedComputeCount.beta BetaRed.refl).mkApps RA
  have HTbody := (ScopedHole.lamBody A' .hole).typed (typed_spine_head HFull)
  have HTend := HTbody.pi_inert_compute heq hs RB.forget
  have WX : ContextSubstitution (A' :: Ω) Ω (ProofShape.Subst.one x) :=
    typed_lambda_argument_map heq hs HFull RX
  have RLambda := (ScopedComputeCount.lam RDomain RB).mkApps RX
  have RBeta : ScopedComputeCount (PiInertStage D n) 0 Ω
      (ProofShape.mkApps (.lam C (ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue])) (x :: rest))
      (ProofShape.mkApps ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).inst x) rest) := by
    simpa only [ProofShape.mkApps, Nat.zero_add] using
      (ScopedComputeCount.beta (Step := PiInertStage D n)
        (BetaRed.beta (A := C) (b := ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]) (a := x))).mkApps
        (ScopedArgumentsCount.refl (args := rest))
  have HNext := HFull.pi_inert_compute heq hs (RLambda.trans RBeta).forget
  have HNext' : TypedSource Ω (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) [nextField, nextValue]).subst (ProofShape.Subst.one x)) rest) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HNext
  have ERest := TypedSource.closed_constructor_image_pending_nil hi hp hz (by simp [hf]) HTend WX HNext'
  subst rest
  have RAll : ScopedComputeCount (PiInertStage D n) (cd+cb+ca) Ω
      (ProofShape.mkApps (.lam A' (ProofShape.mkApps (.const info.ctorName []) [field, value])) args)
      (ProofShape.mkApps (.const info.ctorName []) [nextField.inst x, nextValue.inst x]) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.subst_mkApps, ProofShape.subst,
      List.map_cons, List.map_nil, ProofShape.mkApps] using retained_consumption_count RDomain RB RX
  have HTimage := HFull.pi_inert_compute heq hs RAll.forget
  have HPimage := HProj.pi_inert_compute heq hs RAll.proj.forget
  have HK : PiInertPairComponentSupplyRun D Ω family info out Ω
      (PiInertProjectionContinuation D Ω family 0 out) (nextField.inst x) (nextValue.inst x) ck 0 :=
    .observer (.projection HTimage HPimage RObserve)
  have H : PiInertPairComponentSupplyRun D Ω family info out (A :: Ω)
      (fun body k => PiInertApplicationContinuation D Ω ProofShape.Subst.id []
        (PiInertProjectionContinuation D Ω family 0 out) (ProofShape.mkApps (.lam A' body) args) k)
      field value (cd+cb+ca+ck) 2 := by
    apply PiInertPairComponentSupplyRun.retained HT SD RD WI HFull
      (.identity ContextRenaming.identity.interpretation)
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, List.map_id_fun', List.append_nil, id_eq] using HFull
    · simpa only [ProofShape.subst_id] using RDomain
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id] using RA
    · simpa only [ProofShape.subst_id, List.map_id_fun', List.append_nil, id_eq] using RX
    · exact HK
  exact ⟨rfl, H.congr_predicate fun _ _ => pi_inert_projection_identity_application_iff⟩

/-- Relay a computed projection field through any finite component-supply
chain. Administrative wrappers may survive at every intermediate field.
Leastness is used only for the final observer-scope pair and the fixed output.
Each guarded major path remains before the endpoint map where it was obtained;
only ordinary terminal selection and deletion syntax cross the map. Retained
execution factors ancestry before the outer map and again in its target body
context. The second major computation rebuilds the actual shell while the
first stays before the retained frame. A surviving lambda recurses before
beta with its exact updated wrapper predicate. Domain, body and argument
costs remain within their combined original budget. -/
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

  | @delayed A Δ field value binderU domainStage oldDomainCost A' args Θ τ pending n cd C cb nextField nextValue ca nextArgs K ck frames
      HT SD RD WI HWrapped W HFull RDomain RA RX HK HBody ih =>
    have HTbody := (ScopedHole.lamBody (A'.subst τ) .hole).typed (typed_spine_head HFull)
    have HTfield : TypedSource (A'.subst τ :: Θ) (field.subst τ.lift) :=
      (ScopedHole.appFn (.appArg (.const info.ctorName []) .hole) (value.subst τ.lift)).typed HTbody
    have WBody : ContextSubstitution (A :: Δ) (A'.subst τ :: Θ) τ.lift := by
      intro Γ₀ hΓ₀ EΓ₀
      simpa only [ProofShape.Subst.comp, ProofShape.Subst.id, ProofShape.subst] using
        ContextSubstitution.comp WI (ContextSubstitution.cons W.interpretation) hΓ₀ EΓ₀
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
        have RTerm : ScopedComputeCount (PiInertStage D n) terminalCost (A'.subst τ :: Θ)
            (.proj family 0 after) terminal := by
          rcases HF with ⟨rfl, rfl⟩ | ⟨rfl, RI⟩
          · exact .beta .refl
          · exact .base (pi_inert_stage_core (.inl (.inl (.inl RI))))
        obtain ⟨later, j, endpoint, k, hcost, RJ, RK⟩ := ih (by omega) HSortAfter HDafter RTerm
        have RBodyAlt := (RAfter.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
        have RWrap := (ScopedComputeCount.lam
          (RDomain.mono (pi_inert_stage_mono (Nat.le_max_left n later))) RBodyAlt).mkApps
          (RX.mono (pi_inert_stage_mono (Nat.le_max_left n later)))
        refine ⟨fieldStage, cBefore, before, cd+(cAfter+j)+ca+k, by omega, RBefore,
          max n later, cd+(cAfter+j)+ca, ProofShape.mkApps (.lam C endpoint) nextArgs, k, rfl, ?_, RK⟩
        simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RWrap

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
retained execution outside the certified consuming/surviving cases remains
to be handled. -/
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
