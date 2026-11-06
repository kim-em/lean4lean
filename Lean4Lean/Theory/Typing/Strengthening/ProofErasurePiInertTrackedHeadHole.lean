import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRigidTail

/-! # Tracked head losses exclude structure eta through wrappers

A selected hole follows only function positions, retained lambda bodies and
identity payloads. Rigid result typing propagates outward through precisely
these wrappers, so a sort-ending execution excludes structure recovery at
its selected head-losing root, even when that root is under binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- The hole follows the tracked constant, never an arbitrary argument or
annotation. Identity payloads are the only admitted argument positions. -/
inductive TrackedHeadHole : {Δ Θ : List ProofShape} → ScopedHole Δ Θ → Prop where
  | hole : TrackedHeadHole (.hole : ScopedHole Δ Δ)
  | appFn {C : ScopedHole Δ Θ} : TrackedHeadHole C → TrackedHeadHole (.appFn C x)
  | lamBody {C : ScopedHole (A :: Δ) Θ} : TrackedHeadHole C → TrackedHeadHole (.lamBody A C)
  | identity {C : ScopedHole Δ Θ} : TrackedHeadHole C → TrackedHeadHole (.appArg (.lam A (.bvar 0)) C)

/-- A rigid result at the selected root forces a rigid result for the whole
typed wrapper. Identity payloads use actual beta equality backwards; no
recovery or guarded path is transported across a binder. -/
theorem TrackedHeadHole.rigid_tail_plug
    {C : ScopedHole Δ Θ}
    (hstep : ErasedScopedPrimitiveDescent Step) (hr : env.Rigid c)
    (H : TrackedHeadHole C) (HT : TypedSource Δ (C.plug a))
    (HA : RigidTailTyping Θ a c) : RigidTailTyping Δ (C.plug a) c := by
  induction H with
  | hole => exact HA
  | @appFn Δ Θ x C H ih =>
    exact (ih ((ScopedHole.appFn .hole x).typed HT) HA).app hr HT
  | lamBody H ih =>
    exact (ih ((ScopedHole.lamBody _ .hole).typed HT) HA).lam HT
  | @identity Δ Θ A C H ih =>
    have HP := ih ((ScopedHole.appArg (.lam A (.bvar 0)) .hole).typed HT) HA
    apply HP.compute_backward hstep HT
    simpa only [ScopedHole.plug, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.Subst.cons] using
      (ScopedCompute.beta (Step := Step) (Δ := _) (BetaRed.beta (A := A) (b := .bvar 0) (a := C.plug a)))

/-- A counted local loss of the tracked head. Both surrounding paths keep
their exact scopes and occurrence counts; the hole may lie under retained
binders or inside the payload of an identity application. -/
def TrackedWrappedHeadCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (source out : ProofShape) (cost : Nat) : Prop :=
  ∃ Θ a b, ∃ C : ScopedHole Δ Θ, ∃ cp ct,
    TrackedHeadHole C ∧ cp+1+ct = cost ∧ ScopedComputeCount (PiInertStage D n) cp Δ source (C.plug a) ∧
    PiInertStage D n Θ a b ∧ WrappedConstHead c a ∧ ¬ WrappedConstHead c b ∧
    ScopedComputeCount (PiInertStage D n) ct Δ (C.plug b) out

/-- Losing the wrapped head in an actual counted path selects a primitive
that loses it. Beta cannot be selected. Application arguments and annotations
are skipped unless the argument is the tracked identity payload. -/
theorem ProofShape.ScopedComputeCount.tracked_wrapped_head_cut
    (R : ScopedComputeCount (PiInertStage D n) cost Δ source out)
    (H : WrappedConstHead c source) (HN : ¬ WrappedConstHead c out) :
    TrackedWrappedHeadCut D n Δ c source out cost := by
  classical
  induction R with
  | base HR => exact ⟨_, _, _, .hole, 0, 0, .hole, rfl, .beta .refl, HR, H, HN, .beta .refl⟩
  | beta R => exact (HN (H.beta R)).elim
  | trans R₁ R₂ ih₁ ih₂ =>
    rename_i m Δ a mid j out
    by_cases HM : WrappedConstHead c mid
    · obtain ⟨Θ, a, b, C, cp, ct, Htrack, hc, RP, HR, HS, HN, RT⟩ := ih₂ HM HN
      exact ⟨Θ, a, b, C, _, ct, Htrack, by omega, R₁.trans RP, HR, HS, HN, RT⟩
    · obtain ⟨Θ, a, b, C, cp, ct, Htrack, hc, RP, HR, HS, HN, RT⟩ := ih₁ H HM
      exact ⟨Θ, a, b, C, cp, _, Htrack, by omega, RP, HR, HS, HN, RT.trans R₂⟩
  | app RF RX ihf ihx =>
    rename_i m Δ f f' j x x'
    cases H with
    | app H =>
      obtain ⟨Θ, a, b, C, cp, ct, Htrack, hc, RP, HR, HS, HN, RT⟩ := ihf H (fun HH => HN (.app HH))
      refine ⟨Θ, a, b, .appFn C x, cp, ct+j, .appFn Htrack, by omega, ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug, Nat.add_zero] using RP.app (ScopedComputeCount.beta BetaRed.refl)
      · simpa only [ScopedHole.plug] using RT.app RX
    | identity H =>
      obtain ⟨A', rfl, _⟩ := RF.forget.pi_inert_identity_lam
      obtain ⟨Θ, a, b, C, cp, ct, Htrack, hc, RP, HR, HS, HN, RT⟩ := ihx H (fun HH => HN (.identity HH))
      refine ⟨Θ, a, b, .appArg (.lam A' (.bvar 0)) C, m+cp, ct, .identity Htrack, by omega,
        ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug] using RF.app RP
      · simpa only [ScopedHole.plug, Nat.zero_add] using ScopedComputeCount.app (ScopedComputeCount.beta BetaRed.refl) RT
  | proj => cases H
  | lam RA RB ihA ihb =>
    rename_i m Δ A A' j body body'
    cases H with
    | lam H =>
      obtain ⟨Θ, a, b, C, cp, ct, Htrack, hc, RP, HR, HS, HN, RT⟩ := ihb H (fun HH => HN (.lam HH))
      refine ⟨Θ, a, b, .lamBody A C, cp, m+ct, .lamBody Htrack, by omega, ?_, HR, HS, HN, ?_⟩
      · simpa only [ScopedHole.plug, Nat.zero_add] using ScopedComputeCount.lam (ScopedComputeCount.beta BetaRed.refl) RP
      · simpa only [ScopedHole.plug] using RA.lam RT
  | forallE => cases H


/-- Forget only the restriction on the surrounding hole. -/
theorem TrackedWrappedHeadCut.forget
    (H : TrackedWrappedHeadCut D n Δ c source out cost) :
    WrappedHeadCut D n Δ c source out cost := by
  obtain ⟨Θ, a, b, C, cp, ct, _, hc, RP, HR, HS, HN, RT⟩ := H
  exact ⟨Θ, a, b, C, cp, ct, hc, RP, HR, HS, HN, RT⟩

/-- An actual selected path whose source cannot have any rigid-tail assigned
type. Its tracked hole permits this negative fact to constrain the root. -/
def TypedNonrigidHeadLoss (D : Definitions) (c : Name) (budget : Nat) : Prop :=
  ∃ Δ n cost source endpoint, cost ≤ budget ∧ TypedSource Δ source ∧
    (∀ r, env.Rigid r → ¬ RigidTailTyping Δ source r) ∧
    TrackedWrappedHeadCut D n Δ c source endpoint cost

/-- Retain the old typed head-loss witness with its original cost bound. -/
theorem TypedNonrigidHeadLoss.forget (H : TypedNonrigidHeadLoss D c budget) :
    TypedWrappedHeadLoss D c budget := by
  obtain ⟨Δ, n, cost, source, endpoint, hc, HT, _, Hcut⟩ := H
  exact ⟨Δ, n, cost, source, endpoint, hc, HT, Hcut.forget⟩

/-- A mixed execution ending at a sort selects a tracked loss whose local
path source has no rigid-tail typing. This follows from its actual remaining
execution and does not assume an intermediate endpoint is exposed. -/
theorem PiInertTypedContinuationRun.tracked_head_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck)
    (HH : WrappedConstHead ``Eq.rec e) (HE : CarrierExposure out)
    (HC : ControlTyping Ω out (.sort u)) : TypedNonrigidHeadLoss D ``Eq.rec ck := by
  classical
  induction H with
  | terminal => exact (HH.eq_not_exposed heq HE).elim
  | application HToriginal W HT R HK ih =>
    rename_i Δ e Θ τ args n cs e' K ck
    have HS := (HH.subst τ).mkApps args
    by_cases HH' : WrappedConstHead ``Eq.rec e'
    · obtain ⟨Ξ, m, cost, source, endpoint, hc, HT, HN, Hcut⟩ := ih HH'
      exact ⟨Ξ, m, cost, source, endpoint, by omega, HT, HN, Hcut⟩
    · refine ⟨Θ, n, cs, _, e', by omega, HT, ?_, R.tracked_wrapped_head_cut HS HH'⟩
      intro r hr HTail
      exact HC.no_rigid_tail hr (HK.rigid_tail heq hs hr (HTail.compute
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R.forget))
  | retained HT SD RD WI HK ih => exact ih ((WrappedConstHead.lam HH).mkApps _)

/-- The initial body or the actual continuation supplies a tracked loss,
with nonrigidity derived from the same sort-ending minimum. -/
theorem PiInertTypedContinuationMinimum.tracked_head_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost)
    (HH : WrappedConstHead ``Eq.rec source) (HE : CarrierExposure out)
    (HC : ControlTyping Ω out (.sort u)) : TypedNonrigidHeadLoss D ``Eq.rec cost := by
  classical
  have HNR : ∀ r, env.Rigid r → ¬ RigidTailTyping Δ source r :=
    fun _ hr => H.no_rigid_tail heq hs HC hr
  obtain ⟨K, n, cb, ck, e, HT, R, HR, hc, _⟩ := H
  by_cases HH' : WrappedConstHead ``Eq.rec e
  · obtain ⟨Ξ, m, localCost, localSource, endpoint, hcost, HT, HN, Hcut⟩ :=
      HR.tracked_head_loss heq hs HH' HE HC
    exact ⟨Ξ, m, localCost, localSource, endpoint, by omega, HT, HN, Hcut⟩
  · exact ⟨Δ, n, cb, source, e, by omega, HT, HNR,
      R.tracked_wrapped_head_cut HH HH'⟩

/-- The exact selected constant-spine root excludes native structure
recovery at every finite stage. A hypothetical recovery assigns a rigid
family at the root, hence throughout the tracked wrapper, and then backwards
along the actual typed prefix, contradicting the retained local nonrigidity. -/
theorem TypedNonrigidHeadLoss.root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : TypedNonrigidHeadLoss D c budget) :
    ∃ Δ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Δ Θ,
      cp+1+ct ≤ budget ∧ TrackedHeadHole C ∧ TypedSource Δ source ∧
      ScopedComputeCount (PiInertStage D n) cp Δ source (C.plug (ProofShape.mkApps (.const c ls) args)) ∧
      TypedSource Θ (ProofShape.mkApps (.const c ls) args) ∧
      PiInertStage D n Θ (ProofShape.mkApps (.const c ls) args) target ∧
      ¬ WrappedConstHead c target ∧
      (∀ k, ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ
        (ProofShape.mkApps (.const c ls) args) target) ∧
      ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint := by
  obtain ⟨Δ, n, cost, source, endpoint, hc, HT, HNR, Θ, a, b, C, cp, ct,
    Htrack, hcost, RP, HR, HS, HN, RT⟩ := H
  have HTwhole := HT.pi_inert_compute heq hs RP.forget
  have HTroot := C.typed HTwhole
  obtain ⟨ls, args, rfl⟩ := HS.primitive_source HR
  refine ⟨Δ, Θ, n, source, endpoint, ls, args, b, cp, ct, C,
    by omega, Htrack, HT, RP, HTroot, HR, HN, ?_, RT⟩
  intro k Hstruct
  obtain ⟨r, hr, HRigid⟩ := rigid_tail_of_native_structure
    (erased_static_structure_eta_expansion_stage_descent heq hs k)
    HTroot ProofShape.const_spine_ne_proof Hstruct
  have hstep : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent
    (pi_inert_stage_certificate_descent heq hs n)
  exact HNR r hr ((Htrack.rigid_tail_plug hstep hr HTwhole HRigid).compute_backward hstep HT RP.forget)

/-- A failure of target completion at a selected head loss that additionally
retains the tracked hole and excludes all finite-stage native structure
recoveries. The missing obligation is still argument ancestry through the
actual wrapper history; this predicate does not assert it is impossible. -/
def NonstructuralEqHeadCompletionFailure (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (budget : Nat) : Prop :=
  ∃ Ξ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Ξ Θ,
    cp+1+ct ≤ budget ∧ TrackedHeadHole C ∧ TypedSource Ξ source ∧
    ScopedComputeCount (PiInertStage D n) cp Ξ source (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)) ∧
    TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∧
    ¬ WrappedConstHead ``Eq.rec target ∧
    (∀ k, ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) ∧
    ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint ∧
    ¬ EqHeadCompletion Δ v w original Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)

/-- Dropping the structure exclusions and hole restriction recovers the
previous failure with the same root, paths, contexts and cost bound. -/
theorem NonstructuralEqHeadCompletionFailure.forget
    (H : NonstructuralEqHeadCompletionFailure D Δ v w original budget) :
    EqHeadCompletionFailure D Δ v w original budget := by
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, _, HT, RP, HTroot, HR, HN, _, RT, HP⟩ := H
  exact ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, HT, RP, HTroot, HR, HN, RT, HP⟩

/-- Completion at the selected root reads the original equation; otherwise
the concrete missing completion occurs at a nonstructural tracked head loss.
All restrictions come from the execution, not additional ancestry premises. -/
theorem TypedNonrigidHeadLoss.eq_or_completion_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : TypedNonrigidHeadLoss D ``Eq.rec budget) :
    env.IsDefEq univs Δ a b α ∨
      NonstructuralEqHeadCompletionFailure D Δ v w [α,a,M,minor,b] budget := by
  classical
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, RT⟩ := H.root heq hs
  by_cases HP : EqHeadCompletion Δ v w [α,a,M,minor,b] Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args)
  · exact .inl (HP.read_loss heq hs hreg hoff hRec hΔ ht HR HN)
  · exact .inr ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
      hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, RT, HP⟩

end Lean4Lean.VEnv.Strengthening
