import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetractionHistory

/-! # Strict minimum descent with reverse-renaming completion

A reverse-renaming witness reads positive singleton guards and survives fresh
eta opening. Thus the actual non-level cuts admit the same strict descent,
without asserting ordinary completion in the current context. The remaining
component frontier still needs propagation through its next scope move.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tracked_spine_hole
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixMinimum
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- A completed native eta root inside any application/binder hole yields a
strictly smaller completed fresh-body minimum. Reverse-renaming completion is derived at the
actual root before eta; no transport of completion through an arbitrary later
substitution is assumed. The entire outer suffix is retained as a typed body
continuation, so immediate consumption of the new binder is unnecessary. -/
theorem EqTargetPrefixRetraction.eta_hole_minimum {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) originalArgs) T)
    (HP : EqTargetPrefixRetraction Γ v w originalArgs Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : SpineBinderHole C) (HT : TypedSource Δ original)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B)) (SD : DomainSort Θ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)))
    (HR : PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)
      (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (C.plug (.lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)))) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ original tail →
      K tail k → cost ≤ j+k) :
    cp+1+ct+ck = cost ∧ ct+ck < cost ∧
    PiInertTypedContinuationMinimum D Ω out (A :: Θ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) (ct+ck) ∧
    EqTargetPrefixRetraction Γ v w originalArgs (A :: Θ)
      (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  obtain ⟨hexact, hsmall, HM, _⟩ := pi_inert_lambda_hole_body_minimum heq hs HC HT RP HR RT HK hcost hmin
  exact ⟨hexact, hsmall, HM, HP.eta heq hs hΓ ht RN SD⟩

/-- A completed non-level root under any application/binder hole either
reads the target equation or is native eta with a strictly smaller completed
body minimum. The actual eta recovery, domain and output equality are retained
so callers can additionally exploit the original supplied arguments. Completion
at this actual root is required; no arbitrary-substitution transport is used. -/
theorem EqTargetPrefixRetraction.hole_cut_eq_or_smaller {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixRetraction Γ v w [α,a,M,minor,b] Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : SpineBinderHole C) (HT : TypedSource Δ source)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)))
    (HR : PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ LevelPrimitive univs (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Γ a b α ∨ ∃ k A B u,
      target = .lam A (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) ∧
      k < n ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B) ∧ DomainSort Θ A u ∧
      ct+ck < cost ∧
      PiInertTypedContinuationMinimum D Ω out (A :: Θ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) (ct+ck) ∧
      EqTargetPrefixRetraction Γ v w [α,a,M,minor,b] (A :: Θ)
        (.app ((ProofShape.mkApps (.const ``Eq.rec ls) args).liftN 1) (etaArgument u)) := by
  classical
  have HTwhole := HT.pi_inert_compute heq hs RP.forget
  have HTroot := C.typed HTwhole
  have Hconst := pi_inert_frames_minimum_no_constant heq hs HT HE HC.tracked RP HR RT HK hcost hmin
  have HId := pi_inert_frames_minimum_no_identity HK.frames HE HC.tracked RP RT HK.holds hcost hmin
  have Hcore : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
    rintro (Hcore | HL)
    · exact typed_eq_no_core_root heq hreg hoff hRec HTroot (constHead_mkApps _ _) Hcore
    · exact HN HL
  have Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target := by
    intro HS
    obtain ⟨c, hr, HTail⟩ := rigid_tail_of_native_structure
      (erased_static_structure_eta_expansion_stage_descent heq hs n) HTroot const_spine_ne_proof HS
    have hp : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
      ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
    have Hwhole := HC.tracked.rigid_tail_plug hp hr HTwhole HTail
    exact HO.no_rigid_tail hr (HK.rigid_tail heq hs hr
      (Hwhole.compute hp ((HC.counted (.base HR)).trans RT).forget))
  by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target
  · exact .inl (HP.read_guard heq (erased_static_structure_eta_expansion_stage_certificate_descent heq hs n)
      (erased_static_structure_eta_expansion_stage_rename heq hs n) hΓ ht (.inr HQ))
  rcases static_other_spine_root HR.1 Hcore HQ Hstruct with HC | ⟨k, hk, HG | HI | HEta⟩
  · exact (Hconst HC).elim
  · exact .inl (HP.read_guard heq (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
      (erased_static_structure_eta_expansion_stage_rename heq hs k) hΓ ht (.inl HG))
  · exact (HId _ HI).elim
  · cases HEta with
    | @intro A B u RN SD =>
      obtain ⟨_, hsmall, HM, HPfresh⟩ := HP.eta_hole_minimum
        heq hs hΓ ht HC HT RN SD RP HR RT HK hcost hmin
      exact .inr ⟨k, A, B, u, rfl, hk, RN, SD, hsmall, HM, HPfresh⟩


/-- Every actual completed non-level cut in a typed minimum either reads the
original equation or follows native eta to a strictly smaller typed minimum
with bounded reverse-renaming completion. The entire outer suffix is retained by the smaller fresh-body minimum. No source arity bound or ancestry hypothesis
for the primitive output is imposed. -/
theorem RetractedTargetPrefixEqSpineCut.eq_or_smaller
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (H : RetractedTargetPrefixEqSpineCut D Γ v w [α,a,M,minor,b] n Δ source endpoint budget)
    (HT : TypedSource Δ source)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : budget+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ source endpoint' → K endpoint' k → cost ≤ j+k) :
    env.IsDefEq univs Γ a b α ∨
      ∃ Ξ ls args smaller, smaller < cost ∧
        PiInertTypedContinuationMinimum D Ω out Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) smaller ∧
        EqTargetPrefixRetraction Γ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
  classical
  obtain ⟨ls, pre, pending, target, cp, ct, hc, RP, HR, HN, RT, HP, HPsupplied⟩ := H
  have RP' : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using RP
  obtain ⟨C, HC, EC⟩ := tracked_spine_hole Δ pending
  have RPC : ScopedComputeCount (PiInertStage D n) cp Δ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) pre)) := by rw [EC]; exact RP'
  have RTC : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint := by rw [EC]; exact RT
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΓ ht HC HT RPC HR HN RTC HK HE HO
      (cost := cost) (by omega) hmin with Hlower | ⟨k, A, B, u, _, _, _, _, hsmall, HM, HPfresh⟩
  · exact .inl Hlower
  · have ES : .app ((ProofShape.mkApps (.const ``Eq.rec ls) pre).liftN 1) (etaArgument u) =
        ProofShape.mkApps (.const ``Eq.rec ls) (pre.map (·.liftN 1) ++ [etaArgument u]) := by
      simp only [ProofShape.liftN_mkApps, ProofShape.liftN, ProofShape.mkApps_append, ProofShape.mkApps]
    exact .inr ⟨A :: Δ, ls, pre.map (·.liftN 1) ++ [etaArgument u], ct+ck, hsmall, ES ▸ HM, ES ▸ HPfresh⟩


/-- A remaining component-only minimum with bounded reverse-renaming completion at both ends
of its actual current path. Its actual mixed continuation and next application
are retained, with the intervening prefix represented by an application/binder hole and
its exact inner substitution. The original continuation predicate is preserved
pointwise on all competitors. What is missing is propagation of the reverse
renaming through the next scope move; source typing alone does not provide it. -/
def EqRetractionComponentMinimum (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ Δ ls args ls' args' n cb ck K, cb+ck ≤ budget ∧
    EqTargetPrefixRetraction Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    EqTargetPrefixRetraction Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls') args') ∧
    TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    ScopedComputeCount (PiInertStage D n) cb Δ (ProofShape.mkApps (.const ``Eq.rec ls) args)
      (ProofShape.mkApps (.const ``Eq.rec ls') args') ∧
    List.Forall₂ (· ≈ ·) ls ls' ∧
    List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args' ∧
    PiInertTypedContinuationRun D Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls') args') ck ∧
    (∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint → K endpoint k → cb+ck ≤ j+k) ∧
    PiInertNextApplicationAtHole D Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls') args') ck

/-- Increasing the recorded budget retains the identical actual component
path, continuation and minimum. -/
theorem EqRetractionComponentMinimum.mono
    (H : EqRetractionComponentMinimum D Γ v w original Ω out budget)
    (h : budget ≤ larger) : EqRetractionComponentMinimum D Γ v w original Ω out larger := by
  obtain ⟨Δ, ls, args, ls', args', n, cb, ck, K, hc, H⟩ := H
  exact ⟨Δ, ls, args, ls', args', n, cb, ck, K, Nat.le_trans hc h, H⟩

/-- Follow the frontier's actual next application and focus its enclosing
application/binder hole. This yields a typed minimum at the substituted Eq
spine, with the unchanged remaining budget. Its substitution is identity or
one binder consumption beneath a finite retained prefix, derived from the
actual execution. Identity maps retain their concrete annotation history;
consumption still requires agreement from the recorded argument ancestry.
The reverse-renaming witness is retained at the original endpoint. This theorem does not claim
strict decrease when the preceding component path has zero cost. -/
theorem EqRetractionComponentMinimum.focus_next
    (H : EqRetractionComponentMinimum D Γ v w original Ω out budget) :
    ∃ Δ Λ ls args σ cb ck, cb+ck ≤ budget ∧
      EqTargetPrefixRetraction Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
      ContextSubstitution Δ Λ σ ∧ PiInertEndpointContext D Δ Λ σ ∧
      PiInertTypedContinuationMinimum D Ω out Λ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst σ))) ck := by
  obtain ⟨Δ, ls, args, ls', args', n, cb, ck, K, hc, _, HP, _, R, _, _, _, HM, Hnext⟩ := H
  obtain ⟨Ξ, Λ, σ, C, suffixStage, cs, endpoint, ck', K', _, WS, Hancestry, _, _, _, _, _, HMinner, _, _⟩ :=
    Hnext.joint_minimum R rfl HM
  refine ⟨Δ, Λ, ls', args', σ, cb, ck, hc, HP, WS, Hancestry, ?_⟩
  simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HMinner


/-- Strong induction removes every non-level cut carrying reverse-renaming
completion: singleton guards read the target, administrative roots contradict
the minimum, and native eta strictly decreases it. The remaining actual
component minimum retains the invariant at both endpoints, the next scope
map, and the original competitor predicate. Propagation through that next
scope map and progress through equal-cost moves are still required. -/
theorem EqTargetPrefixRetraction.minimum_frontier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixRetraction Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertTypedContinuationMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqRetractionComponentMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
  induction cost using Nat.strongRecOn generalizing Δ ls args with
  | ind cost ih =>
    obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, hmin⟩ := HM
    rcases HP.counted_spine_or_cut heq hs hΓ HT R with
      ⟨ls', args', rfl, HL, HA, HPend⟩ | Hcut
    · refine .inr ⟨Δ, ls, args, ls', args', n, cb, ck, K, by omega,
        HP, HPend, HT, R, HL, HA, HK, ?_, ?_⟩
      · simpa only [hc] using hmin
      · exact (HK.next_application HE
          (((RetainedConstHead.const (ls := ls')).mkApps args').eq_not_exposed heq)).substitution_hole
    · rcases Hcut.eq_or_smaller heq hs hreg hoff hRec hΓ ht HT HK HE HO
        (cost := cost) (by omega) hmin with Hlower | ⟨Ξ, ls', args', smaller, hsmall, HM', HP'⟩
      · exact .inl Hlower
      · rcases ih smaller hsmall HP' HM' with Hlower | Hfront
        · exact .inl Hlower
        · exact .inr (Hfront.mono (Nat.le_of_lt hsmall))

/-- Follow the ordinary component frontier through its actual next scope
move. A proof-valued endpoint now enters the full strict retraction descent,
so the result is target equality, a later retraction component frontier, or
the actual consumed base binder without a Prop-domain witness. The latter
retains its original completion, typed next minimum, substitution and budget.
This is a necessary frontier, not a sufficient strengthening obligation. -/
theorem EqTargetPrefixComponentMinimum.eq_or_retracted_frontier_or_consumed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqTargetPrefixComponentMinimum D Γ v w [α,a,M,minor,b] Ω out budget)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨
      EqRetractionComponentMinimum D Γ v w [α,a,M,minor,b] Ω out budget ∨
      ∃ Δ Λ ls args σ cb ck, cb+ck ≤ budget ∧
        EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
        ContextSubstitution Δ Λ σ ∧
        PiInertTypedContinuationMinimum D Ω out Λ
          (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst σ))) ck ∧
        ∃ Θ A x depth, ContextSubstitution (A :: Θ) Θ (ProofShape.Subst.one x) ∧
          ¬ DomainSort Θ A .zero ∧ σ = (ProofShape.Subst.one x).liftN depth := by
  obtain ⟨Δ, Λ, ls, args, σ, cb, ck, hc, HP, WS, HM, HR | HN⟩ :=
    H.focus_next_retracted_or_unwitnessed_domain heq hs hΓ
  · rcases HR.minimum_frontier heq hs hreg hoff hRec hΓ ht HM HE HO with HEq | Hfront
    · exact .inl HEq
    · exact .inr (.inl (Hfront.mono (by omega)))
  · exact .inr (.inr ⟨Δ, Λ, ls, args, σ, cb, ck, hc, HP, WS, HM, HN⟩)

end Lean4Lean.VEnv.Strengthening
