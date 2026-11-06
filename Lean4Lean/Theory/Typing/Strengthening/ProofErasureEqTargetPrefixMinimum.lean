import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqUnusedConsumption
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefixExecution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaHoleMinimum

/-! # Completed non-level cuts strictly descend the mixed minimum

Read both positive singleton guards through iterated completion, even when
their output still contains an Eq head. Administrative expansion and structure
recovery are excluded by the actual mixed execution, leaving native eta and
its strictly smaller prefix-completed minimum.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private computed_prefix_length
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaComputed
open private erased_carrier_recovered_singleton_rule_descent erased_computed_joint_prefix_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- Either positive singleton guard reads a completed target directly. The
primitive output need not lose its tracked Eq head. -/
theorem EqHeadCompletion.read_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HG : CarrierRecoveredSingletonPrimitive Step Ξ source target ∨
      ComputedJointPrefixPrimitive Step Ξ source target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, hΓ', W, rfl, hf, hn, HP, rfl⟩ := H
  rcases HG with HG | HQ
  · exact HP.read_singleton heq hstep hΓ hΓ' W hΔ ht hf hn HG
  · have EE := proofErase_const_spine hΓ hf hn
    rw [EE, ProofShape.liftN_mkApps, ProofShape.liftN] at HQ
    have hfive : pre.length = 5 := by
      simpa only [List.length_map] using computed_prefix_length HQ
    obtain ⟨α', a', M', minor', b', rfl⟩ :
        ∃ α' a' M' minor' b', pre = [α',a',M',minor',b'] := by
      cases pre with | nil => simp at hfive | cons x xs =>
      cases xs with | nil => simp at hfive | cons y ys =>
      cases ys with | nil => simp at hfive | cons z zs =>
      cases zs with | nil => simp at hfive | cons q qs =>
      cases qs with | nil => simp at hfive | cons r rs =>
      cases rs with
      | nil => exact ⟨_, _, _, _, _, rfl⟩
      | cons s ss => simp at hfive
    apply HP.read_computed_guard heq hstep hΓ hΓ' W hΔ ht hf
      (rest := []) (pending := []) ?_ HQ
    simp only [List.append_nil]
    exact List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)

/-- Positive singleton readout descends through every actual unused insertion.
The same singleton family is reconstructed at each lower scope before reading
its guard, so no head-loss condition on its output is needed. -/
theorem IteratedAmbientEqCompletion.read_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HG : CarrierRecoveredSingletonPrimitive Step Ξ source target ∨
      ComputedJointPrefixPrimitive Step Ξ source target) :
    env.IsDefEq univs Δ a b α := by
  induction H generalizing target with
  | base H => exact H.read_guard heq hstep hΔ ht HG
  | insert hΓ hΓ' W hf H ih =>
    rcases HG with HG | HQ
    · obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep hΓ hΓ' W hf HG
      exact ih (.inl HL)
    · obtain ⟨_, _, HL, _⟩ := erased_computed_joint_prefix_rule_descent heq hstep hΓ hΓ' W hf HQ
      exact ih (.inr HL)

/-- A positive singleton guard bounds its own source by five arguments.
Bounded completion is consequently full completion at this root, allowing
readout without any assertion about the primitive's output head. -/
theorem EqTargetPrefixCompletion.read_guard
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HG : CarrierRecoveredSingletonPrimitive Step Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
      ComputedJointPrefixPrimitive Step Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Γ a b α := by
  have hlen : args.length ≤ 5 := by
    rcases HG with HG | HQ
    · exact HG.2.eq_rec_arity_le heq
    · exact Nat.le_of_eq (computed_prefix_length HQ)
  have HP : IteratedAmbientEqCompletion Γ v w [α,a,M,minor,b] Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
    simpa only [List.length_cons, List.length_nil, List.take_of_length_le hlen] using H.prefix
  exact HP.read_guard heq hstep hΓ ht HG

omit [Params] in
private theorem tracked_spine_hole (Δ : List ProofShape) (args : List ProofShape) :
    ∃ C : ScopedHole Δ Δ, SpineBinderHole C ∧ ∀ f, C.plug f = ProofShape.mkApps f args := by
  induction args using List.snoc_induction with
  | nil => exact ⟨.hole, .hole, fun _ => rfl⟩
  | snoc args x ih =>
    obtain ⟨C, HC, EC⟩ := ih
    exact ⟨.appFn C x, .appFn HC, fun f => by rw [ProofShape.mkApps_snoc]; exact congrArg (fun g => ProofShape.app g x) (EC f)⟩

/-- A completed non-level root under any application/binder hole either
reads the target equation or is native eta with a strictly smaller completed
body minimum. The actual eta recovery, domain and output equality are retained
so callers can additionally exploit the original supplied arguments. Completion
at this actual root is required; no arbitrary-substitution transport is used. -/
theorem EqTargetPrefixCompletion.hole_cut_eq_or_smaller {C : ScopedHole Δ Θ}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Θ
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
      EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] (A :: Θ)
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
  · exact .inl (HP.read_guard heq (erased_static_structure_eta_expansion_stage_certificate_descent heq hs n) hΓ ht (.inr HQ))
  rcases static_other_spine_root HR.1 Hcore HQ Hstruct with HC | ⟨k, hk, HG | HI | HEta⟩
  · exact (Hconst HC).elim
  · exact .inl (HP.read_guard heq (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k) hΓ ht (.inl HG))
  · exact (HId _ HI).elim
  · cases HEta with
    | @intro A B u RN SD =>
      obtain ⟨_, hsmall, HM, HPfresh⟩ := HP.eta_hole_minimum
        heq hs hΓ ht HC HT RN SD RP HR RT HK hcost hmin
      exact .inr ⟨k, A, B, u, rfl, hk, RN, SD, hsmall, HM, HPfresh⟩

/-- Every actual completed non-level cut in a typed minimum either reads the
original equation or follows native eta to a strictly smaller typed minimum
with bounded completion. An actually consumed component-only body returns to
the parent's scope; the other branches retain the smaller fresh-body minimum. No source arity bound or ancestry hypothesis
for the primitive output is imposed. -/
theorem TargetPrefixEqSpineCut.eq_or_smaller
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (H : TargetPrefixEqSpineCut D Γ v w [α,a,M,minor,b] n Δ source endpoint budget)
    (HT : TypedSource Δ source)
    (HK : PiInertTypedContinuationRun D Ω out Δ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : budget+ck ≤ cost)
    (hmin : ∀ later j endpoint' k,
      ScopedComputeCount (PiInertStage D later) j Δ source endpoint' → K endpoint' k → cost ≤ j+k) :
    env.IsDefEq univs Γ a b α ∨
      ∃ Ξ ls args smaller, smaller < cost ∧
        PiInertTypedContinuationMinimum D Ω out Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) smaller ∧
        EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
  classical
  obtain ⟨ls, pre, pending, target, cp, ct, hc, RP, HR, HN, RT, HP, HPsupplied⟩ := H
  have RP' : ScopedComputeCount (PiInertStage D n) cp Δ source
      (ProofShape.mkApps (ProofShape.mkApps (.const ``Eq.rec ls) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using RP
  have HTwhole := HT.pi_inert_compute heq hs RP'.forget
  obtain ⟨C, HC, EC⟩ := tracked_spine_hole Δ pending
  have RPC : ScopedComputeCount (PiInertStage D n) cp Δ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) pre)) := by rw [EC]; exact RP'
  have RTC : ScopedComputeCount (PiInertStage D n) ct Δ (C.plug target) endpoint := by rw [EC]; exact RT
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΓ ht HC HT RPC HR HN RTC HK HE HO
      (cost := cost) (by omega) hmin with Hlower | ⟨k, A, B, u, rfl, _, RN, SD, _, _, _⟩
  · exact .inl Hlower
  · obtain ⟨_, Ξ, next, smaller, hsmall, HM, HPnew, _⟩ := HPsupplied.eta_origin_minimum
      heq hs hΓ ht HTwhole RN SD RP' HR RT HK (cost := cost) (by omega) hmin
    have Hshape := HPnew
    obtain ⟨nextLs, nextArgs, ES, _⟩ := Hshape
    exact .inr ⟨Ξ, nextLs, nextArgs, smaller, hsmall, ES ▸ HM, ES ▸ HPnew⟩

/-- A remaining component-only minimum with bounded completion at both ends
of its actual current path. Its actual mixed continuation and next application
are retained, with the intervening prefix represented by an application/binder hole and
its exact inner substitution. The original continuation predicate is preserved
pointwise on all competitors. What is missing is propagation of target
agreement when that completed endpoint enters the enclosing frames; source typing alone does not give that agreement. -/
def EqTargetPrefixComponentMinimum (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ Δ ls args ls' args' n cb ck K, cb+ck ≤ budget ∧
    EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls') args') ∧
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
theorem EqTargetPrefixComponentMinimum.mono
    (H : EqTargetPrefixComponentMinimum D Γ v w original Ω out budget)
    (h : budget ≤ larger) : EqTargetPrefixComponentMinimum D Γ v w original Ω out larger := by
  obtain ⟨Δ, ls, args, ls', args', n, cb, ck, K, hc, H⟩ := H
  exact ⟨Δ, ls, args, ls', args', n, cb, ck, K, Nat.le_trans hc h, H⟩

/-- Follow the frontier's actual next application and focus its enclosing
application/binder hole. This yields a typed minimum at the substituted Eq
spine, with the unchanged remaining budget. Its substitution is identity or
one binder consumption beneath a finite retained prefix, derived from the
actual execution. Identity maps retain their concrete annotation history;
consumption still requires agreement from the recorded argument ancestry.
Target completion is retained at the original endpoint. This theorem does not claim
strict decrease when the preceding component path has zero cost. -/
theorem EqTargetPrefixComponentMinimum.focus_next
    (H : EqTargetPrefixComponentMinimum D Γ v w original Ω out budget) :
    ∃ Δ Λ ls args σ cb ck, cb+ck ≤ budget ∧
      EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
      ContextSubstitution Δ Λ σ ∧ PiInertEndpointContext D Δ Λ σ ∧
      PiInertTypedContinuationMinimum D Ω out Λ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst σ))) ck := by
  obtain ⟨Δ, ls, args, ls', args', n, cb, ck, K, hc, _, HP, _, R, _, _, _, HM, Hnext⟩ := H
  obtain ⟨Ξ, Λ, σ, C, suffixStage, cs, endpoint, ck', K', _, WS, Hancestry, _, _, _, _, _, HMinner, _, _⟩ :=
    Hnext.joint_minimum R rfl HM
  refine ⟨Δ, Λ, ls', args', σ, cb, ck, hc, HP, WS, Hancestry, ?_⟩
  simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HMinner

/-- At the actual next application, identity maps preserve target completion
through their recorded annotation history. Consumption also preserves
completion when the bounded prefix comes from below that unused binder. The
remaining one-binder consumption explicitly lacks such a lower completion.
This does not claim strict count decrease for an identity move or agreement
for the remaining consumed argument. -/
theorem EqTargetPrefixComponentMinimum.focus_next_completed_or_consumed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : EqTargetPrefixComponentMinimum D Γ v w original Ω out budget) :
    ∃ Δ Λ ls args σ cb ck, cb+ck ≤ budget ∧
      EqTargetPrefixCompletion Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
      ContextSubstitution Δ Λ σ ∧
      PiInertTypedContinuationMinimum D Ω out Λ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst σ))) ck ∧
      (EqTargetPrefixCompletion Γ v w original Λ
          (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst σ))) ∨
        ∃ x depth, σ = (ProofShape.Subst.one x).liftN depth ∧
          ¬ UnusedTargetPrefixCompletion Γ v w original Δ
            (ProofShape.mkApps (.const ``Eq.rec ls) args) depth) := by
  classical
  obtain ⟨Δ, Λ, ls, args, σ, cb, ck, hc, HP, WS, Hancestry, HM⟩ := H.focus_next
  refine ⟨Δ, Λ, ls, args, σ, cb, ck, hc, HP, WS, HM, ?_⟩
  rcases Hancestry.unused_ancestry heq hs with ⟨rfl, Hctx⟩ | ⟨x, depth, rfl, Hctx⟩
  · exact .inl (by simpa only [ProofShape.subst_id, List.map_id_fun', id] using
      HP.context_history heq hs hΓ Hctx)
  · by_cases HU : UnusedTargetPrefixCompletion Γ v w original Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) depth
    · have HH := UnusedTargetPrefixCompletion.consume heq hs hΓ HU Hctx x
      exact .inl (by simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HH)
    · exact .inr ⟨x, depth, rfl, HU⟩

/-- Strong induction removes every completed non-level cut from the current
path: singleton guards read the target, administrative roots contradict the
minimum, and native eta strictly decreases it. The remaining actual minimum
has component ancestry and bounded completion at both current endpoints.
Its next application retains the exact substituted hole and the original
competitor predicate. Target agreement through that hole is still required. -/
theorem EqTargetPrefixCompletion.minimum_frontier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertTypedContinuationMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqTargetPrefixComponentMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
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

end Lean4Lean.VEnv.Strengthening
