import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointPathSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointAnchoredSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstrainedComputeTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Guard-preserving substitution through the first recursive computation layer

The primitive guards use the entire stage-zero computed-domain checker. Their
transport is proved under generated telescopes; no proposition beta stability
or arbitrary assigned-domain recovery is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim ProofShape
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- A binder-stable interpreted constraint together with proved transport of
both recursive stage-zero checking views. The generic primitive theorem uses
only these explicit fields; it assumes no unrestricted image coverage. -/
structure ComputedZeroGuardSubstitution (D : PureObservation.Definitions)
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop) : Prop where
  interpret : ∀ {Δ Δ' τ}, Transport Δ Δ' τ → ContextSubstitution Δ Δ' τ
  cons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ →
    Transport (A :: Δ) (A.subst τ :: Δ') τ.lift
  check : ∀ {Δ kind a b}, ComputedJointCheck (ErasedJointStage D 0) Δ kind a b →
    ComputedJointTransportResult Transport (ErasedJointStage D 0) Δ kind a b

/-- Selected finite paths instantiate all guard-transport requirements. -/
theorem ComputedZeroGuardSubstitution.path (hs : D.Sound env univs) :
    ComputedZeroGuardSubstitution D (PathImageSubstitution D) :=
  ⟨(fun W => W.interpretation), (fun W => W.cons), (fun H => H.transport_pathImages hs)⟩

/-- Protected neutral-family paths instantiate the same requirements, including
the inert-carrier alternative needed by converted neutral domains. -/
theorem ComputedZeroGuardSubstitution.anchored (hs : D.Sound env univs) :
    ComputedZeroGuardSubstitution D (AnchoredImageSubstitution D) :=
  ⟨(fun W => W.interpretation), (fun W => W.cons), (fun H => H.transport_anchoredImages hs)⟩

/-- The guard-transport constraint extends through a realized dependent residual
telescope, with each annotation substituted at its actual depth. -/
theorem ComputedZeroGuardSubstitution.telescope
    (G : ComputedZeroGuardSubstitution D Transport) {domains : List VExpr}
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs)) :
    Transport (proofEraseCtx (domains.reverse ++ Γ))
      (proofEraseCtx ((domains.mapIdx fun i A => A.subst (σ.liftN i)).reverse ++ Γ₀))
      (τ.liftN domains.length) := by
  induction domains generalizing Γ Γ₀ σ τ with
  | nil => exact WR
  | cons A ds ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx
    obtain ⟨_, u, hA⟩ := OnCtx.of_append hctx
    have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have WR' : Transport (proofEraseCtx (A :: Γ))
        (proofEraseCtx (A.subst σ :: Γ₀)) τ.lift := by
      simp only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA E]
      exact G.cons WR
    simp only [List.mapIdx_cons, VExpr.Subst.liftN,
      List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [← ProofShape.Subst.lift_liftN]
    have HI : Transport (proofEraseCtx (ds.reverse ++ A :: Γ))
        (proofEraseCtx ((ds.mapIdx fun i B => B.subst (σ.lift.liftN i)).reverse ++ A.subst σ :: Γ₀))
        (τ.lift.liftN ds.length) :=
      ih WR' hΓA₀ (W.lift henv.ordered hA) (E.lift hΓ₀ W hA) hctx
    simp only [VExpr.Subst.lift_liftN, VExpr.Subst.liftN] at HI
    exact @HI

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- The actual family guard substitutes under its entire generated telescope.
The entire recursive stage-zero comparison transports, including computed applications. -/
theorem Valid.computed_family_guard_subst (V : C.Valid) (heq : env.HasCanonicalEq)
    (G : ComputedZeroGuardSubstitution D Transport)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ComputedJointCompare (ErasedJointStage D 0) Δ true))
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ComputedJointCompare (ErasedJointStage D 0) Δ true))
      Γ₀ C.data C.levels (args.map (·.subst σ)) (program.subst σ) C.layout C.elim := by
  obtain ⟨_, hnon, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, F, hS, hF, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hF.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv W.wf V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  obtain ⟨hctx₀, Wext, Eext⟩ := erasedSubst_telescope hΓ₀ W E hctx
  let ps := (C.data.openedArguments args).take C.data.numParams
  let idx := ((C.data.openedArguments args).drop C.data.indexOffset).take C.data.numIndices
  have htf := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hpf := WF.family_prop henv hps hargs
  have htfS := transportedFamily_subst henv heq WF hctx hps hargs (σ.liftN program.domains.length)
  have hpos : 0 < program.domains.length := List.length_pos_iff.mpr hnon
  simp only [VExpr.subst_bvar, VExpr.Subst.liftN_apply, if_pos hpos] at htfS
  have hpfS : (mkApps C.elim.family (ps ++ idx)).subst (σ.liftN program.domains.length) =
      mkApps C.elim.family ((ps ++ idx).map (·.subst (σ.liftN program.domains.length))) := by
    rw [VExpr.subst_mkApps, WF.family_closed.subst_eq .zero]
  have HC := G.check HG hctx htf hpf rfl rfl rfl
    (G.telescope WR hΓ₀ W E hctx)
  obtain ⟨_, _, _, _, hlenD, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  unfold GuardedSingleton.FamilyGuard ErasedFamilyComparison
  simp only [RecursorData.openedArguments_subst, ← hlenD, ← List.map_take, ← List.map_drop,
    RecursorData.PrefixUnfolding.subst]
  rw [← htfS, ← List.map_append, ← hpfS,
    proofErase_subst_with hctx₀ Wext htf Eext, proofErase_subst_with hctx₀ Wext hpf Eext]
  exact HC

end SingletonPrefixCode

/-- Typed general singleton primitives retain their exact output under an
interpreted guard-preserving substitution. The generated dependent telescope
is transported explicitly. -/
theorem proofErase_computed_singleton_guard_subst (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (G : ComputedZeroGuardSubstitution D Transport)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.ComputedJointCompare (ErasedJointStage D 0) Δ true) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.SingletonPrimitiveWith (fun Δ => ProofShape.ComputedJointCompare (ErasedJointStage D 0) Δ true) (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq W.wf ha ⟨_, ht⟩ hcalc HG
    have HC := V.checkWith heq (erased_computed_joint_family_descent (erased_computed_joint_stage_descent heq hs 0)) W.wf hg ⟨_, ht⟩ HG
    have hg' := RecursorData.singletonUnfolding_subst henv V.registered V.large V.zero
      V.recType_eq (V.registered.recursorType_closed henv V.recType_eq) hg (σ := σ)
    have ht' : env.HasType univs Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) (T.subst σ) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using ht.subst henv.orderedStrong W hΓ₀
    have HG' := V.computed_family_guard_subst heq G hΓ₀ W E WR hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq (erased_computed_joint_family_descent (erased_computed_joint_stage_descent heq hs 0)) hΓ₀ hg' ⟨_, ht'⟩ HG'
    have hn' : ¬ IsProof Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using
        mt (isProof_subst hΓ₀ W ht).1 hn
    have HE := V.output_eq heq W.wf hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ₀ hg' HC' hn'
    have HS := proofErase_subst_with hΓ₀ W (HC.defeq henv W.wf).hasType.2 E
    rw [← program.subst_rhs (HC.templateScope henv).2.1, HE', HE] at HS
    rw [← hsrc, ← proofErase_subst_with hΓ₀ W ht E, VExpr.subst_mkApps, VExpr.subst_const,
      proofErase_const_spine hΓ₀ ht' hn', ← HS]
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ₀ hg' ⟨_, ht'⟩)
      ((V.guardWith_iff heq hΓ₀ hg' ⟨_, ht'⟩).2 HG')

/-- A specialized Eq prefix transports its actual carrier guard directly.
No encoding of Eq as a different singleton program or registry agreement is
needed for this source-typed substitution theorem. -/
theorem proofErase_computed_prefix_guard_subst
    (heq : env.HasCanonicalEq) (G : ComputedZeroGuardSubstitution D Transport)
    (hΓ : OnCtx Γ (env.IsType univs))
    (WR : Transport (proofEraseCtx Γ) Δ' τ)
    (ht : env.HasType univs Γ e T)
    (R : ComputedJointPrefixPrimitive (ErasedJointStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputedJointPrefixPrimitive (ErasedJointStage D 0) Δ'
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, _, _, Hb⟩ :=
      proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Hα, ← Ha, ← Hb] at HC
    obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have HC' := G.check HC hΓ ha hb rfl rfl rfl rfl WR
    rw [Hα, Ha, Hb] at HC'
    simpa only [ProofShape.eqRecBeforeMajor, ProofShape.eqProofType, ProofShape.subst,
      ProofShape.lift_subst_lift] using
      (ComputedJointPrefixPrimitive.intro (v := v) (w := w)
        (M := M.subst τ) (m := m.subst τ) HC')

/-- First-layer primitives substitute at the same stage under a proved
stage-zero guard-transport constraint. Both actual
singleton programs and specialized Eq prefixes retain their exact output. -/
theorem erased_computed_joint_one_primitive_subst_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (G : ComputedZeroGuardSubstitution D Transport)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (WR : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ)
    (ht : env.HasType univs Γ e T)
    (H : ErasedComputedJointStage D 1 (proofEraseCtx Γ) (proofErase Γ e) out) :
    ErasedComputedJointStage D 1 (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht E]
  rcases H with H | H | H
  · exact .inl (erased_iota_primitive_subst H)
  · exact .inr (.inl ⟨H.1.subst (G.interpret WR),
      proofErase_computed_singleton_guard_subst heq hs G hΓ₀ W E WR ht H.2⟩)
  · exact .inr (.inr (proofErase_computed_prefix_guard_subst heq G W.wf WR ht H))

/-- Every compatible first-layer path transports, including transitive
intermediates and computations under dependent binders. The image condition
is extended only under binders; it is not reapplied to intermediate values. -/
theorem ProofShape.ScopedCompute.transport_firstStage_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (G : ComputedZeroGuardSubstitution D Transport)
    (R : ScopedCompute (ErasedComputedJointStage D 1) Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (WR : Transport Δ Δ' τ) :
    ScopedCompute (ErasedComputedJointStage D 1) Δ' (source.subst τ) (out.subst τ) := by
  apply R.transport_typed (erased_computed_joint_stage_descent heq hs 1)
    Transport (fun W => G.cons W) ?_ hΓ ht EΓ Ee WR
  intro Γ Δ Δ' τ e T source out H hΓ ht EΓ Ee WR
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, W, ES⟩ := G.interpret WR hΓ EΓ
  have WR' : Transport (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
    simpa only [EΓ, EΓ₀] using WR
  have HH := erased_computed_joint_one_primitive_subst_guard heq hs G hΓ₀ W ES WR' ht
    (by simpa only [EΓ, Ee] using H)
  apply ScopedCompute.base
  simpa only [proofErase_subst_with hΓ₀ W ht ES, EΓ₀, Ee] using HH

/-- Actual typed simultaneous substitution preserves a whole first-layer
computation and its exact substituted output, without increasing the stage. -/
theorem proofErase_computed_joint_one_compute_subst_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : PathOrRecoveringImages D Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact R.transport_firstStage_guard heq hs (ComputedZeroGuardSubstitution.path hs) W.wf ht rfl rfl
    (PathImageSubstitution.of_typed hΓ₀ W E HI)

/-- A selected-path argument may instantiate any typed first-layer computation.
The result includes actual generated singleton and Eq computations whose guards
use recursively nested computed-domain application checking. -/
theorem proofErase_computed_joint_one_compute_inst_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (HR : SortRootedRecovery D Γ p (proofErase Γ T) n)
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (T :: Γ)) (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    proofErase_computed_joint_one_compute_subst_path heq hs hΓ W
      (erasedSubstAgreement_one hΓT hp) (PathOrRecoveringImages.inst HR) he R


/-- Any type or proposition may instantiate a first-layer computation; no
native recovery of that argument is required. -/
theorem proofErase_computed_joint_one_compute_inst_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort u))
    (he : env.HasType univs (.sort u :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.sort u :: Γ)) (proofErase (.sort u :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  apply proofErase_computed_joint_one_compute_inst_path (n := 0) heq hs hΓ hp ?_ he R
  rw [show proofErase Γ (.sort u) = .sort u from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (hp.sort_r henv hΓ)))]
  exact .type hp

/-- A type-valued lambda at its displayed Pi may instantiate an entire
first-layer computation, including nested generated-prefix computations.
Arbitrarily converted assigned Pi domains are not included. -/
theorem proofErase_computed_joint_one_compute_inst_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u))
    (hp : env.HasType univs (C :: Γ) p (.sort v))
    (he : env.HasType univs (.forallE C (.sort v) :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE C (.sort v) :: Γ))
      (proofErase (.forallE C (.sort v) :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst (.lam C p))) (out.inst (proofErase Γ (.lam C p))) :=
  proofErase_computed_joint_one_compute_inst_path heq hs hΓ (HasType.lam hC hp)
    (SortRootedRecovery.typeFamily hΓ hC hp) he R


/-- Protected neutral-family images transport first-layer computations at the
same stage, even when exact selected-domain recovery is unavailable. -/
theorem proofErase_computed_joint_one_compute_subst_anchored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact R.transport_firstStage_guard heq hs (ComputedZeroGuardSubstitution.anchored hs)
    W.wf ht rfl rfl (AnchoredImageSubstitution.of_typed hΓ₀ W E HI)

/-- A selected protected-family path supplies the image invariant for single
instantiation throughout a first-layer computation. -/
theorem proofErase_computed_joint_one_compute_inst_anchored
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (HR : AnchoredFamilyRecovery D cut Γ p (proofErase Γ T) n)
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (T :: Γ)) (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    proofErase_computed_joint_one_compute_subst_anchored heq hs hΓ W
      (erasedSubstAgreement_one hΓT hp) (AnchoredOrRecoveringImages.inst HR) he R

/-- Any type family assigned a neutral-domain Pi may instantiate a first-layer
computation. The assigned domain may differ from the lambda's written domain;
its neutral head is protected from the single substitution. -/
theorem proofErase_computed_joint_one_compute_inst_neutralFamily
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE C (.sort u)))
    (HC : AnchoredCarrier 0 (proofErase Γ C))
    (he : env.HasType univs (.forallE C (.sort u) :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE C (.sort u) :: Γ))
      (proofErase (.forallE C (.sort u) :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_anchored heq hs hΓ hp
    (AnchoredFamilyRecovery.of_family hΓ hp HC) he R

end Lean4Lean.VEnv.Strengthening
