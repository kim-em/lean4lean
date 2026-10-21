import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedProviders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSaturatedSingletonComputation

/-! # Computing arbitrary singleton prefix outputs

Supplied arguments compute under the original residual telescope. Replaying
the residual type computation preserves the fresh providers, while telescope
computation changes the generated lambda annotations. The old family guard
types the captures; a target guard is needed only for the residual primitive.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature
variable [Params]

private theorem typed_supply_walk
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ fn type)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps fn args))
    (HS : RecursorData.supplyType args type = some residual) :
    InstForallsC env univs Γ type args residual := by
  induction args generalizing fn type with
  | nil => cases HS; exact .nil
  | cons arg args ih =>
    cases type <;> try contradiction
    rename_i A B
    have hfa : VExpr.WF env univs Γ (.app fn arg) :=
      VExpr.WF.of_mkApps henv.orderedStrong hΓ (f := .app fn arg) ht
    obtain ⟨A', B', hf', ha⟩ := hfa.app_inv henv.orderedStrong hΓ
    obtain ⟨⟨_, hdom⟩, _, _⟩ := (hf.uniqU henv hΓ hf').forallE_inv henv hΓ
    have harg := ha.defeqU_r henv hΓ ⟨_, hdom.symm⟩
    exact .cons harg (ih (hf.app harg) ht HS)

private theorem singleton_compute_telescope
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const data.name levels) args))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args') :
    ∃ ds' result',
      ProofShape.residualTelescope (data.majorOffset + 1 - args.length) args'
        (proofErase [] (recType.instL levels)) = some (ds', result') ∧
    ScopedTelescopeCompute Step (proofEraseCtx Γ) (proofEraseDomains Γ program.domains) ds' ∧
      ∀ n below, contextVars ((proofEraseDomains Γ program.domains).reverse ++ proofEraseCtx Γ)
        n below = contextVars (ds'.reverse ++ proofEraseCtx Γ) n below := by
  unfold RecursorData.singletonUnfolding at hg
  dsimp only at hg
  split at hg <;> try contradiction
  rename_i hguard
  simp at hguard
  have hlen : levels.length = data.uvars := hguard.1
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨recType', htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, _, equation, _, body, _, hg⟩ := hg
  cases Option.some.inj (htype.symm.trans hrec)
  split at hg <;> try contradiction
  cases hg
  have hf : env.HasType univs Γ (.const data.name levels) (recType.instL levels) :=
    .const (H.recursorType htype) hw hlen
  have hf₀ : env.HasType univs [] (.const data.name levels) (recType.instL levels) :=
    .const (H.recursorType htype) hw hlen
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  obtain ⟨v, hT₀⟩ := hf₀.isType henv (by trivial)
  have hc := proofErase_closed_context ((H.recursorType_closed henv htype).instL) hT₀ hΓ
  obtain ⟨w, hres⟩ := (hf.supply henv hΓ ht hsupply).isType henv hΓ
  obtain ⟨out, HS, R⟩ := proofErase_computed_native_supply hstep hhead hsubst hΓ hT
    (typed_supply_walk hΓ hf ht hsupply) .refl RA
  rw [hc] at HS
  obtain ⟨ds', result', HO⟩ :=
    proofErase_takeForalls_compute_exists hstep hsubst hhead hΓ hres htake R
  refine ⟨ds', result', ?_, ?_⟩
  · simpa only [ProofShape.residualTelescope, HS, bind, Option.bind_some] using HO
  exact ⟨(proofErase_takeForalls_compute hstep hsubst hhead hΓ hres R
    (proofErase_takeForalls hΓ ⟨w, hres⟩ htake) HO).1,
    fun _ _ => proofErase_computed_telescope_providers hstep hΓ hres htake R HO⟩

/-- Computing a typed prefix's arguments preserves successful construction of
its residual telescope. This requires no source or target family guard. -/
theorem SingletonPrefixCode.Valid.telescope_compute_exists
    {C : SingletonPrefixCode} (V : C.Valid)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args') :
    ∃ ds' result', C.telescope args' = some (ds', result') := by
  obtain ⟨program, hg⟩ := V.generate ha
  obtain ⟨ds', result', HO, _⟩ := singleton_compute_telescope hstep hsubst hhead hΓ
    V.registered V.levels_wf V.recType_eq hg ht RA
  have hlen : args.length = args'.length := by simpa only [List.length_map] using RA.length_eq
  exact ⟨ds', result', by simpa only [SingletonPrefixCode.telescope, ← hlen] using HO⟩

/-- Computing a typed singleton prefix's supplied arguments computes its whole
generated output, including arbitrary dependent residual lambda annotations.
Only the old family guard is needed for this output path; the new telescope
must successfully peel, but no new guard or chosen argument representatives
are assumed. -/
theorem SingletonPrefixCode.Valid.output_compute
    {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq) (hcmp : ErasedFamilyDescent Cmp)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (ds, result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args')
    (hcalc' : C.telescope args' = some (ds', result')) :
    ScopedCompute Step (proofEraseCtx Γ)
      (C.output (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
      (C.output (proofEraseCtx Γ) ds' args') := by
  obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ht hcalc HG
  have HC := V.checkWith heq hcmp hΓ hg ht HG
  have hlen : args.length = args'.length := by simpa only [List.length_map] using RA.length_eq
  have HO := hcalc'
  simp only [SingletonPrefixCode.telescope, ← hlen] at HO
  obtain ⟨ds₀, result₀, HO₀, RT, HV⟩ := singleton_compute_telescope hstep hsubst hhead hΓ
    V.registered V.levels_wf V.recType_eq hg ht RA
  cases Option.some.inj (HO₀.symm.trans HO)
  have hctx := ((V.registered.prefixType henv hΓ V.levels_wf hg ht).etaOpen_wf henv hΓ).1
  have hrename := fun {Δ Δ' a b τ} (H : Step Δ a b) (W : ContextRenaming Δ Δ' τ) =>
    hsubst H W.interpretation
  have RO := proofErase_openPrefixArguments_compute hrename hΓ hctx RT.length_eq
    (HV _ _) RA
  obtain ⟨hbodyCtx, hbody⟩ := singleton_prefix_body_typed V.registered V.levels_wf hg
  have hcaps : TelInst env univs (program.domains.reverse ++ Γ)
      (program.equationBody.domains.map (·.instL program.levels)) program.captures := by
    refine ⟨by simpa only [List.length_map] using HC.captures_length, ?_⟩
    intro j hj hd
    simpa only [List.getElem_map] using
      HC.captures_typed j hj (by simpa only [List.length_map] using hd)
  have EC := proofErase_singleton_prefix_captures heq hΓ V.registered V.large V.zero
    V.levels_wf V.layout_eq V.elim_eq hg HC
  dsimp only at EC
  rw [proofErase_singleton_prefix_arguments hΓ V.registered V.levels_wf hg ht] at EC
  have RC := (Lean4Lean.List.forall₂_take RO C.data.indexOffset).append'
    (singletonSlots_compute (slots := C.layout.slot) (count := C.layout.fields.length)
      (Lean4Lean.List.forall₂_take (Lean4Lean.List.forall₂_drop RO C.data.indexOffset)
        C.data.numIndices))
  rw [← EC] at RC
  have RB := proofErase_template_compute_captures hrename hctx hbodyCtx hbody hcaps RC
  obtain ⟨hl, hb⟩ := V.program_metadata hg
  rw [EC, hl, hb, proofEraseDomains_context] at RB
  have R := RT.wrapLams RB
  rw [hd] at R
  exact R

/-- The old guard and argument paths alone give a computed output at the new
arguments. Both the target telescope and the whole output path are produced;
there is no target guard or target telescope-success premise. -/
theorem SingletonPrefixCode.Valid.output_compute_exists
    {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq) (hcmp : ErasedFamilyDescent Cmp)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (ds, result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args') :
    ∃ ds' result', C.telescope args' = some (ds', result') ∧
      ScopedCompute Step (proofEraseCtx Γ)
        (C.output (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
        (C.output (proofEraseCtx Γ) ds' args') := by
  obtain ⟨ds', result', HO⟩ := V.telescope_compute_exists hstep hsubst hhead hΓ ha ht RA
  exact ⟨ds', result', HO, V.output_compute heq hcmp hstep hsubst hhead hΓ ha ht hcalc HG RA HO⟩

/-- A singleton/argument fork has a certified residual whenever the computed
argument state supplies its family guard. This covers nonempty dependent
residual telescopes. Source typing is replayed, and the output branch is
constructed without a guard-persistence assumption. -/
theorem SingletonPrefixCode.Valid.certified_residual
    {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const C.data.name C.levels) args) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (ds, result))
    (HG : C.guardWith (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (hcalc' : C.telescope args' = some (ds', result'))
    (HG' : C.guardWith (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) ds' args') :
    ErasedBetaStableJoint D (proofEraseCtx Γ) (ProofShape.mkApps (.const C.data.name C.levels) args')
        (C.output (proofEraseCtx Γ) ds' args') ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (C.output (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
        (C.output (proofEraseCtx Γ) ds' args') := by
  have Rsource := (ScopedCompute.refl (Step := ErasedBetaStableJoint D)
    (Δ := proofEraseCtx Γ) (e := ProofShape.const C.data.name C.levels)).mkApps RA
  obtain ⟨source', HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓ ht rfl
    (proofErase_const_spine hΓ ht hn) Rsource
  have HT : TypedSource (proofEraseCtx Γ) (ProofShape.mkApps (.const C.data.name C.levels) args') :=
    ⟨Γ, source', T, hΓ, rfl, HE.hasType.2, EE⟩
  have ha' : args'.length = C.arity := by
    have H := RA.length_eq
    simp only [List.length_map] at H
    exact H.symm.trans ha
  refine ⟨.inr ⟨HT, .intro V ha' hcalc' HG'⟩, ?_⟩
  exact V.output_compute heq
    (beta_stable_family_descent (erased_joint_family_descent (erased_joint_union_descent heq hs)))
    (erased_beta_stable_joint_descent heq hs) (erased_beta_stable_joint_subst heq hs)
    erased_beta_stable_joint_head hΓ ha ⟨_, ht⟩ hcalc HG RA hcalc'

end Lean4Lean.VEnv.Strengthening
