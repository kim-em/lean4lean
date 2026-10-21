import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonOutputComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureFunctionDomain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDependentCarrierBeta

/-! # Singleton guard transport for mixed argument computations

The generated family guard depends only on parameters and indices. Their beta
reductions compose with its stored beta futures. Other arguments can compute
arbitrarily and change the residual telescope; its actual converted context
interprets the guard's stored substitution future. No general forward
computation law for proposition comparisons is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private singleton_compute_telescope
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonOutputComputation
open private instOuter_beta
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDependentCarrierBeta
variable [Params]

/-- A computed residual telescope transports a future family guard whenever
its opened parameter and index vectors beta reduce to the target vectors. The actual context conversion
is constructed from the source prefix and its argument computations. -/
theorem SingletonPrefixCode.Valid.guard_compute_of_provider_beta
    {C : SingletonPrefixCode} (V : C.Valid)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (ds, result))
    (HG : C.guardWith (BetaStableFamily Cmp) (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args')
    (hcalc' : C.telescope args' = some (ds', result'))
    (EP : List.Forall₂ ProofShape.BetaRed
      ((openPrefixArguments (proofEraseCtx Γ) ds (args.map (proofErase Γ))).take C.data.numParams)
      ((openPrefixArguments (proofEraseCtx Γ) ds' args').take C.data.numParams))
    (EI : List.Forall₂ ProofShape.BetaRed
      (((openPrefixArguments (proofEraseCtx Γ) ds (args.map (proofErase Γ))).drop
        C.data.indexOffset).take C.data.numIndices)
      (((openPrefixArguments (proofEraseCtx Γ) ds' args').drop C.data.indexOffset).take C.data.numIndices)) :
    C.guardWith (BetaStableFamily Cmp) (proofEraseCtx Γ) ds' args' := by
  obtain ⟨program, hg⟩ := V.generate ha
  have hd := (Prod.mk.inj (Option.some.inj ((V.telescope_eq hΓ hg ht).symm.trans hcalc))).1
  have hlen : args.length = args'.length := by simpa only [List.length_map] using RA.length_eq
  have HO := hcalc'
  simp only [SingletonPrefixCode.telescope, ← hlen] at HO
  obtain ⟨ds₀, result₀, HO₀, _, _, domains', W, HD⟩ :=
    singleton_compute_telescope hstep hsubst hhead hΓ V.registered V.levels_wf V.recType_eq hg ht RA
  cases Option.some.inj (HO₀.symm.trans HO)
  unfold SingletonPrefixCode.guardWith SingletonFamilyGuardWith at HG ⊢
  dsimp only at HG ⊢
  have HP := (EP.append' EI).append' (.cons (ProofShape.BetaRed.refl (e := .proof)) .nil)
  have HB := HG.beta (instOuter_beta HP _) (instOuter_beta HP _)
  rw [← hd, ← proofEraseDomains_context] at HB
  have HH := HB.defeqCtx (by trivial) W
  simpa only [proofEraseDomains_context, HD] using HH

private theorem opened_parts
    (hlen : ds.length = ds'.length) (ha : args.length = args'.length)
    (HV : contextVars (ds.reverse ++ Δ) ds.length 0 = contextVars (ds'.reverse ++ Δ) ds'.length 0)
    (EP : List.Forall₂ ProofShape.BetaRed (args.take p) (args'.take p))
    (EI : List.Forall₂ ProofShape.BetaRed ((args.drop offset).take n) ((args'.drop offset).take n)) :
    List.Forall₂ ProofShape.BetaRed
        ((openPrefixArguments Δ ds args).take p) ((openPrefixArguments Δ ds' args').take p) ∧
      List.Forall₂ ProofShape.BetaRed
        (((openPrefixArguments Δ ds args).drop offset).take n)
        (((openPrefixArguments Δ ds' args').drop offset).take n) := by
  unfold openPrefixArguments
  rw [HV, hlen]
  constructor
  · simp only [List.take_append, ← List.map_take, List.length_map, ha]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact EP.imp (fun _ _ H => H.liftN)
    · exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)
  · simp only [List.drop_append, ← List.map_drop, List.take_append, ← List.map_take,
      List.length_map, List.length_drop, ha]
    apply List.Forall₂.append'
    · apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact EI.imp (fun _ _ H => H.liftN)
    · exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)

/-- Beta-reducing supplied parameter and index slices preserve the entire future
guard through argument computation. Other supplied arguments may compute
arbitrarily, and the residual telescope need not be empty or unchanged. -/
theorem SingletonPrefixCode.Valid.guard_compute_of_family_args_beta
    {C : SingletonPrefixCode} (V : C.Valid)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some (ds, result))
    (HG : C.guardWith (BetaStableFamily Cmp) (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args')
    (hcalc' : C.telescope args' = some (ds', result'))
    (EP : List.Forall₂ ProofShape.BetaRed
      ((args.map (proofErase Γ)).take C.data.numParams) (args'.take C.data.numParams))
    (EI : List.Forall₂ ProofShape.BetaRed
      (((args.map (proofErase Γ)).drop C.data.indexOffset).take C.data.numIndices)
      ((args'.drop C.data.indexOffset).take C.data.numIndices)) :
    C.guardWith (BetaStableFamily Cmp) (proofEraseCtx Γ) ds' args' := by
  obtain ⟨program, hg⟩ := V.generate ha
  have hd := (Prod.mk.inj (Option.some.inj ((V.telescope_eq hΓ hg ht).symm.trans hcalc))).1
  have hlen : args.length = args'.length := by simpa only [List.length_map] using RA.length_eq
  have HO := hcalc'
  simp only [SingletonPrefixCode.telescope, ← hlen] at HO
  obtain ⟨ds₀, result₀, HO₀, RT, HV, _⟩ :=
    singleton_compute_telescope hstep hsubst hhead hΓ V.registered V.levels_wf V.recType_eq hg ht RA
  cases Option.some.inj (HO₀.symm.trans HO)
  have HL := RT.length_eq
  rw [hd] at HL HV
  have HV' : contextVars (ds.reverse ++ proofEraseCtx Γ) ds.length 0 =
      contextVars (ds'.reverse ++ proofEraseCtx Γ) ds'.length 0 := by
    rw [HL]
    exact HV _ _
  obtain ⟨HP, HI⟩ := opened_parts HL RA.length_eq HV' EP EI
  exact V.guard_compute_of_provider_beta hstep hsubst hhead hΓ ha ht hcalc HG RA hcalc' HP HI

/-- A singleton/argument fork closes when its supplied family parameters and
indices beta reduce while its other arguments compute arbitrarily. The target telescope, target guard,
new certified primitive and whole output computation are all constructed;
none is assumed separately. This includes dependent residual telescopes. -/
theorem SingletonPrefixCode.Valid.certified_residual_of_family_args_beta
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
    (EP : List.Forall₂ ProofShape.BetaRed
      ((args.map (proofErase Γ)).take C.data.numParams) (args'.take C.data.numParams))
    (EI : List.Forall₂ ProofShape.BetaRed
      (((args.map (proofErase Γ)).drop C.data.indexOffset).take C.data.numIndices)
      ((args'.drop C.data.indexOffset).take C.data.numIndices)) :
    ∃ ds' result', C.telescope args' = some (ds', result') ∧
      ErasedBetaStableJoint D (proofEraseCtx Γ)
        (ProofShape.mkApps (.const C.data.name C.levels) args')
        (C.output (proofEraseCtx Γ) ds' args') ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (C.output (proofEraseCtx Γ) ds (args.map (proofErase Γ)))
        (C.output (proofEraseCtx Γ) ds' args') := by
  obtain ⟨ds', result', HO⟩ := V.telescope_compute_exists
    (erased_beta_stable_joint_descent heq hs) (erased_beta_stable_joint_subst heq hs)
    erased_beta_stable_joint_head hΓ ha ⟨_, ht⟩ RA
  have HG' := V.guard_compute_of_family_args_beta
    (erased_beta_stable_joint_descent heq hs) (erased_beta_stable_joint_subst heq hs)
    erased_beta_stable_joint_head hΓ ha ⟨_, ht⟩ hcalc HG RA HO EP EI
  exact ⟨ds', result', HO, V.certified_residual heq hs hΓ ha ht hn hcalc HG RA HO HG'⟩

end Lean4Lean.VEnv.Strengthening
