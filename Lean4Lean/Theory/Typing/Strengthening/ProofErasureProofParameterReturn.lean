import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralHead
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureControlReturn

/-! # Exact return for neutral families with dependent proof parameters

Head-and-arity readout alone leaves an arbitrary exposed argument vector. Typed
replay and the original proof telescope force every exposed argument to erase to
the proof marker. No native certificates for those arguments are required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A universe-ending telescope whose domains are propositions, including
propositions depending on earlier proof parameters. -/
inductive ProofSortTelescope : List VExpr → VExpr → Nat → VLevel → Prop where
  | sort : ProofSortTelescope Γ (.sort u) 0 u
  | forallE : env.HasType univs Γ A (.sort .zero) →
      ProofSortTelescope (A :: Γ) B n u →
      ProofSortTelescope Γ (.forallE A B) (n+1) u

/-- Ordinary typed substitution preserves the proof-only telescope. -/
theorem ProofSortTelescope.subst (H : ProofSortTelescope Γ T n u)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.SubstEq env univs Γ' σ σ Γ) :
    ProofSortTelescope Γ' (T.subst σ) n u := by
  induction H generalizing Γ' σ with
  | sort => exact .sort
  | forallE hA _ ih =>
    have hA' := hA.subst henv.orderedStrong W hΓ'
    exact .forallE hA' (ih ⟨hΓ', _, hA'⟩ (W.lift henv.ordered hA))

/-- Forgetting the domain restriction gives the telescope used by neutral-head
readout. -/
theorem ProofSortTelescope.sortTelescope (H : ProofSortTelescope Γ T n u) :
    DemandProfile.SortTelescope n T := by
  induction H with
  | sort => exact .sort
  | forallE _ _ ih => exact .forallE ih

/-- The literal telescope has exactly the binders needed for typed spine
inversion, independently of the supplied proof representatives. -/
theorem ProofSortTelescope.takeForalls (H : ProofSortTelescope Γ T n u) :
    ∃ doms, T.takeForalls n = some (doms, .sort u) := by
  induction H with
  | sort => exact ⟨[], rfl⟩
  | @forallE Γ A B n u _ _ ih =>
    obtain ⟨doms, E⟩ := ih
    exact ⟨A :: doms, by simp [VExpr.takeForalls, E]⟩

/-- Every fully supplied proof telescope has the advertised universe result
and the same erased argument vector, regardless of its proof representatives. -/
theorem ProofSortTelescope.arguments (H : ProofSortTelescope Γ T args.length u)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HW : InstForallsC env univs Γ T args result) :
    result = .sort u ∧ args.map (proofErase Γ) = List.replicate args.length .proof := by
  induction HW generalizing u with
  | nil => cases H; exact ⟨rfl, rfl⟩
  | @cons a A args result B ha HW ih =>
    cases H with
    | forallE hA HB =>
      have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq ⟨hΓ, _, hA⟩ ha
      have HI : ProofSortTelescope Γ (B.inst a) args.length u := by
        simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using HB.subst hΓ W
      obtain ⟨ER, EA⟩ := ih HI
      exact ⟨ER, by simp only [List.map_cons, List.length_cons, List.replicate_succ,
        proofErase_eq_proof.2 ⟨_, ha, hA⟩, EA]⟩

/-- A typed telescope walk types its application spine at the final residual. -/
theorem typed_telescope_application (hf : env.HasType univs Γ f T)
    (HW : InstForallsC env univs Γ T args result) :
    env.HasType univs Γ (VExpr.mkApps f args) result := by
  induction HW generalizing f with
  | nil => exact hf
  | cons ha _ ih => exact ih (hf.app ha)

open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- A visible variable spine retains an actual argument at every position,
including proof-erased positions. -/
theorem proofErase_bvar_spine_inv
    (H : proofErase Γ e = ProofShape.mkApps (.bvar i) args) :
    ∃ original, e = VExpr.mkApps (.bvar i) original ∧ args = original.map (proofErase Γ) := by
  induction args using List.snoc_induction generalizing e with
  | nil => exact ⟨[], erase_bvar_inv H, rfl⟩
  | snoc args a ih =>
    rw [ProofShape.mkApps_snoc] at H
    obtain ⟨f, a₀, rfl, _, Hf, Ha⟩ := erase_app_inv H
    obtain ⟨args₀, rfl, rfl⟩ := ih Hf
    exact ⟨args₀ ++ [a₀], (VExpr.mkApps_snoc ..).symm, by simp [Ha]⟩

/-- Full enriched computation from a saturated neutral family with dependent
proof parameters returns by beta alone to its exact original erasure. Readout
does not constrain intermediate syntax; typed replay forces the final arguments
to be proofs at the original head's telescope. -/
theorem static_structure_neutral_proof_parameter_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T)
    (HP : ProofSortTelescope Γ T args.length u)
    (HW : InstForallsC env univs Γ T args result)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) out) :
    BetaRed out (proofErase Γ (VExpr.mkApps (.bvar i) args)) := by
  obtain ⟨rfl, EA⟩ := HP.arguments hΓ HW
  have ht := typed_telescope_application hf HW
  obtain ⟨rawArgs, hlen, RB⟩ := DemandProfile.static_structure_neutral_telescope_head_readout
    heq hs hΓ hf HP.sortTelescope HW R
  have RC := R.trans (.beta RB)
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl rfl RC
  obtain ⟨actualArgs, rfl, rfl⟩ := proofErase_bvar_spine_inv EE
  simp only [List.length_map] at hlen
  obtain ⟨doms, HD⟩ := HP.takeForalls
  obtain ⟨res, HW', _⟩ := HasType.mkApps_telescope henv hΓ hf ⟨_, HE.hasType.2⟩ (hlen.symm ▸ HD)
  have HP' : ProofSortTelescope Γ T actualArgs.length u := hlen.symm ▸ HP
  obtain ⟨_, EA'⟩ := HP'.arguments hΓ HW'
  have EF : proofErase Γ (.bvar i) = .bvar i := by
    obtain ⟨_, hT⟩ := hf.isType henv hΓ
    exact if_neg ((DemandProfile.Fits.of_sortTelescope hΓ hT HP.sortTelescope).not_isProof
      hΓ (DemandProfile.spineDemand_valid args.length).visible hf)
  rw [proofErase_mkApps hΓ ht (not_isProof_of_sort hΓ ht), EF, EA]
  simpa only [EA', hlen] using RB

/-- A common native certificate against a neutral proof-parameter family
recovers the exact assigned type after beta cleanup. -/
theorem CommonNativeArgument.exact_proof_parameter_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T)
    (HP : ProofSortTelescope Γ T args.length u)
    (HW : InstForallsC env univs Γ T args result)
    (H : CommonNativeArgument D Γ x (VExpr.mkApps (.bvar i) args)) (hn : ¬ IsProof Γ x) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ (VExpr.mkApps (.bvar i) args)) := by
  obtain ⟨shared, RN, RC⟩ := H hn
  exact RN.convert (.beta (static_structure_neutral_proof_parameter_return heq hs hΓ hf HP HW RC))

/-- Changing a binder from a neutral proof-parameter family to any computed
representative preserves the body's selected native output exactly. -/
theorem static_structure_proof_parameter_forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T)
    (HP : ProofSortTelescope Γ T args.length u)
    (HW : InstForallsC env univs Γ T args result)
    (HAC : env.IsDefEq univs Γ (VExpr.mkApps (.bvar i) args) C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.bvar i) args)) (proofErase Γ C))
    (ht : env.HasType univs (VExpr.mkApps (.bvar i) args :: Γ) e B)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (VExpr.mkApps (.bvar i) args :: Γ))
      (proofErase (VExpr.mkApps (.bvar i) args :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out :=
  proofErase_static_structure_union_recovery_backward_context heq hs hΓ HAC.symm
    (.beta (static_structure_neutral_proof_parameter_return heq hs hΓ hf HP HW RA)) ht RN

/-- Beta with a commonly recovered argument assigned a neutral proof-parameter
family preserves every selected native result. No exact argument recovery is
assumed; it follows from the common certificate and the return theorem. -/
theorem static_structure_proof_parameter_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar i) T)
    (HP : ProofSortTelescope Γ T args.length u)
    (HW : InstForallsC env univs Γ T args result)
    (hb : env.HasType univs (VExpr.mkApps (.bvar i) args :: Γ) b B)
    (hx : env.HasType univs Γ x (VExpr.mkApps (.bvar i) args))
    (HX : CommonNativeArgument D Γ x (VExpr.mkApps (.bvar i) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam (VExpr.mkApps (.bvar i) args) b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out := by
  obtain ⟨rfl, _⟩ := HP.arguments hΓ HW
  exact static_structure_root_beta_native_recovery heq hs hΓ (typed_telescope_application hf HW) hb hx
    (HX.exact_proof_parameter_family heq hs hΓ hf HP HW) RN

end Lean4Lean.VEnv.Strengthening
