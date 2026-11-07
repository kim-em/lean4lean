import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorProjectionContinuation

/-! # Structure projection readout across an actual endpoint substitution

A structure guard need not survive substitution to retain its field-selection
equation. Replay supplies actual records, ordinary typed substitution supplies
their images, and raw projection iota supplies the equation at those images.
The subsequent projection path is analyzed in its own scope and stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- A closed rigid record assignment rules out every pending application,
including a different typed representative in the same erased context. -/
theorem TypedSource.closed_record_pending_nil
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hm : env.HasType univs Γ m (.const family []))
    (HT : TypedSource Δ (ProofShape.mkApps (proofErase Γ m) pending)) : pending = [] := by
  cases pending with
  | nil => rfl
  | cons x rest =>
    obtain ⟨Γ₀, e, T, hΓ₀, EΓ₀, ht, Ee⟩ :=
      typed_spine_head (f := .app (proofErase Γ m) x) (args := rest) HT
    obtain ⟨f, a, rfl, hn, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨A, B, hf, ha⟩ := ht.app_inv henv hΓ₀
    have W := proofEraseCtx_defeq hΓ hΓ₀ (EΓ.trans EΓ₀.symm)
    have hm' := hm.defeqDFC henv W
    have Em' := (proofErase_defeqCtx hΓ W hm).symm
    obtain ⟨_, HE⟩ := (proofErase_reflect hΓ₀ hf hm' (Ef.trans Em'.symm)).2
      (not_isProof_fn hΓ₀ hf ha hn)
    have hf' := ((HE.defeq hΓ₀).of_r henv hΓ₀ hm').hasType.1
    obtain ⟨_, hF⟩ := hf'.isType henv hΓ₀
    exact (IsDefEqU.rigidApp_forallE_inv (args := []) henv hΓ₀
      (henv.projectionRigid hi) hF (hf'.uniqU henv hΓ₀ hf)).elim

/-- Native structure eta at a closed record supplies actual short and expanded
records after any interpreted endpoint substitution. Selecting the expanded
type field returns the projection of the short image in exactly one primitive.
No substitution of the native recovery or its computation is asserted. -/
theorem proofErase_closed_structure_projection_substitution
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hj : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (ht : env.HasType univs Γ (.proj family i m) (.sort u))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ) :
    ∃ Γ₀ short expanded, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Θ ∧
      env.HasType univs Γ₀ short (.const family []) ∧
      env.HasType univs Γ₀ expanded (.const family []) ∧
      proofErase Γ₀ short = (proofErase Γ m).subst τ ∧
      proofErase Γ₀ expanded = target.subst τ ∧
      Primitive D (.proj family i (target.subst τ))
        (.proj family i ((proofErase Γ m).subst τ)) := by
  have RI : Primitive D (.proj family i target) (.proj family i (proofErase Γ m)) :=
    proofErase_closed_structure_type_projection_primitive hstep hi hj hΓ hm ht H
  obtain ⟨expanded, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeMaskedStructureExpansion_descent hstep) hΓ hm rfl rfl (.base H)
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ rfl
  have hm' : env.HasType univs Γ₀ (m.subst σ) (.const family []) :=
    hm.subst henv.orderedStrong HS hΓ₀
  have he' : env.HasType univs Γ₀ (expanded.subst σ) (.const family []) :=
    HE.hasType.2.subst henv.orderedStrong HS hΓ₀
  refine ⟨Γ₀, m.subst σ, expanded.subst σ, hΓ₀, EΓ₀, hm', he',
    proofErase_subst_with hΓ₀ HS hm ES, ?_, ?_⟩
  · rw [proofErase_subst_with hΓ₀ HS HE.hasType.2 ES, EE]
  · simpa only [ProofShape.subst] using RI.subst (σ := τ)

/-- The native structure case can be analyzed after the endpoint substitution
using only the actual later projection path. Either the short image's
projection reaches the output with strictly fewer primitives, or the existing
function-eta alternative occurs at a reachable pair in the later scope.
The guard remains in its original scope and may use an unrelated relation. -/
theorem pi_inert_substituted_structure_projection_count_readout_or_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedComputeCount (PiInertStage D n) bound Θ (.proj family 0 (target.subst τ)) out) :
    (∃ later j, j < bound ∧ ScopedComputeCount (PiInertStage D later) j Θ
      (.proj family 0 ((proofErase Γ m).subst τ)) out) ∨
    ∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Θ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.subst τ) out := by
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  obtain ⟨Γ₀, short, expanded, hΓ₀, EΓ₀, _, he, _, EE, RI⟩ :=
    proofErase_closed_structure_projection_substitution hstep hi (by omega) hΓ hm ht H W
  have R' : ScopedComputeCount (PiInertStage D n) bound (proofEraseCtx Γ₀)
      (.proj family 0 (proofErase Γ₀ expanded)) out := by rw [EE, EΓ₀]; exact R
  have RI' : Primitive D (.proj family 0 (proofErase Γ₀ expanded))
      (.proj family 0 ((proofErase Γ m).subst τ)) := by rw [EE]; exact RI
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ₀ he RI' hout hproj R' with ⟨later, j, hj, RJ⟩ | HF
  · exact .inl ⟨later, j, hj, EΓ₀ ▸ RJ⟩
  · exact .inr ⟨Γ₀, hΓ₀, EΓ₀, EE ▸ HF⟩

/-- When the short image is reachable before the charged structure occurrence,
full projection minimality excludes the readout branch. The remaining eta is
an actual function eta on a pair in the later scope. This conclusion neither
moves a guarded body path through substitution nor infers reachability of the
expanded image from semantic equality alone. -/
theorem pi_inert_substituted_structure_projection_minimum_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (RP : ScopedComputeCount (PiInertStage D prefixStage) before Θ original ((proofErase Γ m).subst τ))
    (R : ScopedComputeCount (PiInertStage D n) bound Θ (.proj family 0 (target.subst τ)) out)
    (hcost : before + 1 + bound ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Θ
      (.proj family 0 original) out → cost ≤ j) :
    ∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Θ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.subst τ) out := by
  rcases pi_inert_substituted_structure_projection_count_readout_or_function_eta
      heq hs hstep hi hp hf hz hadm hshape hD hΓ hm H W hout hproj R with
      ⟨later, j, hj, RJ⟩ | HF
  · have Ralt := (RP.mono (pi_inert_stage_mono (Nat.le_max_left prefixStage later))).proj.trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right prefixStage later)))
    have HH := hmin _ _ Ralt
    omega
  · exact HF

/-- A structure root followed only by beta in a consumed eta body can be
relayed to function eta in the outer scope. The prefix to the short record is
constructed by replacing the lambda body before consumption, so its guarded
computation is never substituted. The actual argument supplies the endpoint
interpretation. Typing forces the pending spine after consumption to be empty; this is not
assumed of the argument computation. Positive-cost body tails and additional
retained frames remain open. -/
theorem pi_inert_consumed_structure_projection_minimum_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = A :: Δ)
    (hm : env.HasType univs Γ m (.const family []))
    (RB : ScopedComputeCount (PiInertStage D bodyStage) pb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) (proofErase Γ m))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (RBeta : BetaRed target body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') major)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.proj family 0 major) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (hcost : cp + 1 + cd + pb + 1 + ca + cs + cf ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 original) out → cost ≤ j) :
    ∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.inst x') out := by
  obtain ⟨_, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have WP : ContextSubstitution (proofEraseCtx Γ) Δ (ProofShape.Subst.one x') := EΓ ▸ WI
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  obtain ⟨Γ₀, short, expanded, hΓ₀, EΓ₀, hshort, _, Eshort, _, _⟩ :=
    proofErase_closed_structure_projection_substitution (D := D) hstep hi (by omega)
      hΓ hm ht H WP
  have Rlocal := pi_inert_counted_lambda_body_replace
    (ScopedComputeCount.beta (Step := PiInertStage D n) (Δ := Δ)
      (BetaRed.refl (e := ProofShape.mkApps f args))) HR RD RB RX
    (ScopedComputeCount.beta (Step := PiInertStage D n)
      (BetaRed.refl (e := ProofShape.mkApps ((proofErase Γ m).inst x') xs')))
  have HTshort := HT.pi_inert_compute heq hs Rlocal.forget
  have HTshort' : TypedSource Δ (ProofShape.mkApps (proofErase Γ₀ short) xs') := by
    simpa only [Eshort, ProofShape.mkApps, ProofShape.inst_eq_subst,
      ProofShape.Subst.liftN] using HTshort
  have EX := TypedSource.closed_record_pending_nil hi hΓ₀ EΓ₀ hshort HTshort'
  subst xs'
  simp only [ProofShape.mkApps] at RS
  have Rshort := pi_inert_counted_lambda_body_replace RP HR RD RB RX
    (ScopedComputeCount.beta (Step := PiInertStage D n)
      (BetaRed.refl (e := (proofErase Γ m).inst x')))
  have Rshort' : ScopedComputeCount (PiInertStage D (max bodyStage n)) (cp+1+cd+pb+ca) Δ
      original ((proofErase Γ m).subst (ProofShape.Subst.one x')) := by
    simpa only [Nat.add_zero, ProofShape.mkApps, ProofShape.inst_eq_subst,
      ProofShape.Subst.liftN] using Rshort
  have Rbeta' : ScopedComputeCount (PiInertStage D n) 0 Δ
      (target.subst (ProofShape.Subst.one x')) (body'.inst x') := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      (ScopedComputeCount.beta (Δ := Δ) (Step := PiInertStage D n)
        (RBeta.subst (σ := ProofShape.Subst.one x')))
  have Rtail : ScopedComputeCount (PiInertStage D n) (cs+cf) Δ
      (.proj family 0 (target.subst (ProofShape.Subst.one x'))) out := by
    simpa only [Nat.zero_add] using (Rbeta'.trans RS).proj.trans RF
  have HH := pi_inert_substituted_structure_projection_minimum_function_eta
    heq hs hstep hi hp hf hz hadm hshape hD hΓ hm H WP hout hproj Rshort' Rtail
    (cost := cost) (by omega) hmin
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HH

end Lean4Lean.VEnv.Strengthening
