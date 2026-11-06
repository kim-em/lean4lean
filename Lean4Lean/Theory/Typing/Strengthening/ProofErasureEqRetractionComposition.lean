import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetractionMinimum

/-! # Compose reverse-renaming witnesses through further proof consumption

Exact reverse renamings compose without a bound on inserted binders. A typed
proof binder has no retained erased occurrences, so its consumption can be
followed by reinsertion and the previously chosen reverse renaming.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Ordinary completion is reverse-renaming completion with the identity map. -/
theorem EqTargetPrefixCompletion.retraction
    (H : EqTargetPrefixCompletion Δ v w original Ξ source) :
    EqTargetPrefixRetraction Δ v w original Ξ source :=
  ⟨Ξ, ProofShape.Subst.id, ContextRenaming.identity,
    by simpa only [ProofShape.subst_id] using H⟩

/-- Pull a completed reverse-renaming witness back along another exact
renaming. The composed map retains both context interpretations and exact
oracle transport; no single-insertion restriction is needed. -/
theorem EqTargetPrefixRetraction.pullback
    (H : EqTargetPrefixRetraction Δ v w original Ξ' (source.subst τ))
    (W : ContextRenaming Ξ Ξ' τ) :
    EqTargetPrefixRetraction Δ v w original Ξ source := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  exact ⟨Θ, τ.comp κ, W.compose WK, by simpa only [ProofShape.subst_subst] using HP⟩

/-- Consuming any raw argument at a proof-valued binder and reinserting that
binder restores a typed erased source literally. The argument needs no raw
typing or representative because the consumed variable has no retained use. -/
theorem proofErase_proof_inst_lift
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (he : env.HasType univs (P :: Γ) e T) (x : ProofShape) :
    ((proofErase (P :: Γ) e).inst x).liftN 1 = proofErase (P :: Γ) e := by
  rw [ProofShape.inst_eq_subst]
  change ((proofErase (P :: Γ) e).subst (ProofShape.Subst.one x)).liftN 1 = _
  rw [ProofShape.liftN_subst]
  apply proofErase_subst_retained (show OnCtx (P :: Γ) (env.IsType univs) from ⟨hΓ, _, hP⟩) he
  intro i B hl hn
  cases i with
  | zero => exact (hn ⟨P.lift, .bvar .zero, hP.weak henv.ordered⟩).elim
  | succ i =>
    simp [ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.id,
      ProofShape.liftN, liftVar, Nat.add_comm]

/-- A further proof-binder consumption preserves an existing retraction.
This can be iterated after earlier reverse renamings and component/eta
histories. The current full source is typed; changed retained annotations
above the consumed binder still need their own transport theorem. -/
theorem EqTargetPrefixRetraction.consume_proof_binder
    (H : EqTargetPrefixRetraction Δ v w original (A :: Ξ) source)
    (HT : TypedSource (A :: Ξ) source) (SD : DomainSort Ξ A .zero)
    (x : ProofShape) : EqTargetPrefixRetraction Δ v w original Ξ (source.inst x) := by
  obtain ⟨Γ, P, hΓ, EΓ, hP, EP⟩ := SD
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have Ectx : proofEraseCtx (P :: Γ) = A :: Ξ := by simp only [proofEraseCtx, EP, EΓ]
  obtain ⟨Γ₀, e, T, hΓ₀, EΓ₀, he, Ee⟩ := HT
  have C := proofEraseCtx_defeq hΓ₀ hΓP (EΓ₀.trans Ectx.symm)
  have he' := he.defeqDFC henv C
  have Ee' : proofErase (P :: Γ) e = source :=
    (proofErase_defeqCtx hΓ₀ C he).symm.trans Ee
  have WK : ContextRenaming Ξ (A :: Ξ) (fun i => .bvar (liftVar 1 i 0)) := by
    simpa only [Ectx, EΓ] using ContextRenaming.of_liftN hΓ hΓP Ctx.LiftN.one
  have ES : (source.inst x).subst (fun i => .bvar (liftVar 1 i 0)) = source := by
    rw [subst_bvar_liftN, ← Ee']
    exact proofErase_proof_inst_lift hΓ hP he' x
  exact (show EqTargetPrefixRetraction Δ v w original (A :: Ξ)
    ((source.inst x).subst (fun i => .bvar (liftVar 1 i 0))) from ES.symm ▸ H).pullback WK

/-- At an actual base endpoint map, an existing retraction is preserved or
the consumed domain lacks a Prop witness. The interpretation and exact
argument come from the endpoint constructor. Retained annotations above this
base map are not covered by this theorem. -/
theorem EqTargetPrefixRetraction.endpoint_map_or_unwitnessed_domain
    (H : EqTargetPrefixRetraction Δ v w original Ξ source)
    (HT : TypedSource Ξ source) (W : PiInertEndpointMap Ξ Ξ' τ) :
    EqTargetPrefixRetraction Δ v w original Ξ' (source.subst τ) ∨
      ∃ A x, Ξ = A :: Ξ' ∧ τ = ProofShape.Subst.one x ∧
        ContextSubstitution (A :: Ξ') Ξ' (ProofShape.Subst.one x) ∧
        ¬ DomainSort Ξ' A .zero := by
  classical
  cases W with
  | identity => exact .inl (by simpa only [ProofShape.subst_id] using H)
  | @inst A _ x W =>
    by_cases SD : DomainSort Ξ' A .zero
    · exact .inl (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        H.consume_proof_binder HT SD x)
    · exact .inr ⟨A, x, rfl, rfl, W, SD⟩

/-- Concrete finite histories interleaving existing spine execution with
further proof-binder consumption. Each consumption retains its actual context
interpretation and typed source. This does not assert that arbitrary retained
annotation histories are represented by these constructors. -/
inductive EqRepeatedProofHistory (D : Definitions) (slots : Nat) :
    List ProofShape → ProofShape → List ProofShape → ProofShape → Prop where
  | spine : EqSpineConsumptionHistory D slots Ξ source Θ out →
      EqRepeatedProofHistory D slots Ξ source Θ out
  | trans : EqRepeatedProofHistory D slots Ξ source Θ mid →
      EqRepeatedProofHistory D slots Θ mid Ω out →
      EqRepeatedProofHistory D slots Ξ source Ω out
  | proof : TypedSource (A :: Ξ) source → DomainSort Ξ A .zero →
      ContextSubstitution (A :: Ξ) Ξ (ProofShape.Subst.one x) →
      EqRepeatedProofHistory D slots (A :: Ξ) source Ξ (source.inst x)

/-- Any finite number of these proof consumptions preserves the same target
readout witness, interleaved with component computations and eta execution.
The composed reverse map has no prescribed insertion count. -/
theorem EqRepeatedProofHistory.retraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqRepeatedProofHistory D slots Ξ source Θ out)
    (HP : EqTargetPrefixRetraction Δ v w original Ξ source) :
    EqTargetPrefixRetraction Δ v w original Θ out := by
  induction H with
  | spine H => exact H.target_prefix_retraction heq hs hΔ ht HP
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ HP)
  | proof HT SD _ => exact HP.consume_proof_binder HT SD _

/-- An actual nonstructural head loss after a repeated proof history reads
the original target equation. All later typings and the selected primitive
are those of the actual endpoint; no target inhabitants for removed or
unused binders are supplied. -/
theorem EqRepeatedProofHistory.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqRepeatedProofHistory D slots Ξ source Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HP : EqTargetPrefixRetraction Δ v w [α,a,M,minor,b] Ξ source)
    (HT : TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Δ a b α :=
  (H.retraction heq hs hΔ ht HP).read_loss heq hs hreg hoff hD hΔ ht HT HR HN Hstruct

end Lean4Lean.VEnv.Strengthening
