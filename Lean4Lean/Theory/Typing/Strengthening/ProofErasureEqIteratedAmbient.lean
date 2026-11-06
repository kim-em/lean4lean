import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEqCoreExclusion

/-! # Eq completion under successive unused binder insertions

Unused binders may be inserted at different depths after earlier eta binders.
Keep each actual insertion rather than requiring their composite to be one
contiguous block. A head-losing primitive descends as one primitive at each
insertion before the original target completion is read.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Target completion with finitely many additional, actually typed unused
binder insertions. No inserted type needs an inhabitant in the target context.
This extends the single-block witness; closure under arbitrary wrapper bodies
and changed displayed annotations is not part of the definition. -/
inductive IteratedAmbientEqCompletion (Δ : List VExpr) (v w : VLevel) (original : List VExpr) :
    List ProofShape → ProofShape → Prop where
  | base : EqHeadCompletion Δ v w original Ξ e → IteratedAmbientEqCompletion Δ v w original Ξ e
  | insert (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
      (W : Ctx.LiftN count offset Γ Γ') (hf : env.HasType univs Γ f T) :
      IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ) (proofErase Γ f) →
      IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ')
        ((proofErase Γ f).liftN count offset)

/-- Every iterated completion still has the original target's arity bound.
Insertion preserves the constant head and all argument positions. -/
theorem IteratedAmbientEqCompletion.arity
    (H : IteratedAmbientEqCompletion Δ v w original Ξ source) :
    ∃ ls args, source = ProofShape.mkApps (.const ``Eq.rec ls) args ∧ args.length ≤ original.length := by
  induction H with
  | base H => exact H.arity
  | insert hΓ hΓ' W hf H ih =>
    obtain ⟨ls, args, E, hlen⟩ := ih
    rw [E, ProofShape.liftN_mkApps, ProofShape.liftN]
    exact ⟨ls, _, rfl, by simpa only [List.length_map] using hlen⟩

/-- Read a head-losing primitive below every retained unused insertion.
Each descent preserves the primitive's finite stage and its exact lifted
output. Wrapped-head preservation under lifting transfers the loss condition
backwards, allowing the original semantic completion to read the equation. -/
theorem IteratedAmbientEqCompletion.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HR : PiInertStage D n Ξ source target) (HN : ¬ WrappedConstHead ``Eq.rec target) :
    env.IsDefEq univs Δ a b α := by
  induction H generalizing target with
  | base H => exact H.read_loss heq hs hreg hoff hD hΔ ht HR HN
  | insert hΓ hΓ' W hf H ih =>
    obtain ⟨f', HE, HR', EE⟩ := pi_inert_stage_rule_descent heq hs hΓ hΓ' W hf HR
    apply ih HR'
    intro HH
    exact HN (EE ▸ HH.liftN _ _)

/-- Every completion has an actual typing at its current raw source.
The insertion case uses ordinary weakening at the recorded actual context. -/
theorem IteratedAmbientEqCompletion.typed
    (H : IteratedAmbientEqCompletion Δ v w original Ξ source) : TypedSource Ξ source := by
  cases H with
  | base H =>
    obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, hΓ', W, EΓ, hf, _, _, E⟩ := H
    exact ⟨Γ', _, _, hΓ', EΓ, hf.weakN henv W, (proofErase_liftN hΓ hΓ' W hf).trans E⟩
  | insert hΓ hΓ' W hf H =>
    exact ⟨_, _, _, hΓ', rfl, hf.weakN henv W, proofErase_liftN hΓ hΓ' W hf⟩

/-- A concrete domain-sort witness permits adding a new unused binder to
any iterated completion. The domain is realized in the completion's typed
source context; no inhabitant of that domain is needed in the target context. -/
theorem IteratedAmbientEqCompletion.under_domain
    (H : IteratedAmbientEqCompletion Δ v w original Ξ source)
    (SD : DomainSort Ξ A u) :
    IteratedAmbientEqCompletion Δ v w original (A :: Ξ) (source.liftN 1) := by
  obtain ⟨Γ, f, F, hΓ, rfl, hf, rfl⟩ := H.typed
  obtain ⟨A₀, hA, EA⟩ := SD.realize hΓ
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HH := IteratedAmbientEqCompletion.insert hΓ hΓA Ctx.LiftN.one hf H
  simpa only [proofEraseCtx, EA] using HH

/-- Computing the annotation of an unused wrapper binder preserves the
completion of its lifted payload under the new displayed domain. Its new
sort witness comes from actual replay. No old recovery guard is converted
or copied into the changed raw context. -/
theorem IteratedAmbientEqCompletion.under_computed_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : IteratedAmbientEqCompletion Δ v w original Ξ source)
    (SD : DomainSort Ξ A u) (RD : ScopedCompute Step Ξ A A') :
    IteratedAmbientEqCompletion Δ v w original (A' :: Ξ) (source.liftN 1) := by
  obtain ⟨Γ, A₀, hΓ, rfl, hA, rfl⟩ := SD
  obtain ⟨A₁, HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl RD
  exact H.under_domain ⟨Γ, A₁, hΓ, rfl, HA.hasType.2, EA⟩

/-- A concrete singleton failure now excludes every completion with any
finite sequence of extra unused insertions, not only one inserted block.
The exact singleton, counted paths and tracked hole are retained. This does
not assert coverage of arbitrary histories by the extended completion. -/
def IteratedAmbientSingletonFailure (D : Definitions) (Δ : List VExpr) (v w : VLevel)
    (original : List VExpr) (budget : Nat) : Prop :=
  ∃ Ξ Θ n source endpoint ls args target cp ct, ∃ C : ScopedHole Ξ Θ,
    cp+1+ct ≤ budget ∧ TrackedHeadHole C ∧ TypedSource Ξ source ∧
    ScopedComputeCount (PiInertStage D n) cp Ξ source (C.plug (ProofShape.mkApps (.const ``Eq.rec ls) args)) ∧
    TypedSource Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertStage D n Θ (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∧
    ¬ WrappedConstHead ``Eq.rec target ∧
    (∀ k, ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) ∧
    args.length ≤ 5 ∧
    (ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target ∨
      ∃ k, k < n ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) target) ∧
    ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint ∧
    ¬ IteratedAmbientEqCompletion Δ v w original Θ (ProofShape.mkApps (.const ``Eq.rec ls) args)

/-- Forgetting the added exclusion recovers the prior singleton failure,
since every single-block completion embeds into iterated completion. -/
theorem IteratedAmbientSingletonFailure.forget
    (H : IteratedAmbientSingletonFailure D Δ v w original budget) :
    SingletonEqHeadCompletionFailure D Δ v w original budget := by
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, hlen, HG, RT, HP⟩ := H
  exact ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, hlen, HG, RT, fun H => HP (.base H)⟩

/-- The same selected singleton either reads the target through an iterated
ambient completion or lacks every such completion. No new root is selected. -/
theorem SingletonEqHeadCompletionFailure.eq_or_iterated_ambient_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : SingletonEqHeadCompletionFailure D Δ v w [α,a,M,minor,b] budget) :
    env.IsDefEq univs Δ a b α ∨ IteratedAmbientSingletonFailure D Δ v w [α,a,M,minor,b] budget := by
  classical
  obtain ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
    hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, hlen, HG, RT, _⟩ := H
  by_cases HP : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) args)
  · exact .inl (HP.read_loss heq hs hreg hoff hD hΔ ht HR HN)
  · exact .inr ⟨Ξ, Θ, n, source, endpoint, ls, args, target, cp, ct, C,
      hc, Htrack, HT, RP, HTroot, HR, HN, Hstruct, hlen, HG, RT, HP⟩

end Lean4Lean.VEnv.Strengthening
