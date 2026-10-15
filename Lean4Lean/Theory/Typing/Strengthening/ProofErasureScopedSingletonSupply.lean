import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSingletonSubstitution
import Lean4Lean.Theory.Typing.Strengthening.PrefixSpineSupply

/-! # Exact erased overlap between shorter and longer singleton prefixes

Both prefix contractions are supplied, with possibly different guard relations.
Replay at the same original source identifies their actual generated programs.
Checked spine supply then gives a directed beta path from the shorter output
applied to its remaining arguments to the longer output. No new guard, zero-prefix
typing, or confluence assumption is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- At a specified typed constant spine, primitive replay retains its exact
original head, universe list and supplied arguments. The witness is an actual
prefix rule, rather than an arbitrary compatible prefix-computation path. -/
theorem proofErase_scoped_singleton_replay_spine
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T)
    (R : ProofShape.ScopedSingletonPrefixPrimitive Step (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const name levels) args)) out) :
    ∃ original, PrefixUnfold env univs recursorData Γ name levels args original ∧
      proofErase Γ original = out := by
  generalize hsrc : proofErase Γ (mkApps (.const name levels) args) = source at R
  cases R with
  | @intro C rawArgs domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ (mkApps (.const name levels) args) := by
      intro hp
      exact const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, E, Hargs⟩ := proofErase_const_spine_inv hsrc
    obtain ⟨rfl, rfl, rfl⟩ := VExpr.mkApps_const_inj E
    rw [Hargs] at ha hcalc HG ⊢
    simp only [List.length_map] at ha
    exact V.replay heq hstep hΓ ha ⟨_, ht⟩ hn hcalc HG

/-- Two certified prefixes on the same typed spine have a directed beta
overlap: apply the shorter output to the trailing arguments, then beta-reduce
to the longer output. The two recursive guard relations may differ; no guard
transport or confluence is assumed. Indexed and dependent layouts are allowed. -/
theorem proofErase_scoped_singleton_supply_peak
    (heq : env.HasCanonicalEq)
    (hstep₁ : ErasedScopedPrimitiveDescent Step₁)
    (hstep₂ : ErasedScopedPrimitiveDescent Step₂)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const name levels) (args ++ tail)) T)
    (Rshort : ProofShape.ScopedSingletonPrefixPrimitive Step₁ (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const name levels) args)) short)
    (Rlong : ProofShape.ScopedSingletonPrefixPrimitive Step₂ (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const name levels) (args ++ tail))) long) :
    ProofShape.BetaRed (ProofShape.mkApps short (tail.map (proofErase Γ))) long := by
  have ht' : env.HasType univs Γ (mkApps (mkApps (.const name levels) args) tail) T := by
    simpa only [mkApps_append] using ht
  obtain ⟨S, hshort⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, ht'⟩
  obtain ⟨early, HE, Ee⟩ := proofErase_scoped_singleton_replay_spine heq hstep₁ hΓ hshort Rshort
  obtain ⟨late, HL, El⟩ := proofErase_scoped_singleton_replay_spine heq hstep₂ hΓ ht Rlong
  obtain ⟨data, hreg, hbound⟩ : ∃ data, recursorData name = some data ∧
      args.length + tail.length ≤ data.majorOffset := by
    cases HL with
    | intro hreg _ _ _ _ _ hg _ =>
      exact ⟨_, hreg, by simpa only [List.length_append] using (RecursorData.singletonUnfolding_spec hg).1⟩
  obtain ⟨late', HL', HB⟩ := prefixUnfold_supply_spine henv hΓ hreg hbound HE ⟨_, ht⟩
  have Eout := HL'.unique HL
  rw [Eout] at HB
  have HH := (IsDefEqU.mkApps_congr_left henv hΓ (HE.defeq henv hΓ) ⟨_, ht'⟩).of_l henv hΓ ht'
  have hn : ¬ IsProof Γ (mkApps (.const name levels) (args ++ tail)) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Rlong
    generalize E : ProofShape.proof = source at Rlong
    cases Rlong with
    | intro => exact const_spine_ne_proof E.symm
  have hn' : ¬ IsProof Γ (mkApps early tail) := by
    intro hp
    apply hn
    simpa only [mkApps_append] using (isProof_congr hΓ HH).2 hp
  have HR := proofErase_beta_forward hΓ HH.hasType.2 HB
  rwa [proofErase_mkApps hΓ HH.hasType.2 hn', Ee, El] at HR

private theorem nonproof_spine_head (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps f args) T) (hn : ¬ IsProof Γ (mkApps f args)) :
    ¬ IsProof Γ f := by
  induction args using List.snoc_induction generalizing T with
  | nil => exact hn
  | snoc args a ih =>
    rw [mkApps_snoc] at ht hn
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact ih hf (not_isProof_fn hΓ hf ha hn)

/-- The general typed raw primitives themselves have the directed supply
overlap, without externally chosen original representatives. Realizability of
the longer source recovers a shared original spine and its shorter prefix. -/
theorem ProofShape.ScopedTypedSingletonPrimitive.supply_peak
    (heq : env.HasCanonicalEq)
    (hstep₁ : ErasedScopedPrimitiveDescent Step₁)
    (hstep₂ : ErasedScopedPrimitiveDescent Step₂)
    (Rshort : ProofShape.ScopedTypedSingletonPrimitive Step₁ Δ
      (ProofShape.mkApps (.const name levels) args) short)
    (Rlong : ProofShape.ScopedTypedSingletonPrimitive Step₂ Δ
      (ProofShape.mkApps (.const name levels) (args ++ tail)) long) :
    ProofShape.BetaRed (ProofShape.mkApps short tail) long := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := Rlong.1
  obtain ⟨original, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  have Efirst : (original.take args.length).map (proofErase Γ) = args := by
    rw [List.map_take, ← Eargs, List.take_left]
  have Elast : (original.drop args.length).map (proofErase Γ) = tail := by
    rw [List.map_drop, ← Eargs, List.drop_left]
  have Ewhole : original.take args.length ++ original.drop args.length = original :=
    List.take_append_drop _ _
  have ht' : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const name levels) (original.take args.length))
        (original.drop args.length)) T := by
    simpa only [← VExpr.mkApps_append, Ewhole] using ht
  have hn : ¬ IsProof Γ (VExpr.mkApps (.const name levels) original) := by
    intro hp
    exact const_spine_ne_proof (Ee.symm.trans (proofErase_eq_proof.2 hp))
  have hn' := nonproof_spine_head hΓ ht'
    (by simpa only [← VExpr.mkApps_append, Ewhole] using hn)
  obtain ⟨_, hshort⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, ht'⟩
  have Eshort := proofErase_const_spine hΓ hshort hn'
  rw [Efirst] at Eshort
  have H := proofErase_scoped_singleton_supply_peak heq hstep₁ hstep₂ hΓ
    (args := original.take args.length) (tail := original.drop args.length)
    (Ewhole.symm ▸ ht) (Eshort.symm ▸ Rshort.2)
    (by simpa only [Ewhole, Ee] using Rlong.2)
  simpa only [Elast] using H

end Lean4Lean.VEnv.Strengthening
