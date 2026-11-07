import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertReplayFailure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureProjectionSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery
import Lean4Lean.Theory.Typing.Strengthening.OrdinaryIotaCoverage

/-! # Structure replay from the constructor image itself

A saturated constructor recovers its own family without certificates for its
fields. If its parameter header is the one selected by an original structure
expansion, ordinary interpreted substitution replays that root at stage one.
At a closed parameterless family the header condition is automatic.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private rigid_spine_eq_closed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params] {D : Definitions}

/-- A typed saturated raw constructor recovers its literal family and retained
parameters in any recovery language. Its fields need no native certificates. -/
theorem TypedSource.structure_constructor_native
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName ls) args))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hlen : args.length = info.nparams + info.numFields) :
    ScopedTypeRecovery Step Δ (ProofShape.mkApps (.const info.ctorName ls) args)
      (ProofShape.mkApps (.const family ls) (args.take info.nparams)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  have hn : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName ls) actual) := by
    intro H
    have E := congrArg ProofShape.constHead ((proofErase_eq_proof.2 H).symm.trans Ee)
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  have hlen' : actual.length = info.nparams + info.numFields := by
    rw [Eargs, List.length_map] at hlen
    exact hlen
  have RN := proofErase_structure_constructor_native (Step := Step) hΓ hi hx hlen' ht hn
  rw [Ee, EΓ] at RN
  simpa only [Eargs, ← List.map_take] using RN

/-- A constructor image with the selected parameter header supplies its own
stage-zero guard. Thus the original expansion replays in one primitive at
stage one, irrespective of the original guard stage and field image recovery.
The header equation is directed syntactic evidence, not inferred from equality
of parameterized family assignments. -/
theorem pi_inert_structure_constructor_image_replay
    (hi : env.projections family info) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hp : ps.length = info.nparams)
    (HT : TypedSource Δ source) (W : ContextSubstitution Δ Θ τ)
    (E : source.subst τ = ProofShape.mkApps (.const info.ctorName ls) args)
    (hlen : args.length = info.nparams + info.numFields)
    (EP : args.take info.nparams = ps.map (fun p => p.subst τ)) :
    ScopedComputeCount (PiInertStage D 1) 1 Θ (source.subst τ)
      ((nativeStructureOutput family info ls ps source).subst τ) := by
  have RN := TypedSource.structure_constructor_native
    (Step := ErasedStaticStructureEtaExpansionStage D 0) (E ▸ HT.subst W) hi hx hlen
  rw [EP, ← E] at RN
  rw [nativeStructureOutput_subst]
  refine .base ⟨.inr (.inr (.inr (.inr (.inr
    (.intro hi hx ha (by simpa only [List.length_map] using hp) RN))))), .inl ?_⟩
  rw [E]
  clear E hlen EP RN
  induction args using List.snoc_induction with
  | nil => trivial
  | snoc args a ih => simpa only [ProofShape.mkApps_snoc, PrimitiveHead] using ih

/-- A constructor at a closed parameterless family is saturated and has the
empty universe instance. These are consequences of actual typing, even if
only its raw constructor head and arbitrary argument vector were supplied. -/
theorem proofErase_closed_constructor_shape
    (hi : env.projections family info) (hp : info.nparams = 0) (hx : info.nindices = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (E : proofErase Γ m = ProofShape.mkApps (.const info.ctorName levels) fields) :
    levels = [] ∧ fields.length = info.numFields := by
  obtain ⟨actual, rfl, Efields⟩ := proofErase_const_spine_inv E
  have hlen := (projection_major_family (ls := []) (ps := []) henv hΓ hi (henv.projectionRigid hi) hm).2
  have hfam := structure_constructor_family hΓ hi hx hlen hm
  obtain ⟨_, hF⟩ := hfam.isType henv hΓ
  obtain ⟨_, HL, _⟩ := henv.headInversion.rigid_rigid (args' := []) hΓ
    (henv.projectionRigid hi) (henv.projectionRigid hi)
    ((hfam.uniqU henv hΓ hm).typeChain henv hΓ hF)
  cases HL
  exact ⟨rfl, by simpa only [Efields, List.length_map, hp, Nat.zero_add] using hlen⟩

/-- Semantic typing at a closed rigid family fixes every structure guard's
family, universe instance and empty parameter vector. Any image headed by its
constructor then replays the root without any native-image substitution law.
Saturation and the universe instance follow from typing; the image fields
need no native recovery. -/
theorem pi_inert_closed_structure_constructor_image_replay
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ)
    (E : (proofErase Γ m).subst τ = ProofShape.mkApps (.const info.ctorName levels) fields) :
    ScopedComputeCount (PiInertStage D 1) 1 Θ ((proofErase Γ m).subst τ) (target.subst τ) := by
  cases H with
  | intro hi' hx ha hps RN =>
    obtain ⟨A, hmA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hm RN
    obtain ⟨v, hA⟩ := hmA.isType henv hΓ
    have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi) (henv.projectionRigid hi')
      hA (hmA.uniqU henv hΓ hm) EA
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj (ps' := []) EC
    cases henv.ordered.projections_unique hi hi'
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ rfl
    have hm' := hm.subst henv.orderedStrong HS hΓ₀
    have Em : proofErase Γ₀ (m.subst σ) = ProofShape.mkApps (.const info.ctorName levels) fields :=
      (proofErase_subst_with hΓ₀ HS hm ES).trans E
    obtain ⟨rfl, hlen⟩ := proofErase_closed_constructor_shape hi hp hx hΓ₀ hm' Em
    exact pi_inert_structure_constructor_image_replay hi hx ha hps
      ⟨Γ, m, _, hΓ, rfl, hm, rfl⟩ W E (by omega) (by simp [hp])

/-- Any registered constructor head in the image suffices. Actual typing
identifies its family with the selected closed family, so no separate equality
of constructor names, universe instances or argument lengths is needed. -/
theorem pi_inert_closed_structure_registered_image_replay
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hc : env.projections other otherInfo)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ)
    (E : (proofErase Γ m).subst τ = ProofShape.mkApps (.const otherInfo.ctorName levels) fields) :
    ScopedComputeCount (PiInertStage D 1) 1 Θ ((proofErase Γ m).subst τ) (target.subst τ) := by
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ rfl
  have hm' : env.HasType univs Γ₀ (m.subst σ) (.const family []) :=
    hm.subst henv.orderedStrong HS hΓ₀
  have Em : proofErase Γ₀ (m.subst σ) = ProofShape.mkApps (.const otherInfo.ctorName levels) fields :=
    (proofErase_subst_with hΓ₀ HS hm ES).trans E
  obtain ⟨actual, EE, _⟩ := proofErase_const_spine_inv Em
  rw [EE] at hm'
  obtain ⟨rfl, _⟩ := projection_major_family (ls := []) (ps := []) henv hΓ₀ hc
    (henv.projectionRigid hi) hm'
  cases henv.ordered.projections_unique hi hc
  exact pi_inert_closed_structure_constructor_image_replay hstep hi hp hΓ hm H W E

/-- A structure expansion rooted at a registered constructor of a closed
family always substitutes with cost one. Substitution preserves its constructor
head; typing supplies saturation and identifies the selected family. This
handles arbitrary field substitutions and arbitrary original guard stages. -/
theorem pi_inert_closed_structure_constructor_substitution
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hc : env.projections other otherInfo)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (E : proofErase Γ m = ProofShape.mkApps (.const otherInfo.ctorName levels) fields)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ) :
    ScopedComputeCount (PiInertStage D 1) 1 Θ ((proofErase Γ m).subst τ) (target.subst τ) := by
  apply pi_inert_closed_structure_registered_image_replay hstep hi hp hc hΓ hm H W
    (fields := fields.map (fun a => a.subst τ)) (levels := levels)
  rw [E, ProofShape.subst_mkApps]
  rfl

/-- A closed-family structure failure has no registered constructor head in
its image, regardless of the proposed family, universe instance or arguments.
This rules out that concrete root case, not all compatible failures or all
neutral structure majors. -/
theorem pi_inert_closed_structure_replay_failure_not_constructor
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (W : ContextSubstitution (proofEraseCtx Γ) Θ τ)
    (HF : ∀ later j, j ≤ 1 → ¬ ScopedComputeCount (PiInertStage D later) j Θ
      ((proofErase Γ m).subst τ) (target.subst τ)) :
    ∀ other otherInfo, env.projections other otherInfo → ∀ levels fields,
      (proofErase Γ m).subst τ ≠ ProofShape.mkApps (.const otherInfo.ctorName levels) fields := by
  intro other otherInfo hc levels fields E
  exact HF 1 1 (by omega)
    (pi_inert_closed_structure_registered_image_replay hstep hi hp hc hΓ hm H W E)

end Lean4Lean.VEnv.Strengthening
