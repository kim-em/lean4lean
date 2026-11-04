import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaSquares
import Lean4Lean.Theory.Typing.Strengthening.StructureProofFieldUniverses

/-! # Structure expansion joins across selected universe instances

Equivalent universe instances have identical static field masks. Expansions
therefore compute to a shared constructor whenever their parameter spines and
majors have explicit common reducts. No recovery is required at that reduct.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Equivalent well-formed universe instances select exactly the same raw
field mask, even for dependent proof fields. -/
theorem ProofShape.nativeStructureField_levels
    (hi : env.projections s info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls') :
    nativeStructureField s info ls m j = nativeStructureField s info ls' m j := by
  classical
  unfold nativeStructureField
  rw [StructureReplay.proofField_congr_levels_iff hi hw hw' hl he]

/-- Simultaneous parameter and major computation commutes with universe
conversion of the constructor head. Every field uses the same closed mask. -/
theorem ProofShape.nativeStructureOutput_levels_compute
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (hi : env.projections s info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (HP : List.Forall₂ (ScopedCompute Step Δ) ps qs) (HM : ScopedCompute Step Δ a b) :
    ScopedCompute Step Δ (nativeStructureOutput s info ls ps a)
      (nativeStructureOutput s info ls' qs b) := by
  unfold nativeStructureOutput
  apply ScopedCompute.mkApps (hlevel (.const he hw'))
  apply List.Forall₂.append HP
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply Lean4Lean.List.Forall₂.rfl
  intro j _
  rw [nativeStructureField_levels hi hw hw' hl he]
  exact nativeStructureField_compute HM

/-- Two selected expansions join at explicit common parameter and major
reducts. Their selected universes may differ syntactically. The shared raw
constructor needs no independent typing or native recovery certificate. -/
theorem ProofShape.nativeStructureOutput_levels_join
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (hi : env.projections s info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (HP : List.Forall₂ (ScopedCompute Step Δ) ps rs)
    (HQ : List.Forall₂ (ScopedCompute Step Δ) qs rs)
    (HA : ScopedCompute Step Δ a c) (HB : ScopedCompute Step Δ b c) :
    ScopedCompute Step Δ (nativeStructureOutput s info ls ps a)
        (nativeStructureOutput s info ls' rs c) ∧
      ScopedCompute Step Δ (nativeStructureOutput s info ls' qs b)
        (nativeStructureOutput s info ls' rs c) :=
  ⟨nativeStructureOutput_levels_compute hlevel hi hw hw' hl he HP HA,
    nativeStructureOutput_compute HQ HB⟩

/-- A same-source structure-eta peak with different native family instances
joins once their parameter computations meet and their universes are equivalent.
The guard depths are unbounded and no common-reduct recovery is assumed. -/
theorem static_structure_eta_selected_universe_join
    (hi : env.projections s info) (hx : info.nindices = 0)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (hA : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hB : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls')
    (hp : ps.length = info.nparams) (hq : qs.length = info.nparams)
    (RA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ a
      (ProofShape.mkApps (.const s ls) ps))
    (RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ a
      (ProofShape.mkApps (.const s ls') qs))
    (HP : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) ps rs)
    (HQ : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) qs rs) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a
        (nativeStructureOutput s info ls ps a) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a
        (nativeStructureOutput s info ls' qs a) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (nativeStructureOutput s info ls ps a) (nativeStructureOutput s info ls' rs a) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
        (nativeStructureOutput s info ls' qs a) (nativeStructureOutput s info ls' rs a) := by
  have hlevel : ∀ {Δ a b}, LevelPrimitive univs a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b := by
    intro Δ a b H
    exact .base ⟨0, .inl (.inr H)⟩
  exact ⟨.base (erased_static_structure_eta_expansion_union_structure (.intro hi hx hA hp RA)),
    .base (erased_static_structure_eta_expansion_union_structure (.intro hi hx hB hq RB)),
    nativeStructureOutput_levels_join hlevel hi hw hw' hl he HP HQ .refl .refl⟩

/-- Two native recoveries of the same typed source at a registered family
necessarily select equivalent well-formed universe instances. This uses actual
replay and family injectivity, with no computational confluence hypothesis. -/
theorem proofErase_native_structure_family_universes
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections s info)
    (RA : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const s ls) ps))
    (RB : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const s ls') qs)) :
    (∀ l ∈ ls, l.WF univs) ∧ (∀ l ∈ ls', l.WF univs) ∧
      ls.length = info.uvars ∧ List.Forall₂ (· ≈ ·) ls ls' := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hleft hΓ ht RA
  obtain ⟨B, heB, EB⟩ := proofErase_scoped_typeRecovery_replay hright hΓ ht RB
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EA
  obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EB
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  obtain ⟨_, hB⟩ := heB.isType henv hΓ
  obtain ⟨_, hheadA⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hA⟩
  obtain ⟨_, hheadB⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hB⟩
  obtain ⟨hw, hl⟩ := StructureReplay.family_instance_levels hi hΓ hheadA
  obtain ⟨hw', _⟩ := StructureReplay.family_instance_levels hi hΓ hheadB
  exact ⟨hw, hw', hl, ((heA.uniqU henv hΓ heB).structApp_inv henv hΓ hi hA).1⟩

/-- In the actual typed same-source structure-eta peak, universe alignment is
a theorem. Only an explicit common computation of the selected parameter
spines remains to join the two long forms; no purity or common native guard is
required. -/
theorem proofErase_static_structure_eta_selected_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections s info)
    (RA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const s ls) ps))
    (RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const s ls') qs))
    (HP : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)) ps rs)
    (HQ : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)) qs rs) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (nativeStructureOutput s info ls ps (proofErase Γ e))
        (nativeStructureOutput s info ls' rs (proofErase Γ e)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (nativeStructureOutput s info ls' qs (proofErase Γ e))
        (nativeStructureOutput s info ls' rs (proofErase Γ e)) := by
  obtain ⟨hw, hw', hl, he⟩ := proofErase_native_structure_family_universes
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht hi RA RB
  exact nativeStructureOutput_levels_join (fun H => .base ⟨0, .inl (.inr H)⟩)
    hi hw hw' hl he HP HQ .refl .refl

/-- A native registered family selected for a source already assigned a
nullary registered family has that same name and no parameters. This is actual
head injectivity; it does not postulate raw computation of family arguments. -/
theorem proofErase_native_nullary_structure_family
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ e (.const s ls))
    (hi : env.projections s info) (hi' : env.projections s' info')
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const s' ls') ps)) : s = s' ∧ ps = [] := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hm RN
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EA
  obtain ⟨_, hS⟩ := hm.isType henv hΓ
  have H := henv.headInversion.rigid_rigid (args := []) hΓ
    (henv.projectionRigid hi) (henv.projectionRigid hi')
    ((hm.uniqU henv hΓ heA).typeChain henv hΓ hS)
  have Hargs := H.2.2
  cases Hargs
  exact ⟨H.1, rfl⟩

/-- For a typed source at a nullary registered family, any two full native
structure expansions differ only by equivalent constructor universe instances.
They join already by directed level-core computation. There is no guard purity,
field-count, proof-field, shared-stage or target-recovery assumption. -/
theorem proofErase_nullary_native_structure_diamond
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hΓ : OnCtx Γ (env.IsType univs)) (hm : env.HasType univs Γ e (.const s ls))
    (hi : env.projections s info)
    (RA : NativeMaskedStructureExpansion Left (proofEraseCtx Γ) (proofErase Γ e) a)
    (RB : NativeMaskedStructureExpansion Right (proofEraseCtx Γ) (proofErase Γ e) b) :
    ScopedCompute (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) a b := by
  cases RA with
  | intro hiA hxA haA hpA RN =>
    cases RB with
    | intro hiB hxB haB hpB RN' =>
      obtain ⟨rfl, rfl⟩ := proofErase_native_nullary_structure_family hleft hΓ hm hi hiA RN
      obtain ⟨rfl, rfl⟩ := proofErase_native_nullary_structure_family hright hΓ hm hiA hiB RN'
      cases henv.ordered.projections_unique hiA hiB
      obtain ⟨hw, hw', hl, HE⟩ := proofErase_native_structure_family_universes
        hleft hright hΓ hm hiA RN RN'
      exact nativeStructureOutput_levels_compute (fun H => .base (.inr H))
        hiA hw hw' hl HE .nil .refl

/-- Proof-only supplied parameters erase to the same vector in every native
registered-family recovery of a typed source. Family injectivity gives actual
argument equalities; proof erasure turns these into literal raw agreement. -/
theorem proofErase_native_structure_proof_parameters
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ e (VExpr.mkApps (.const s ls) params))
    (hi : env.projections s info) (hi' : env.projections s' info')
    (hparams : ∀ p ∈ params, IsProof Γ p)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const s' ls') ps)) :
    s = s' ∧ ps = List.replicate params.length .proof := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hm RN
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EA
  obtain ⟨_, hS⟩ := hm.isType henv hΓ
  have H := henv.headInversion.rigid_rigid hΓ
    (henv.projectionRigid hi) (henv.projectionRigid hi')
    ((hm.uniqU henv hΓ heA).typeChain henv hΓ hS)
  refine ⟨H.1, ?_⟩
  have Hargs := H.2.2
  clear RN heA hm H hS EA
  induction Hargs with
  | nil => rfl
  | @cons p a params args E H ih =>
    obtain ⟨_, E⟩ := E
    have hproof := (isProof_congr hΓ E).1 (hparams p (by simp))
    simp only [List.map_cons, List.length_cons, List.replicate_succ, proofErase_eq_proof.2 hproof]
    exact congrArg (ProofShape.proof :: ·) (ih (fun p hp => hparams p (by simp [hp])))

/-- If a source's assigned structure parameters are all proofs, arbitrary
native structure expansions of that source join by level conversion alone.
There may be any number of dependent proof parameters and mixed proof/data
fields; neither selected parameter computation nor native field recovery is a
premise. The nullary-family case is included. -/
theorem proofErase_proof_parameter_native_structure_diamond
    (hleft : ErasedScopedPrimitiveDescent Left) (hright : ErasedScopedPrimitiveDescent Right)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ e (VExpr.mkApps (.const s ls) params))
    (hi : env.projections s info) (hparams : ∀ p ∈ params, IsProof Γ p)
    (RA : NativeMaskedStructureExpansion Left (proofEraseCtx Γ) (proofErase Γ e) a)
    (RB : NativeMaskedStructureExpansion Right (proofEraseCtx Γ) (proofErase Γ e) b) :
    ScopedCompute (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) a b := by
  cases RA with
  | intro hiA hxA haA hpA RN =>
    cases RB with
    | intro hiB hxB haB hpB RN' =>
      obtain ⟨rfl, rfl⟩ := proofErase_native_structure_proof_parameters hleft hΓ hm hi hiA hparams RN
      obtain ⟨rfl, rfl⟩ := proofErase_native_structure_proof_parameters hright hΓ hm hiA hiB hparams RN'
      cases henv.ordered.projections_unique hiA hiB
      obtain ⟨hw, hw', hl, HE⟩ := proofErase_native_structure_family_universes
        hleft hright hΓ hm hiA RN RN'
      exact nativeStructureOutput_levels_compute (fun H => .base (.inr H))
        hiA hw hw' hl HE (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) .refl

end Lean4Lean.VEnv.Strengthening
