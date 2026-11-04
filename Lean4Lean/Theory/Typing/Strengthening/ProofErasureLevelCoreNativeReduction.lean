import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativePullback
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction

/-! # Removing mixed expansion from native recovery through the level core

Every conversion with a level-core common reduct can be replaced by native
level-core recovery whose output is an ordinary reduct of the old output.
Postponed universe conversions are reversed at typed intermediate endpoints.
This preserves the original sort syntax and projection universe instances in
all recovery constructors, without requiring those instances to stay fixed
along general level-core paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params]
namespace LevelCoreNative

private theorem forall_parts
    (R : Compute (ErasedIotaPrimitive D) (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ Compute (ErasedIotaPrimitive D) A A' ∧ Compute (ErasedIotaPrimitive D) B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (E ▸ erased_iota_primitive_head H).elim
  | beta H =>
    cases E
    obtain ⟨A', B', HE, HA, HB⟩ := beta_forallE_parts H
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA, HB⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA', HB'⟩ := ih₂ rfl
    exact ⟨_, _, HE, HA.trans HA', HB.trans HB'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA, HB⟩
  | app | proj | lam => cases E

private theorem instOuter_compute
    (H : List.Forall₂ (Compute (ErasedIotaPrimitive D)) args args') (body : ProofShape) :
    Compute (ErasedIotaPrimitive D) (body.instOuter args) (body.instOuter args') := by
  apply Compute.subst_images (fun H => erased_iota_primitive_liftN H)
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < args.length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

private theorem projection_compute
    (H : List.Forall₂ (Compute (ErasedIotaPrimitive D)) args args') :
    Compute (ErasedIotaPrimitive D) (projectionType s info doms j hj args m)
      (projectionType s info doms j hj args' m) := by
  apply instOuter_compute
  exact (Lean4Lean.List.forall₂_take H info.nparams).append'
    (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))

/-- All native recovery constructors transfer when source conversions have
level-core common reducts. The expression is unchanged; its old selected output
computes by ordinary rules to the new native output. No native coverage or
normalization assumption is used. -/
theorem recovery_of_compute_join (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ source out' ∧ Compute (ErasedIotaPrimitive D) out out' := by
  induction R generalizing Γ e T with
  | bvar => exact ⟨_, .bvar, .refl⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) EB
    exact ⟨_, .lam HR, .forallE .refl RC⟩
  | app R ih =>
    obtain ⟨f, x, rfl, _, EF, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih hΓ hf EΓ EF
    obtain ⟨A', B', rfl, _, RB⟩ := forall_parts RC
    refine ⟨_, .app HR, ?_⟩
    simpa only [ProofShape.inst_eq_subst] using RB.subst (fun H => erased_iota_primitive_subst H)
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, CA⟩ := ihA hΓ hA EΓ EA
    have EoutA := (CA.scoped (Δ := Δ) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outA
    obtain ⟨outB, HB, CB⟩ := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB
    have EoutB := (CB.scoped (Δ := Δ) (fun H => .base H)).sort_fixed
      (fun H => erased_iota_primitive_head H)
    subst outB
    exact ⟨_, .forallE HA HB, .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, RC⟩ := ih hΓ hm.hasType.2 EΓ EM
    have RC' := RC.scoped (Δ := Δ) (Step' := fun _ => ErasedIotaPrimitive D) (fun H => .base H)
    obtain ⟨args', rfl, Hargs⟩ := RC'.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (hD (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    refine ⟨_, .proj hi HT hj (Hargs.length_eq.symm.trans hlen) HR, ?_⟩
    exact projection_compute (Hargs.imp (fun _ _ H => H.core_forget))
  | convert R RC ih =>
    obtain ⟨out', HR, HC⟩ := ih hΓ ht EΓ Ee
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := heA.isType henv hΓ
    have RC' := RC
    rw [← EΓ, ← EA] at RC'
    obtain ⟨shared, Hold, Hout⟩ := hjoin hΓ hA RC'
    obtain ⟨final, Hnative, Hshared⟩ := proofErase_level_core_confluent hs hlevels hcon hc hΓ hA
      (EA ▸ HC.mono (fun H => Or.inl H)) Hold
    obtain ⟨Aout, HAout, EAout⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RC
    obtain ⟨native, RN, Rcore⟩ := pullback hs hlevels hcon hΓ HAout.hasType.2
      (HR.convert (Hnative.scoped (fun H => .base H))) (EAout ▸ Hout.trans Hshared)
    exact ⟨native, RN, by simpa only [EAout] using Rcore⟩

/-- Native recovery with arbitrary mixed ordinary, universe, and controlled
expansion paths collapses to level-core recovery with an ordinary output residual.
The recovery guards themselves may use any descending relation. -/
theorem expansion_recovery
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLevelCoreExpansion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) out' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) out out' :=
  recovery_of_compute_join hs hlevels hcon hD hc (erased_level_core_expansion_descent hs hr)
    (fun hΓ ht R => proofErase_level_core_expansion_join hs hlevels hcon hc hr hΓ ht R) R hΓ ht rfl rfl

/-- A mixed native output joined to the assigned type supplies a level-core
native ordinary reduct of that assigned type. Both original join branches may
compute, and no exact assigned-type native recovery is required. -/
theorem expansion_recovery_align
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedLevelCoreExpansion D Recovery)
      (proofEraseCtx Γ) (proofErase Γ e) out)
    (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ T) out) :
    ∃ native, ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) native ∧
      ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ T) native := by
  obtain ⟨core, RN, RC⟩ := expansion_recovery hs hlevels hcon hD hc hr hΓ ht R
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_level_core_expansion_descent hs hr) hΓ ht R
  obtain ⟨_, hA⟩ := heA.isType henv hΓ
  have K : ComputeJoin (ErasedLevelCore D) out core :=
    .of_compute (RC.mono (fun H => Or.inl H))
  rw [← EA] at HJ K
  have J := HJ.trans_typed (proofErase_level_core_confluent hs hlevels hcon hc) hΓ hA
    (by simpa only [EA] using K)
  obtain ⟨_, hT⟩ := ht.isType henv hΓ
  exact of_join hs hlevels hcon hΓ hT RN (by simpa only [EA] using J)

end LevelCoreNative
end Lean4Lean.VEnv.Strengthening
