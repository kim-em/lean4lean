import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerDomainGuards
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperNativeOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInstantiationBoundary

/-! # Domain guards survive a failure of exact caller-type recovery

A constant caller needs only some native type for its returned value to recover
its written input domain. Its assigned codomain can remain unrecoverable. An
identity beta cover supplies the whole assigned Pi before contraction, giving
a strict separation between the two caller interfaces, even for an input which
is a nonempty literal Pi telescope. This is not a strengthening counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Some native type for the constant result suffices for the caller's written
domain guard. The selected result need not equal the ordinary assigned type.
The input domain has an ordinary inhabitant; it needs no native certificate. -/
theorem static_structure_constant_caller_domain_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (hx : env.HasType univs Γ x A)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) selected) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b.lift)) (.forallE (proofErase Γ A) (selected.liftN 1)) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb' := hb.weakN henv (Ctx.LiftN.one (A := A))
  have hf := HasType.lam hA hb'
  have HE : env.IsDefEq univs Γ (.app (.lam A b.lift) x) b B := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hb' hx
  have hn : ¬ IsProof Γ b := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have hnapp := mt (isProof_congr hΓ HE).1 hn
  have hnf := not_isProof_fn hΓ hf hx hnapp
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RL := RN.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN, proofEraseCtx] at RL
  rw [show proofErase Γ (.lam A b.lift) = .lam _ _ from if_neg hnf,
    proofErase_liftN hΓ hΓA Ctx.LiftN.one hb]
  exact .lam RL

/-- In contrast, recovering the whole assigned Pi of a retained constant
caller would recover its result at the assigned type. Applying any ordinary
inhabitant and descending the unused body binder proves this reflection. -/
theorem static_structure_constant_caller_exact_reflects
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b B)
    (hx : env.HasType univs Γ x A) (hn : ¬ IsProof Γ b)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b.lift)) (proofErase Γ (.forallE A B.lift))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) (proofErase Γ B) := by
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hb' := hb.weakN henv (Ctx.LiftN.one (A := A))
  have hf := HasType.lam hA hb'
  have HE : env.IsDefEq univs Γ (.app (.lam A b.lift) x) b B := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta hb' hx
  have hnapp := mt (isProof_congr hΓ HE).1 hn
  have RA := static_structure_exact_native_app hΓ hf hx (fun _ => RN) hnapp
  simp only [VExpr.inst_lift] at RA
  exact static_structure_constant_beta_native_recovery heq hs hΓ hb hx RA

/-- One identity beta contraction loses the complete assigned Pi, while a
native Pi with exactly the same argument domain survives. The domain is the
nonempty literal telescope `Sort 1 -> Sort 1`, with an explicit ordinary lambda
inhabitant. Thus domain-guarded caller transformations cover strictly more than
the earlier exact-assigned-Pi interface. A positive empty structure supplies
the usual exact-recovery obstruction; neither common coverage nor strengthening
is refuted. -/
theorem static_structure_caller_beta_preserves_domain_not_assigned_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    let Q := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
    ∃ Γ f g, ∃ B : VExpr, ∃ selected, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.lam (.sort (.succ .zero)) (.bvar 0)) Q ∧
      env.HasType univs Γ f (.forallE Q B.lift) ∧
      env.HasType univs Γ g (.forallE Q B.lift) ∧
      VExpr.BetaRed f g ∧
      BetaRed (proofErase Γ f) (proofErase Γ g) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.forallE Q B.lift)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ g) (.forallE (proofErase Γ Q) selected) ∧
      ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ g) (proofErase Γ (.forallE Q B.lift)) := by
  dsimp only
  obtain ⟨Γ, b, B, hΓ, hb, hn, Hno, Hcommon⟩ := descending_native_exact_coverage_failure
    (erased_static_structure_eta_expansion_union_descent heq hs) hi hp hix hz hS
  obtain ⟨selected, RN, _⟩ := Hcommon D
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) selected :=
    RN.mono (fun H => ⟨1, erased_unit_into_static_structure_eta_stage 1 H⟩)
  let Q := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  have hsrt : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
    .forallE hsrt (.sort (by trivial))
  have hx : env.HasType univs Γ (.lam (.sort (.succ .zero)) (.bvar 0)) Q :=
    .lam hsrt (.bvar .zero)
  let g := VExpr.lam Q b.lift
  have hg : env.HasType univs Γ g (.forallE Q B.lift) :=
    .lam hQ (hb.weakN henv Ctx.LiftN.one)
  have RNg := static_structure_constant_caller_domain_guard heq hs hΓ hb hx RN
  have hng : ¬ IsProof Γ g := fun hp => RNg.ne_proof (proofErase_eq_proof.2 hp)
  let f := VExpr.app (.lam (.forallE Q B.lift) (.bvar 0)) g
  have hf := (nativeIdentityExpansion_equal hg).hasType.1
  have RB : VExpr.BetaRed f g := by
    simpa only [VExpr.inst, VExpr.instVar_zero] using
      (VExpr.BetaRed.beta (A := .forallE Q B.lift) (b := .bvar 0) (a := g))
  refine ⟨Γ, f, g, B, selected.liftN 1, hΓ, hx, hf, hg, RB,
    proofErase_beta_forward hΓ hf RB, proofErase_identity_wrapper_native hΓ hg hng, RNg, ?_⟩
  intro H
  exact Hno (static_structure_constant_caller_exact_reflects heq hs hΓ hb hx hn H)

/-- Domain-only guards are still not universally preserved by caller beta
reduction. The target is an ordinarily typed family ending in Sort 1, and its
input is a nonempty literal Pi telescope. It cannot recover any Pi with that
domain, regardless of codomain or descending primitive language. The identity
cover has the complete assigned Pi at stage zero before its one contraction.
This excludes replacing full guard transfer by universal domain-only transfer;
common or changed-domain pivots remain possible and are not refuted. -/
theorem static_structure_type_caller_beta_loses_domain_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hix : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ f g A, OnCtx Γ (env.IsType univs) ∧
      let Q := VExpr.forallE A (.sort (.succ .zero))
      env.HasType univs Γ f (.forallE Q (.sort (.succ .zero))) ∧
      env.HasType univs Γ g (.forallE Q (.sort (.succ .zero))) ∧
      VExpr.BetaRed f g ∧ BetaRed (proofErase Γ f) (proofErase Γ g) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ (.forallE Q (.sort (.succ .zero)))) ∧
      ∀ Step, ErasedScopedPrimitiveDescent Step → ∀ selected,
        ¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ g)
          (.forallE (proofErase Γ Q) selected) := by
  obtain ⟨Γ, Q, g, _, _, _, hΓ, _, hg, ⟨A, rfl⟩, _, Hno, _⟩ :=
    static_structure_generic_family_domain_instantiation_beta_residual_failure heq hs hi hp hix hz hS
  let Q := VExpr.forallE A (.sort (.succ .zero))
  let F := VExpr.forallE Q (.sort (.succ .zero))
  let f := VExpr.app (.lam F (.bvar 0)) g
  have hng := not_isProof_function_to_sort hΓ hg
  have hf := (nativeIdentityExpansion_equal hg).hasType.1
  have RB : VExpr.BetaRed f g := by
    simpa only [VExpr.inst, VExpr.instVar_zero] using
      (VExpr.BetaRed.beta (A := F) (b := .bvar 0) (a := g))
  exact ⟨Γ, f, g, A, hΓ, hf, hg, RB, proofErase_beta_forward hΓ hf RB,
    proofErase_identity_wrapper_native hΓ hg hng, Hno⟩

end Lean4Lean.VEnv.Strengthening
