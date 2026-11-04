import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelStages

/-! # Singleton-prefix guards through structural context changes

The generated residual telescope is held fixed as actual syntax. Context
conversion extends beneath it, its erased entries remain structural variants,
and the actual family propositions retain their typing. This transports the
stored guard certificate and preserves the prefix's exact erased output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation InductiveSignature PropElim
open private ProofShape.const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- Actual context conversion extends beneath any fixed well-formed prefix. -/
theorem carrier_aligned_context_prefix
    (W : IsDefEqCtx env univs [] Γ Γ') (hctx : OnCtx (ds ++ Γ) (env.IsType univs)) :
    IsDefEqCtx env univs [] (ds ++ Γ) (ds ++ Γ') := by
  induction ds with
  | nil => exact W
  | cons A ds ih => exact .succ (ih hctx.1) hctx.2.choose_spec

/-- Prefix annotations are the same actual expressions and hence have equal
erasures under context conversion. Structural variation is confined to the tail. -/
theorem carrier_aligned_context_prefix_variant
    (W : IsDefEqCtx env univs [] Γ Γ') (hctx : OnCtx (ds ++ Γ) (env.IsType univs))
    (HΓ : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ')) :
    List.Forall₂ StructuralVariant (proofEraseCtx (ds ++ Γ)) (proofEraseCtx (ds ++ Γ')) := by
  induction ds with
  | nil => exact HΓ
  | cons A ds ih =>
    have W' := carrier_aligned_context_prefix W hctx.1
    have E := proofErase_defeqCtx hctx.1 W' hctx.2.choose_spec
    exact .cons (E ▸ StructuralVariant.refl) (ih hctx.1)

/-- The family comparator transports actual proposition typings and their
certificates through structural context conversion. This is a certificate law,
not just semantic soundness. The level-extended recovered base proves it below. -/
def ErasedFamilyStructuralContext
    (Cmp : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' P Q}, OnCtx Γ (env.IsType univs) → IsDefEqCtx env univs [] Γ Γ' →
    List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ') →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    Cmp (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q) →
    Cmp (proofEraseCtx Γ') (proofErase Γ' P) (proofErase Γ' Q)

/-- Full recovered comparison transport supplies the required family certificate law. -/
theorem erased_recovered_family_structural_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b) :
    ErasedFamilyStructuralContext (fun Δ => CarrierRecoveredCompare Step Δ true) := by
  intro Γ Γ' P Q hΓ W HO hP hQ H
  have H' := H.structural_context hstep hctx hsim hlevel hΓ hP hQ rfl rfl rfl W HO
  rwa [proofErase_defeqCtx hΓ W hP, proofErase_defeqCtx hΓ W hQ] at H'

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}
/-- A generated singleton's actual family guard transports under the entire
residual binder telescope. Actual family typings are reconstructed from the
registered code and source typing, before certificate transport is invoked. -/
theorem Valid.family_guard_structural_context
    (V : C.Valid) (heq : env.HasCanonicalEq) (hcontext : ErasedFamilyStructuralContext Cmp)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard (ErasedFamilyComparison Cmp)
      Γ' C.data C.levels args program C.layout C.elim := by
  obtain ⟨_, _, hl, hll, he, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq he
  obtain ⟨S, E, hS, hE, WF⟩ := RecursorData.propElim_wf henv V.registered V.large V.zero
    V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args
    henv hΓ V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht WF
  have htf := (transportedFamily_typings henv heq WF hctx hps hargs).1
  have hpf := WF.family_prop henv hps hargs
  exact hcontext hctx (carrier_aligned_context_prefix W hctx)
    (carrier_aligned_context_prefix_variant W hctx HO) htf hpf HG
end SingletonPrefixCode

/-- A general raw singleton step retains the same exact output under structural
context conversion. The target guard certificate is transported and checked;
output equality follows from actual generated-RHS typing and context conversion. -/
theorem proofErase_singleton_structural_context
    (heq : env.HasCanonicalEq) (hcmp : ErasedFamilyDescent Cmp)
    (hcontext : ErasedFamilyStructuralContext Cmp)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ht : env.HasType univs Γ e T)
    (R : SingletonPrimitiveWith Cmp (proofEraseCtx Γ) (proofErase Γ e) out) :
    SingletonPrimitiveWith Cmp (proofEraseCtx Γ') (proofErase Γ' e) out := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact ProofShape.const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ⟨_, ht⟩ hcalc HG
    have HC := V.checkWith heq hcmp hΓ hg ⟨_, ht⟩ HG
    have hΓ' := (W.symm henv.ordered).isType
    have ht' := ht.defeqDFC henv W
    have HG' := V.family_guard_structural_context heq hcontext hΓ W HO hg ⟨_, ht⟩ HG
    have HC' := V.checkWith heq hcmp hΓ' hg ⟨_, ht'⟩ HG'
    have hn' := mt (isProof_defeqCtx W).2 hn
    have HE := V.output_eq heq hΓ hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ' hg HC' hn'
    rw [← HE, proofErase_defeqCtx hΓ W (HC.defeq henv hΓ).hasType.2, HE',
      proofErase_const_spine hΓ' ht' hn']
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ' hg ⟨_, ht'⟩)
      ((V.guardWith_iff heq hΓ' hg ⟨_, ht'⟩).2 HG')

/-- Recovered-family singleton steps retain both their source realization and
exact raw output through a structurally varied actual context. -/
theorem proofErase_recovered_singleton_structural_context
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hctx : StructuralVariantComputeContext Step) (hsim : StructuralVariantCompute Step)
    (hlevel : ∀ {Δ a b}, LevelPrimitive univs a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ht : env.HasType univs Γ e T)
    (R : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ') (proofErase Γ' e) out :=
  ⟨⟨Γ', e, T, (W.symm henv.ordered).isType, rfl, ht.defeqDFC henv W, rfl⟩,
    proofErase_singleton_structural_context heq (erased_carrier_recovered_family_descent hstep)
      (erased_recovered_family_structural_context hstep hctx hsim hlevel) hΓ W HO ht R.2⟩

end Lean4Lean.VEnv.Strengthening
