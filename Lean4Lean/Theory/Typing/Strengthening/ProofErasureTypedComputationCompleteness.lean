import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDeclarations

/-! # The remaining pattern case of computation-chain completeness

All ordinary equality rules except checked registered patterns are now covered.
The missing case receives typed computation chains for every checked equation.
This isolates a completeness subproblem; it neither proves type-fork joining
nor claims a strictly smaller sufficient strengthening obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Missing pattern closure: a registered pattern with actually typed source
and reduct must yield a computation chain when its realized checks already
have such chains. The task is to align the checked captures and realize the
guarded primitive, without assuming native coverage or type-fork joining. -/
def TypedPatternChainClosure (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures chk},
    OnCtx Γ (env.IsType univs) → env.pats p r → p.Matches e ls captures →
    env.HasType univs Γ e A → env.HasType univs Γ (r.1.apply ls captures) A →
    r.2.Realizes ls captures chk →
    (∀ t ∈ chk, TypedComputationEq D Γ t.1 t.2.1 t.2.2) →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- Checked-pattern closure is the sole remaining constructor case in ordinary
equality completeness. Type-only computational joining is not used here. -/
theorem TypedComputationEq.of_defeq_of_pattern_closure
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hpat : TypedPatternChainClosure EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A := by
  induction H with
  | bvar h => exact .refl (.bvar h)
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hΓ).trans (ih₂ hΓ)
  | sortDF hu hv H => exact .sortDF hΓ hu hv H
  | constDF hc hw hw' hl HE => exact .constDF hΓ hc hw hw' hl HE
  | appDF _ _ ihf ihx => exact .app hΓ (ihf hΓ) (ihx hΓ)
  | projDF hi hw hu hp hx hf hT hm hn hc hg _ ihm ihn =>
    have H := IsDefEq.projDF hi hw hu hp hx hf hT hm hn hc hg
    exact ((ihm hΓ).symm.trans (ihn hΓ)).proj hΓ H.hasType.1
  | lamDF HA _ ihA ihb => exact .lam hΓ (ihA hΓ) (ihb ⟨hΓ, _, HA.hasType.1⟩)
  | forallEDF HA _ ihA ihB => exact .forallE hΓ (ihA hΓ) (ihB ⟨hΓ, _, HA.hasType.1⟩)
  | defeqDF HAB _ _ ih => exact (ih hΓ).convert HAB
  | beta hb hx _ _ => exact .of_beta hΓ (IsDefEq.beta hb hx).hasType.1 .beta
  | eta hf _ => exact (TypedComputationEq.eta heq EnvironmentCore.sound hΓ hf).symm
  | proofIrrel hP ha hb _ _ _ => exact .proof_irrel hP ha hb
  | extra hd hw hl => exact .extra hcon hqpat hΓ hd hw hl
  | pat hp hm he hr hc _ _ _ ihc => exact hpat hΓ hp hm he hr hc (fun t ht => ihc t ht hΓ)
  | projIota hi ht hg hf _ _ => exact .projIota EnvironmentCore.sound hΓ hi ht hg hf
  | structEta hi hp hx hm hc _ _ => exact .structEta heq EnvironmentCore.sound hΓ hi hp hx hm hc
  | unitLike hi hp hx hz hm hn _ _ => exact .unitLike heq EnvironmentCore.sound hΓ hi hp hx hz hm hn

/-- Pattern closure plus the independent type-fork joining obligation yields
common erased reducts for all ordinary type equalities. Neither hypothesis is
discharged by this conditional bridge. -/
theorem typed_type_join_of_pattern_closure
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hpat : TypedPatternChainClosure EnvironmentCore.definitions)
    (HF : TypeForkJoin EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b (.sort u)) :
    ∃ shared,
      ProofShape.ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
        (proofEraseCtx Γ) (proofErase Γ a) shared ∧
      ProofShape.ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions)
        (proofEraseCtx Γ) (proofErase Γ b) shared :=
  (TypedComputationEq.of_defeq_of_pattern_closure heq hcon hqpat hpat hΓ H).type_join
    heq EnvironmentCore.sound HF hΓ

end Lean4Lean.VEnv.Strengthening
