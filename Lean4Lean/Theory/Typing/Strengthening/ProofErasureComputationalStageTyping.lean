import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongChainTyping

/-! # Interpreting earlier strong derivations in the ambient computation system

Only patterns of the earlier environment need coverage. All chain operations
and structural typing certificates live in the ambient environment, so no
transport of erased computations between different environments is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Coverage of one pattern with computational endpoint certificates. This
interface can be restricted to a particular earlier registry by its caller. -/
def ComputationalPatternCoverage (D : PureObservation.Definitions)
    (p : Pattern) (r : p.RHS × p.Check) : Prop :=
  ∀ {Γ e A ls captures chk}, OnCtx Γ (env.IsType univs) → p.Matches e ls captures →
    HasTypeC D Γ e A → HasTypeC D Γ (r.1.apply ls captures) A →
    r.2.Realizes ls captures chk →
    (∀ t ∈ chk, TypedComputationEq D Γ t.1 t.2.1 t.2.2) →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- Earlier strong derivations produce ambient computation chains and
structural typings from coverage restricted to the earlier pattern registry.
This is the induction interface for declaration history; it does not assert
that the earlier patterns have already been covered. -/
theorem computational_typing_of_strong_earlier
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    {E : VEnv} (hE : E ≤ env)
    (hpat : ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures chk},
      OnCtx Γ (env.IsType univs) → E.pats p r → p.Matches e ls captures →
      HasTypeC EnvironmentCore.definitions Γ e A →
      HasTypeC EnvironmentCore.definitions Γ (r.1.apply ls captures) A →
      r.2.Realizes ls captures chk →
      (∀ t ∈ chk, TypedComputationEq EnvironmentCore.definitions Γ t.1 t.2.1 t.2.2) →
      TypedComputationEq EnvironmentCore.definitions Γ e (r.1.apply ls captures) A)
    (H : E.IsDefEqStrong univs Γ a b A) (hΓ : OnCtx Γ (env.IsType univs)) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A := by
  induction H with
  | bvar h1 h2 h3 =>
    have H := ((IsDefEqStrong.bvar h1 h2 h3).mono hE).defeq
    exact ⟨.refl H, .bvar h1, .bvar h1⟩
  | symm _ ih =>
    obtain ⟨H, ha, hb⟩ := ih hΓ
    exact ⟨H.symm, hb, ha⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨H₁, ha, _⟩ := ih₁ hΓ
    obtain ⟨H₂, _, hc⟩ := ih₂ hΓ
    exact ⟨H₁.trans H₂, ha, hc⟩
  | sortDF h1 h2 h3 =>
    have C := TypedComputationEq.sortDF (D := EnvironmentCore.definitions) hΓ h1 h2 h3
    have H := C.defeq
    exact ⟨.sortDF hΓ h1 h2 h3, .other not_app_sort not_const_sort (by intros; intro h; cases h) H.hasType.1,
      .other not_app_sort not_const_sort (by intros; intro h; cases h) H.hasType.2⟩
  | constDF h1 h2 h3 h4 h5 h6 h7 h8 _ ih8 =>
    have H := ((IsDefEqStrong.constDF h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    exact ⟨.constDF hΓ (hE.constants h1) h2 h3 h4 h5, .const (hE.constants h1) H.hasType.1,
      .convert ⟨_, (ih8 hΓ).1.symm⟩ (.const (hE.constants h1) (HasType.const (hE.constants h1) h3
        ((Lean4Lean.List.Forall₂.length_eq h5).symm.trans h4))) H.hasType.2⟩
  | appDF h1 h2 h3 h4 h5 h6 h7 _ _ ih5 ih6 ih7 =>
    have H := ((IsDefEqStrong.appDF h1 h2 h3 h4 h5 h6 h7).mono hE).defeq
    obtain ⟨c5, j5, j5'⟩ := ih5 hΓ
    obtain ⟨c6, j6, j6'⟩ := ih6 hΓ
    exact ⟨.app hΓ c5 c6, .app j5 j6 H.hasType.1,
      .convert ⟨_, (ih7 hΓ).1.symm⟩
        (.app j5' j6' ((h5.mono hE).defeq.hasType.2.app (h6.mono hE).defeq.hasType.2)) H.hasType.2⟩
  | projDF hi hw hu hp hx hf hT ht hm hn hc hg _ ihm ihn =>
    have H := ((IsDefEqStrong.projDF hi hw hu hp hx hf hT ht hm hn hc hg).mono hE).defeq
    exact ⟨((ihm hΓ).1.symm.trans (ihn hΓ).1).proj hΓ H.hasType.1,
      .other not_app_proj not_const_proj (by intros; intro h; cases h) H.hasType.1, .other not_app_proj not_const_proj (by intros; intro h; cases h) H.hasType.2⟩
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih3 _ _ ih6 _ =>
    have H := ((IsDefEqStrong.lamDF h1 h2 h3 h4 h5 h6 h7).mono hE).defeq
    exact ⟨.lam hΓ (ih3 hΓ).1 (ih6 ⟨hΓ, _, (h3.mono hE).defeq.hasType.1⟩).1,
      .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.1, .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.2⟩
  | forallEDF h1 h2 h3 h4 h5 ih3 ih4 _ =>
    have H := ((IsDefEqStrong.forallEDF h1 h2 h3 h4 h5).mono hE).defeq
    exact ⟨.forallE hΓ (ih3 hΓ).1 (ih4 ⟨hΓ, _, (h3.mono hE).defeq.hasType.1⟩).1,
      .other not_app_forallE not_const_forallE (by intros; intro h; cases h) H.hasType.1,
      .other not_app_forallE not_const_forallE (by intros; intro h; cases h) H.hasType.2⟩
  | defeqDF h1 h2 h3 ih2 ih3 =>
    have H := ((IsDefEqStrong.defeqDF h1 h2 h3).mono hE).defeq
    obtain ⟨c, j1, j2⟩ := ih3 hΓ
    have cA := (ih2 hΓ).1
    exact ⟨c.convert (h2.mono hE).defeq, .convert ⟨_, cA⟩ j1 H.hasType.1, .convert ⟨_, cA⟩ j2 H.hasType.2⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ ih8 =>
    have H := ((IsDefEqStrong.beta h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    have hlam := HasType.lam (h3.mono hE).defeq (h5.mono hE).defeq
    exact ⟨.of_beta hΓ H.hasType.1 .beta,
      .app (.other not_app_lam not_const_lam (by intros; intro h; cases h) hlam) (ih6 hΓ).2.1 H.hasType.1, (ih8 hΓ).2.1⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    have H := ((IsDefEqStrong.eta h1 h2 h3 h4 h5 h6 h7 h8).mono hE).defeq
    exact ⟨(TypedComputationEq.eta heq EnvironmentCore.sound hΓ (h6.mono hE).defeq).symm,
      .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.1, (ih6 hΓ).2.1⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨.proof_irrel (h1.mono hE).defeq (h2.mono hE).defeq (h3.mono hE).defeq, (ih2 hΓ).2.1, (ih3 hΓ).2.1⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact ⟨.extra hcon hqpat hΓ (hE.defeqs h1) h2 h3, (ih8 hΓ).2.1, (ih9 hΓ).2.1⟩
  | pat hp hm he hred hr hall ihe ihred ihall =>
    have JL := (ihe hΓ).2.1
    have JR := (ihred hΓ).2.1
    exact ⟨hpat hΓ hp hm JL JR hr (fun t ht => (ihall t ht hΓ).1), JL, JR⟩
  | projIota hi ht hg hf iht ihf =>
    exact ⟨.projIota EnvironmentCore.sound hΓ (hE.projections hi) (ht.mono hE).defeq hg (hf.mono hE).defeq, (iht hΓ).2.1, (ihf hΓ).2.1⟩
  | structEta hi hp hx hm hc ihm ihc =>
    exact ⟨.structEta heq EnvironmentCore.sound hΓ (hE.projections hi) hp hx (hm.mono hE).defeq (hc.mono hE).defeq,
      (ihc hΓ).2.1, (ihm hΓ).2.1⟩
  | unitLike hi hp hx hz hm hn ihm ihn =>
    exact ⟨.unitLike heq EnvironmentCore.sound hΓ (hE.projections hi) hp hx hz (hm.mono hE).defeq (hn.mono hE).defeq,
      (ihm hΓ).2.1, (ihn hΓ).2.1⟩

end Lean4Lean.VEnv.Strengthening
