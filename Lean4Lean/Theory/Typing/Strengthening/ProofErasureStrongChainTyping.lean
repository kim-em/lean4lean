import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalTyping
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDeclarations

/-! # Strong equality produces computational application typings

The pattern case receives the computational typings already constructed for its
source and reduct. Strong conversion nodes provide their type chains from
induction hypotheses. This avoids assuming that arbitrary ordinary typings
already contain computational index alignment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Remaining pattern coverage when both actual endpoints have structural
variable/constant/application typings with computational conversions, and all realized
checks have chains. Strong induction supplies these certificates; this premise
has not yet been proved for the general data-indexed singleton case. -/
def ComputationallyTypedPatternClosure (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures chk},
    OnCtx Γ (env.IsType univs) → env.pats p r → p.Matches e ls captures →
    HasTypeC D Γ e A → HasTypeC D Γ (r.1.apply ls captures) A →
    r.2.Realizes ls captures chk →
    (∀ t ∈ chk, TypedComputationEq D Γ t.1 t.2.1 t.2.2) →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- Strong derivations simultaneously give term chains and computational
application typings, assuming only the strengthened-input pattern obligation.
No type-fork joining or native coverage premise is needed for this induction. -/
theorem computational_typing_of_strong
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hpat : ComputationallyTypedPatternClosure EnvironmentCore.definitions)
    (H : env.IsDefEqStrong univs Γ a b A) (hΓ : OnCtx Γ (env.IsType univs)) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A := by
  induction H with
  | bvar h1 h2 h3 =>
    have H := (IsDefEqStrong.bvar h1 h2 h3).defeq
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
    have H := (IsDefEqStrong.constDF h1 h2 h3 h4 h5 h6 h7 h8).defeq
    exact ⟨.constDF hΓ h1 h2 h3 h4 h5, .const h1 H.hasType.1,
      .convert ⟨_, (ih8 hΓ).1.symm⟩ (.const h1 (HasType.const h1 h3
        ((Lean4Lean.List.Forall₂.length_eq h5).symm.trans h4))) H.hasType.2⟩
  | appDF h1 h2 h3 h4 h5 h6 h7 _ _ ih5 ih6 ih7 =>
    have H := (IsDefEqStrong.appDF h1 h2 h3 h4 h5 h6 h7).defeq
    obtain ⟨c5, j5, j5'⟩ := ih5 hΓ
    obtain ⟨c6, j6, j6'⟩ := ih6 hΓ
    exact ⟨.app hΓ c5 c6, .app j5 j6 H.hasType.1,
      .convert ⟨_, (ih7 hΓ).1.symm⟩
        (.app j5' j6' (h5.defeq.hasType.2.app h6.defeq.hasType.2)) H.hasType.2⟩
  | projDF hi hw hu hp hx hf hT ht hm hn hc hg _ ihm ihn =>
    have H := (IsDefEqStrong.projDF hi hw hu hp hx hf hT ht hm hn hc hg).defeq
    exact ⟨((ihm hΓ).1.symm.trans (ihn hΓ).1).proj hΓ H.hasType.1,
      .other not_app_proj not_const_proj (by intros; intro h; cases h) H.hasType.1, .other not_app_proj not_const_proj (by intros; intro h; cases h) H.hasType.2⟩
  | lamDF h1 h2 h3 h4 h5 h6 h7 ih3 _ _ ih6 _ =>
    have H := (IsDefEqStrong.lamDF h1 h2 h3 h4 h5 h6 h7).defeq
    exact ⟨.lam hΓ (ih3 hΓ).1 (ih6 ⟨hΓ, _, h3.defeq.hasType.1⟩).1,
      .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.1, .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.2⟩
  | forallEDF h1 h2 h3 h4 h5 ih3 ih4 _ =>
    have H := (IsDefEqStrong.forallEDF h1 h2 h3 h4 h5).defeq
    exact ⟨.forallE hΓ (ih3 hΓ).1 (ih4 ⟨hΓ, _, h3.defeq.hasType.1⟩).1,
      .other not_app_forallE not_const_forallE (by intros; intro h; cases h) H.hasType.1,
      .other not_app_forallE not_const_forallE (by intros; intro h; cases h) H.hasType.2⟩
  | defeqDF h1 h2 h3 ih2 ih3 =>
    have H := (IsDefEqStrong.defeqDF h1 h2 h3).defeq
    obtain ⟨c, j1, j2⟩ := ih3 hΓ
    have cA := (ih2 hΓ).1
    exact ⟨c.convert h2.defeq, .convert ⟨_, cA⟩ j1 H.hasType.1, .convert ⟨_, cA⟩ j2 H.hasType.2⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ ih8 =>
    have H := (IsDefEqStrong.beta h1 h2 h3 h4 h5 h6 h7 h8).defeq
    have hlam := HasType.lam h3.defeq h5.defeq
    exact ⟨.of_beta hΓ H.hasType.1 .beta,
      .app (.other not_app_lam not_const_lam (by intros; intro h; cases h) hlam) (ih6 hΓ).2.1 H.hasType.1, (ih8 hΓ).2.1⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    have H := (IsDefEqStrong.eta h1 h2 h3 h4 h5 h6 h7 h8).defeq
    exact ⟨(TypedComputationEq.eta heq EnvironmentCore.sound hΓ h6.defeq).symm,
      .other not_app_lam not_const_lam (by intros; intro h; cases h) H.hasType.1, (ih6 hΓ).2.1⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨.proof_irrel h1.defeq h2.defeq h3.defeq, (ih2 hΓ).2.1, (ih3 hΓ).2.1⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact ⟨.extra hcon hqpat hΓ h1 h2 h3, (ih8 hΓ).2.1, (ih9 hΓ).2.1⟩
  | pat hp hm he hred hr hall ihe ihred ihall =>
    have JL := (ihe hΓ).2.1
    have JR := (ihred hΓ).2.1
    exact ⟨hpat hΓ hp hm JL JR hr (fun t ht => (ihall t ht hΓ).1), JL, JR⟩
  | projIota hi ht hg hf iht ihf =>
    exact ⟨.projIota EnvironmentCore.sound hΓ hi ht.defeq hg hf.defeq, (iht hΓ).2.1, (ihf hΓ).2.1⟩
  | structEta hi hp hx hm hc ihm ihc =>
    exact ⟨.structEta heq EnvironmentCore.sound hΓ hi hp hx hm.defeq hc.defeq,
      (ihc hΓ).2.1, (ihm hΓ).2.1⟩
  | unitLike hi hp hx hz hm hn ihm ihn =>
    exact ⟨.unitLike heq EnvironmentCore.sound hΓ hi hp hx hz hm.defeq hn.defeq,
      (ihm hΓ).2.1, (ihn hΓ).2.1⟩

/-- Ordinary equality inherits the simultaneous result through the checked
strong-derivation translation. Pattern coverage with computational typings is
still explicit; no completeness result is asserted without it. -/
theorem computational_typing_of_defeq
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hpat : ComputationallyTypedPatternClosure EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A :=
  computational_typing_of_strong heq hcon hqpat hpat (H.strong henv.orderedStrong hΓ) hΓ

end Lean4Lean.VEnv.Strengthening
