import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitution

/-! # Simultaneous typed substitution in annotated proof erasures

Only non-proof source variables constrain the erased substitution. This support
condition remains valid under binders even when a new bound variable is a proof
and therefore disappears from the erased body. The result supplies uniform RHS
template erasure from typed capture substitutions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Simultaneous substitutions on erased syntax. -/
abbrev Subst := Nat → ProofShape

/-- Enter a binder while preserving its new de Bruijn variable. -/
def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i + 1 => (σ i).liftN 1

/-- Apply a simultaneous substitution, leaving proof markers unchanged. -/
def subst : ProofShape → Subst → ProofShape
  | .proof, _ => .proof
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c ls, _ => .const c ls
  | .app f a, σ => .app (f.subst σ) (a.subst σ)
  | .proj s i m, σ => .proj s i (m.subst σ)
  | .lam A b, σ => .lam (A.subst σ) (b.subst σ.lift)
  | .forallE A B, σ => .forallE (A.subst σ) (B.subst σ.lift)
end ProofShape

variable [Params]

/-- Simultaneous typed substitution preserves and reflects proofness. Universe
uniqueness reflects the source type's Prop sort without strengthening. -/
theorem isProof_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (he : env.HasType univs Γ e T) :
    IsProof Γ₀ (e.subst σ) ↔ IsProof Γ e := by
  constructor
  · rintro ⟨P, heP, hP⟩
    obtain ⟨u, hT⟩ := he.isType henv W.wf
    have he' := he.subst henv.orderedStrong W hΓ₀
    have hT' := hT.subst henv.orderedStrong W hΓ₀
    have htP := he'.uniqU henv hΓ₀ heP
    have hT0 := hP.defeqU_l henv hΓ₀ htP.symm
    have hu := (hT'.uniqU henv hΓ₀ hT0).sort_inv henv hΓ₀
    exact ⟨T, he, (IsDefEq.sortDF (hT.sort_r henv W.wf) (by trivial) hu).defeq hT⟩
  · rintro ⟨P, heP, hP⟩
    exact ⟨P.subst σ, heP.subst henv.orderedStrong W hΓ₀,
      hP.subst henv.orderedStrong W hΓ₀⟩

/-- Agreement is needed only at variables retained by typed erasure. -/
def ErasedSubstAgreement (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) → proofErase Γ₀ (σ i) = τ i

/-- The support condition survives binder extension. A proof-valued fresh
variable never constrains the erased substitution at index zero. -/
theorem ErasedSubstAgreement.lift (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (hA : env.HasType univs Γ A (.sort u))
    (H : ErasedSubstAgreement Γ Γ₀ σ τ) :
    ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  have hA' := hA.subst henv.orderedStrong W hΓ₀
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨W.wf, _, hA⟩
  have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, _, hA'⟩
  intro i B hl hn
  cases hl with
  | zero =>
    have hn' : ¬ IsProof (A.subst σ :: Γ₀) (.bvar 0) :=
      fun hp => hn ((isProof_subst hΓA' (W.lift henv.ordered hA) (.bvar .zero)).1 hp)
    simp only [VExpr.Subst.lift, ProofShape.Subst.lift, proofErase, if_neg hn']
  | @succ _ i B _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hx := (W.lookup hl).hasType.1
    have HE := proofErase_liftN hΓ₀ hΓA' (Ctx.LiftN.one) hx
    simpa only [VExpr.Subst.lift, ProofShape.Subst.lift, H hl hn₀] using HE

/-- Erasure commutes with typed simultaneous substitution on all retained
variables. Proof captures need no syntactic representative in the erased map. -/
theorem proofErase_subst_with (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (he : env.HasType univs Γ e T)
    (H : ErasedSubstAgreement Γ Γ₀ σ τ) :
    proofErase Γ₀ (e.subst σ) = (proofErase Γ e).subst τ := by
  induction e generalizing Γ Γ₀ σ τ T
  case bvar i =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.bvar i)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    obtain ⟨B, hl⟩ := he.bvar_inv henv W.wf
    simpa only [VExpr.subst, proofErase, if_neg hn, ProofShape.subst] using H hl hn
  case sort u =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.sort u)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    simpa only [VExpr.subst, proofErase, if_neg hn, ProofShape.subst] using
      (show proofErase Γ₀ (.sort u) = .sort u from if_neg hn')
  case const c ls =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.const c ls)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    simpa only [VExpr.subst, proofErase, if_neg hn, ProofShape.subst] using
      (show proofErase Γ₀ (.const c ls) = .const c ls from if_neg hn')
  case app f a ihf iha =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.app f a)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv W.wf
    simp only [VExpr.subst] at hn'
    simp only [VExpr.subst, proofErase, if_neg hn, if_neg hn', ProofShape.subst]
    exact congr (congrArg ProofShape.app (ihf hΓ₀ W hf H)) (iha hΓ₀ W ha H)
  case proj s i m ih =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.proj s i m)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    simp only [VExpr.subst] at hn'
    simp only [VExpr.subst, proofErase, if_neg hn, if_neg hn', ProofShape.subst]
    exact congrArg (ProofShape.proj s i) (ih hΓ₀ W hm.hasType.2 H)
  case lam A b ihA ihb =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.lam A b)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv W.wf
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, _, hA.subst henv.orderedStrong W hΓ₀⟩
    simp only [VExpr.subst] at hn'
    simp only [VExpr.subst, proofErase, if_neg hn, if_neg hn', ProofShape.subst]
    exact congr (congrArg ProofShape.lam (ihA hΓ₀ W hA H))
      (ihb hΓA' (W.lift henv.ordered hA) hb (H.lift hΓ₀ W hA))
  case forallE A B ihA ihB =>
    have hp := isProof_subst hΓ₀ W he
    by_cases hn : IsProof Γ (.forallE A B)
    · rw [proofErase_eq_proof.2 (hp.2 hn), proofErase_eq_proof.2 hn]
      rfl
    have hn' := mt hp.1 hn
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, _, hA.subst henv.orderedStrong W hΓ₀⟩
    simp only [VExpr.subst] at hn'
    simp only [VExpr.subst, proofErase, if_neg hn, if_neg hn', ProofShape.subst]
    exact congr (congrArg ProofShape.forallE (ihA hΓ₀ W hA H))
      (ihB hΓA' (W.lift henv.ordered hA) hB (H.lift hΓ₀ W hA))

/-- The canonical erased map simply erases every substituted argument. -/
theorem proofErase_subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (he : env.HasType univs Γ e T) :
    proofErase Γ₀ (e.subst σ) = (proofErase Γ e).subst (fun i => proofErase Γ₀ (σ i)) :=
  proofErase_subst_with hΓ₀ W he (fun _ _ => rfl)

/-- A typed template has the same erased result in different target contexts
whenever all its non-proof captures have the same erasure. -/
theorem proofErase_template_congr
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₁ σ₁ σ₁ Δ) (W₂ : Ctx.SubstEq env univs Γ₂ σ₂ σ₂ Δ)
    (he : env.HasType univs Δ e T)
    (H : ∀ {i A}, Lookup Δ i A → ¬ IsProof Δ (.bvar i) →
      proofErase Γ₁ (σ₁ i) = proofErase Γ₂ (σ₂ i)) :
    proofErase Γ₁ (e.subst σ₁) = proofErase Γ₂ (e.subst σ₂) := by
  rw [proofErase_subst hΓ₁ W₁ he]
  exact (proofErase_subst_with hΓ₂ W₂ he (fun hl hn => (H hl hn).symm)).symm

end Lean4Lean.VEnv.Strengthening
