import Lean4Lean.Theory.Typing.Strengthening.DomainNormal

/-! # Proof erasure retaining all lambda annotations

A separate syntax erases proof payloads but retains every non-proof node, including
lambda domains. Reflection is deliberately typed: equal erasures reflect at
convertible endpoint types, or independently for a non-proof left endpoint.
Heterogeneous reflection of two arbitrary proofs is not claimed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Classical

/-- Proof-erased syntax. The marker is not an object-language term or a polymorphic
proof; its interpretation requires the original endpoint typings. -/
inductive ProofShape where
  | proof
  | bvar (i : Nat)
  | sort (u : VLevel)
  | const (c : Name) (ls : List VLevel)
  | app (f a : ProofShape)
  | proj (s : Name) (i : Nat) (m : ProofShape)
  | lam (A b : ProofShape)
  | forallE (A B : ProofShape)

variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- Erase proof payloads, keeping the displayed domain when traversing a binder. -/
noncomputable def proofErase : List VExpr → VExpr → ProofShape
  | Γ, e@(.bvar i) => if IsProof Γ e then .proof else .bvar i
  | Γ, e@(.sort u) => if IsProof Γ e then .proof else .sort u
  | Γ, e@(.const c ls) => if IsProof Γ e then .proof else .const c ls
  | Γ, e@(.app f a) => if IsProof Γ e then .proof else .app (proofErase Γ f) (proofErase Γ a)
  | Γ, e@(.proj s i m) => if IsProof Γ e then .proof else .proj s i (proofErase Γ m)
  | Γ, e@(.lam A b) => if IsProof Γ e then .proof else .lam (proofErase Γ A) (proofErase (A :: Γ) b)
  | Γ, e@(.forallE A B) => if IsProof Γ e then .proof else
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B)

/-- Exactly proofs erase to the proof marker. -/
theorem proofErase_eq_proof : proofErase Γ e = .proof ↔ IsProof Γ e := by
  cases e <;> simp only [proofErase] <;> split <;> simp_all

/-- Context conversion preserves whether a term is a proof. -/
theorem isProof_defeqCtx (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) :
    IsProof Γ₁ e ↔ IsProof Γ₂ e := by
  have forward {Δ₁ Δ₂} (W : IsDefEqCtx Params.env univs Γ₀ Δ₁ Δ₂) {t}
      (hp : IsProof Δ₁ t) : IsProof Δ₂ t := by
    obtain ⟨P, ht, hP⟩ := hp
    exact ⟨P, ht.defeqDFC henv W, hP.defeqDFC henv W⟩
  have Ws : IsDefEqCtx Params.env univs Γ₀ Γ₂ Γ₁ := by
    induction W with
    | zero => exact .zero
    | succ W h ih => exact .succ ih (h.symm.defeqDFC henv W)
  exact ⟨forward W, forward Ws⟩

/-- Typed erasure is invariant under conversion of the context. -/
theorem proofErase_defeqCtx (hΓ : OnCtx Γ₁ (Params.env.IsType univs))
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) (he : Γ₁ ⊢ e : T) :
    proofErase Γ₁ e = proofErase Γ₂ e := by
  induction e generalizing Γ₁ Γ₂ T with
  | bvar | sort | const => simp only [proofErase, isProof_defeqCtx W]
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    simp only [proofErase, isProof_defeqCtx W, ihf hΓ W hf, iha hΓ W ha]
  | proj s i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    simp only [proofErase, isProof_defeqCtx W, ih hΓ W hm.hasType.2]
  | lam A b ihA ihb =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    simp only [proofErase, isProof_defeqCtx W, ihA hΓ W hA, ihb (Γ₁ := A :: Γ₁) ⟨hΓ, _, hA⟩ (.succ W hA) hb]
  | forallE A B ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := he.forallE_inv henv
    simp only [proofErase, isProof_defeqCtx W, ihA hΓ W hA, ihB (Γ₁ := A :: Γ₁) ⟨hΓ, _, hA⟩ (.succ W hA) hB]

private theorem proofErase_modes (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B)
    (core : ¬ IsProof Γ a → ∃ n, DomainNormal n Γ a b) :
    (IsDefEqU Params.env univs Γ A B → ∃ n, DomainNormal n Γ a b) ∧
    (¬ IsProof Γ a → ∃ n, DomainNormal n Γ a b) := by
  refine ⟨fun hAB => ?_, core⟩
  by_cases hp : IsProof Γ a
  · obtain ⟨P, haP, hP⟩ := hp
    have hAP := ha.uniqU henv hΓ haP
    exact ⟨_, .proofIrrel hP haP (hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP))⟩
  · exact core hp

/-- Equal proof erasures yield recursive domain certificates in common-type mode
or for a non-proof endpoint. Proof payloads need no independent proposition-label
comparison: the surrounding typing supplies alignment at each proof position. -/
theorem proofErase_reflect (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B) (H : proofErase Γ a = proofErase Γ b) :
    (IsDefEqU Params.env univs Γ A B → ∃ n, DomainNormal n Γ a b) ∧
    (¬ IsProof Γ a → ∃ n, DomainNormal n Γ a b) := by
  induction a generalizing Γ b A B with
  | bvar i =>
    apply proofErase_modes hΓ ha hb
    intro hn
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    cases b <;> simp_all [proofErase]
    exact ⟨_, .refl ha⟩
  | sort u =>
    have hn := not_isProof_of_sort hΓ (HasType.sort (ha.sort_inv henv))
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    have core : ∃ n, DomainNormal n Γ (.sort u) b := by
      cases b <;> simp_all [proofErase]
      exact ⟨_, .refl ha⟩
    exact ⟨fun _ => core, fun _ => core⟩
  | const c ls =>
    apply proofErase_modes hΓ ha hb
    intro hn
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    cases b <;> simp_all [proofErase]
    exact ⟨_, .refl ha⟩
  | app f x ihf ihx =>
    apply proofErase_modes hΓ ha hb
    intro hn
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    cases b <;> simp only [proofErase, if_neg hn, if_neg hnb] at H <;> try contradiction
    case app f' x' =>
      obtain ⟨Hf, Hx⟩ := ProofShape.app.inj H
      obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
      obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
      obtain ⟨_, HF⟩ := (ihf hΓ hf hf' Hf).2 (not_isProof_fn hΓ hf hx hn)
      have hff := (HF.defeq hΓ).of_l henv hΓ hf
      obtain ⟨⟨_, hD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
      obtain ⟨_, HX⟩ := (ihx hΓ hx hx' Hx).1 ⟨_, hD⟩
      exact ⟨_, .appDF hf hff.hasType.2 hx ((HX.defeq hΓ).of_l henv hΓ hx).hasType.2 HF HX⟩
  | proj s i m ihm =>
    apply proofErase_modes hΓ ha hb
    intro hn
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    cases b <;> simp only [proofErase, if_neg hn, if_neg hnb] at H <;> try contradiction
    case proj s' i' m' =>
      obtain ⟨rfl, rfl, Hm⟩ := ProofShape.proj.inj H
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
      obtain ⟨_, HM⟩ := (ihm hΓ hm.hasType.2 hm'.hasType.2 Hm).2 (not_isProof_major hΓ ha hn)
      exact ⟨_, .projDF ha HM⟩
  | lam D t ihD iht =>
    apply proofErase_modes hΓ ha hb
    intro hn
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    cases b <;> simp only [proofErase, if_neg hn, if_neg hnb] at H <;> try contradiction
    case lam D' t' =>
      obtain ⟨HD, Ht⟩ := ProofShape.lam.inj H
      obtain ⟨⟨_, hD⟩, _, ht⟩ := ha.lam_inv henv hΓ
      obtain ⟨⟨_, hD'⟩, _, ht'⟩ := hb.lam_inv henv hΓ
      obtain ⟨_, HC⟩ := (ihD hΓ hD hD' HD).2 (not_isProof_of_sort hΓ hD)
      have hDD := (HC.defeq hΓ).of_l henv hΓ hD
      have W := IsDefEqCtx.succ .zero hDD.symm
      rw [proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ W ht'] at Ht
      have ht'' := ht'.defeqDFC henv W
      obtain ⟨_, HT⟩ := (iht (Γ := D :: Γ) ⟨hΓ, _, hD⟩ ht ht'' Ht).2 (fun hp => hn (hp.lam hΓ hD))
      exact ⟨_, .lamDF hD HC HT⟩
  | forallE D C ihD ihC =>
    obtain ⟨⟨_, hD⟩, _, hC⟩ := ha.forallE_inv henv
    have hn := not_isProof_of_sort hΓ (HasType.forallE hD hC)
    have hnb : ¬ IsProof Γ b := fun hp => hn (proofErase_eq_proof.1 (H.trans (proofErase_eq_proof.2 hp)))
    have core : ∃ n, DomainNormal n Γ (.forallE D C) b := by
      cases b <;> simp only [proofErase, if_neg hn, if_neg hnb] at H <;> try contradiction
      case forallE D' C' =>
        obtain ⟨HD, HB⟩ := ProofShape.forallE.inj H
        obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
        obtain ⟨_, HC⟩ := (ihD hΓ hD hD' HD).2 (not_isProof_of_sort hΓ hD)
        have hDD := (HC.defeq hΓ).of_l henv hΓ hD
        have W := IsDefEqCtx.succ .zero hDD.symm
        rw [proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ W hC'] at HB
        obtain ⟨_, HB'⟩ := (ihC (Γ := D :: Γ) ⟨hΓ, _, hD⟩ hC (hC'.defeqDFC henv W) HB).2
          (not_isProof_of_sort ⟨hΓ, _, hD⟩ hC)
        exact ⟨_, .forallEDF hD HC hC HB'⟩
    exact ⟨fun _ => core, fun _ => core⟩

end Lean4Lean.VEnv.Strengthening
