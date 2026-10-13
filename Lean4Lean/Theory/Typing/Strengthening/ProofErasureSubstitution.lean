import Lean4Lean.Theory.Typing.Strengthening.ProofErasure

/-! # Renaming and substitution for annotated proof erasure

Proof classification is preserved by typed substitution. Consequently the single
proof marker commutes with substitution while all non-proof syntax and annotations
are retained. No typing is assigned to the marker in the original calculus.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Classical

namespace ProofShape
/-- Insert variables in proof-erased syntax; proof markers have no free variables. -/
def liftN (n : Nat) : ProofShape → (k : Nat := 0) → ProofShape
  | .proof, _ => .proof
  | .bvar i, k => .bvar (Lean4Lean.liftVar n i k)
  | .sort u, _ => .sort u
  | .const c ls, _ => .const c ls
  | .app f a, k => .app (f.liftN n k) (a.liftN n k)
  | .proj s i m, k => .proj s i (m.liftN n k)
  | .lam A b, k => .lam (A.liftN n k) (b.liftN n (k+1))
  | .forallE A B, k => .forallE (A.liftN n k) (B.liftN n (k+1))

/-- Substitute an erased argument at de Bruijn depth `k`. -/
def inst : ProofShape → ProofShape → (k : Nat := 0) → ProofShape
  | .proof, _, _ => .proof
  | .bvar i, x, k => if i < k then .bvar i else if i = k then x.liftN k else .bvar (i-1)
  | .sort u, _, _ => .sort u
  | .const c ls, _, _ => .const c ls
  | .app f a, x, k => .app (f.inst x k) (a.inst x k)
  | .proj s i m, x, k => .proj s i (m.inst x k)
  | .lam A b, x, k => .lam (A.inst x k) (b.inst x (k+1))
  | .forallE A B, x, k => .forallE (A.inst x k) (B.inst x (k+1))
/-- Erased renaming is injective, including in the presence of proof markers. -/
theorem liftN_inj {a b : ProofShape} : a.liftN n k = b.liftN n k ↔ a = b := by
  induction a generalizing b k <;> cases b <;> simp_all [liftN, VExpr.liftVar_inj]
end ProofShape

variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- Proofness is reflected and preserved by a typed binder insertion. -/
theorem isProof_liftN (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.LiftN n k Γ Γ') (he : Γ ⊢ e : T) :
    IsProof Γ' (e.liftN n k) ↔ IsProof Γ e := by
  rw [← lift'_consN_skipN]
  exact ⟨fun ⟨_, hp, hP⟩ => IsProof.of_lift hΓ hΓ' (Ctx.liftN_iff_lift'.1 W) he hP hp,
    IsProof.lift' (Ctx.liftN_iff_lift'.1 W)⟩

/-- Erasure commutes with insertion of any number of binders at any depth. -/
theorem proofErase_liftN (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.LiftN n k Γ Γ') (he : Γ ⊢ e : T) :
    proofErase Γ' (e.liftN n k) = (proofErase Γ e).liftN n k := by
  have hp := isProof_liftN hΓ hΓ' W he
  induction e generalizing Γ Γ' k T with
  | bvar | sort | const =>
    simp only [VExpr.liftN] at hp
    simp only [VExpr.liftN, proofErase, hp]
    split <;> simp_all only [ProofShape.liftN]
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    simp only [VExpr.liftN] at hp
    simp only [VExpr.liftN, proofErase, hp,
      ihf hΓ hΓ' W hf (isProof_liftN hΓ hΓ' W hf),
      iha hΓ hΓ' W ha (isProof_liftN hΓ hΓ' W ha)]
    split <;> simp_all only [ProofShape.liftN]
  | proj s i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    simp only [VExpr.liftN] at hp
    simp only [VExpr.liftN, proofErase, hp,
      ih hΓ hΓ' W hm.hasType.2 (isProof_liftN hΓ hΓ' W hm.hasType.2)]
    split <;> simp_all only [ProofShape.liftN]
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    simp only [VExpr.liftN] at hp
    simp only [VExpr.liftN, proofErase, hp,
      ihA hΓ hΓ' W hA (isProof_liftN hΓ hΓ' W hA),
      ihb hΓA hΓA' W.succ hb (isProof_liftN hΓA hΓA' W.succ hb)]
    split <;> simp_all only [ProofShape.liftN]
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    simp only [VExpr.liftN] at hp
    simp only [VExpr.liftN, proofErase, hp,
      ihA hΓ hΓ' W hA (isProof_liftN hΓ hΓ' W hA),
      ihB hΓA hΓA' W.succ hB (isProof_liftN hΓA hΓA' W.succ hB)]
    split <;> simp_all only [ProofShape.liftN]

/-- Typed substitution does not change whether a term is a proof. -/
theorem isProof_instN (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hx : Γ₀ ⊢ x : A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (he : Γ₁ ⊢ e : T) :
    IsProof Γ (e.inst x k) ↔ IsProof Γ₁ e := by
  have hΓ := (W.wf henv hx hΓ₁).2
  constructor
  · rintro ⟨P, heP, hP⟩
    obtain ⟨u, hT⟩ := he.isType henv hΓ₁
    have he' := he.instN henv W hx
    have hT' := hT.instN henv W hx
    have htP := he'.uniqU henv hΓ heP
    have hT0 := hP.defeqU_l henv hΓ htP.symm
    have hu := (hT'.uniqU henv hΓ hT0).sort_inv henv hΓ
    exact ⟨T, he, (IsDefEq.sortDF (hT.sort_r henv hΓ₁) (by trivial) hu).defeq hT⟩
  · rintro ⟨P, heP, hP⟩
    exact ⟨P.inst x k, heP.instN henv W hx, hP.instN henv W hx⟩

omit [Params] in
private theorem instN_target_lift (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) :
    Ctx.LiftN k 0 Γ₀ Γ := by
  apply Ctx.liftN_iff_lift'.2
  change Ctx.Lift' (Lift.skipN .refl k) Γ₀ Γ
  induction W with
  | zero => exact .refl
  | succ _ ih => exact .skip ih

/-- Erasure commutes with arbitrary typed single-variable substitution, including
under binders and when the argument is a proof. -/
theorem proofErase_instN (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (hx : Γ₀ ⊢ x : A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (he : Γ₁ ⊢ e : T) :
    proofErase Γ (e.inst x k) = (proofErase Γ₁ e).inst (proofErase Γ₀ x) k := by
  have hp := isProof_instN hΓ₁ hx W he
  by_cases hp₁ : IsProof Γ₁ e
  · rw [proofErase_eq_proof.2 (hp.2 hp₁), proofErase_eq_proof.2 hp₁]
    rfl
  have hp₂ : ¬ IsProof Γ (e.inst x k) := fun h => hp₁ (hp.1 h)
  induction e generalizing Γ₁ Γ k T with
  | bvar i =>
    simp only [proofErase, if_neg hp₁, ProofShape.inst, VExpr.inst, VExpr.instVar]
    split
    · simp only [VExpr.inst, VExpr.instVar, if_pos ‹i < k›] at hp₂
      exact if_neg hp₂
    · split
      · rename_i hi
        subst i
        have hΓs := W.wf henv hx hΓ₁
        have Wlift := instN_target_lift W
        exact proofErase_liftN hΓs.1 hΓs.2 Wlift hx
      · simp only [VExpr.inst, VExpr.instVar, if_neg ‹¬i < k›, if_neg ‹i ≠ k›] at hp₂
        exact if_neg hp₂
  | sort | const =>
    simp only [VExpr.inst] at hp₂
    simp only [VExpr.inst, proofErase, if_neg hp₁, if_neg hp₂, ProofShape.inst]
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ₁
    simp only [VExpr.inst] at hp₂
    simp only [VExpr.inst, proofErase, if_neg hp₁, if_neg hp₂, ProofShape.inst]
    congr 1
    · exact ihf hΓ₁ W hf (isProof_instN hΓ₁ hx W hf) (not_isProof_fn hΓ₁ hf ha hp₁)
        (fun h => (not_isProof_fn hΓ₁ hf ha hp₁) ((isProof_instN hΓ₁ hx W hf).1 h))
    · by_cases hpa : IsProof Γ₁ a
      · rw [proofErase_eq_proof.2 ((isProof_instN hΓ₁ hx W ha).2 hpa), proofErase_eq_proof.2 hpa]
        rfl
      · exact iha hΓ₁ W ha (isProof_instN hΓ₁ hx W ha) hpa
          (fun h => hpa ((isProof_instN hΓ₁ hx W ha).1 h))
  | proj s i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ₁
    have hnm := not_isProof_major hΓ₁ he hp₁
    simp only [VExpr.inst] at hp₂
    simp only [VExpr.inst, proofErase, if_neg hp₁, if_neg hp₂, ProofShape.inst]
    exact congrArg (ProofShape.proj s i) (ih hΓ₁ W hm.hasType.2
      (isProof_instN hΓ₁ hx W hm.hasType.2) hnm
      (fun h => hnm ((isProof_instN hΓ₁ hx W hm.hasType.2).1 h)))
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ₁
    have hΓA : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    have hnA := not_isProof_of_sort hΓ₁ hA
    have hnb : ¬ IsProof (A :: Γ₁) b := fun h => hp₁ (h.lam hΓ₁ hA)
    simp only [VExpr.inst] at hp₂
    simp only [VExpr.inst, proofErase, if_neg hp₁, if_neg hp₂, ProofShape.inst]
    exact congr (congrArg ProofShape.lam
      (ihA hΓ₁ W hA (isProof_instN hΓ₁ hx W hA) hnA
        (fun h => hnA ((isProof_instN hΓ₁ hx W hA).1 h))))
      (ihb hΓA W.succ hb (isProof_instN hΓA hx W.succ hb) hnb
        (fun h => hnb ((isProof_instN hΓA hx W.succ hb).1 h)))
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    have hnA := not_isProof_of_sort hΓ₁ hA
    have hnB := not_isProof_of_sort hΓA hB
    simp only [VExpr.inst] at hp₂
    simp only [VExpr.inst, proofErase, if_neg hp₁, if_neg hp₂, ProofShape.inst]
    exact congr (congrArg ProofShape.forallE
      (ihA hΓ₁ W hA (isProof_instN hΓ₁ hx W hA) hnA
        (fun h => hnA ((isProof_instN hΓ₁ hx W hA).1 h))))
      (ihB hΓA W.succ hB (isProof_instN hΓA hx W.succ hB) hnB
        (fun h => hnB ((isProof_instN hΓA hx W.succ hB).1 h)))

/-- Equality of erased lifted terms descends when the originals are independently
well typed. As for ordinary erasure reflection, comparison requires convertible
endpoint types or a non-proof left endpoint; arbitrary conversion of erased terms
is not assumed. -/
theorem proofErase_lift_reflect (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B)
    (H : proofErase Γ' (a.liftN n k) = proofErase Γ' (b.liftN n k)) :
    (IsDefEqU Params.env univs Γ A B → ∃ m, DomainNormal m Γ a b) ∧
    (¬ IsProof Γ a → ∃ m, DomainNormal m Γ a b) := by
  rw [proofErase_liftN hΓ hΓ' W ha, proofErase_liftN hΓ hΓ' W hb, ProofShape.liftN_inj] at H
  exact proofErase_reflect hΓ ha hb H

end Lean4Lean.VEnv.Strengthening
