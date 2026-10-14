import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK

/-! # Raw retraction of erased certificates through arbitrary thinning

Erased substitutions need no typed inhabitant for a removed variable. Every
thinning has a raw left inverse, so a substitution-stable certificate descends
by retracting the certificate and reflecting at its already typed endpoints.
This does not assert that arbitrary declarative equalities have certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- General variable thinning on annotated proof shapes. -/
def lift' : ProofShape → Lift → ProofShape
  | .proof, _ => .proof
  | .bvar i, ρ => .bvar (ρ.liftVar i)
  | .sort u, _ => .sort u
  | .const c ls, _ => .const c ls
  | .app f a, ρ => .app (f.lift' ρ) (a.lift' ρ)
  | .proj s i m, ρ => .proj s i (m.lift' ρ)
  | .lam A b, ρ => .lam (A.lift' ρ) (b.lift' ρ.cons)
  | .forallE A B, ρ => .forallE (A.lift' ρ) (B.lift' ρ.cons)

/-- General thinning is a raw substitution by renamed variables. -/
theorem lift'_eq_subst (e : ProofShape) (ρ : Lift) :
    e.lift' ρ = e.subst (fun i => .bvar (ρ.liftVar i)) := by
  induction e generalizing ρ with
  | proof | bvar | sort | const => rfl
  | app f a ihf iha => simp only [lift', subst, ihf, iha]
  | proj s i m ih => simp only [lift', subst, ih]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HH : (fun i => bvar (ρ.cons.liftVar i)) =
        Subst.lift (fun i => bvar (ρ.liftVar i)) := by
      funext i
      cases i <;> simp [Lift.liftVar, Subst.lift, ProofShape.liftN, _root_.Lean4Lean.liftVar] <;> omega
    simp only [lift', subst, ihA, ihb, HH]

/-- A raw left inverse uses a proof marker at skipped variables. No typing is
claimed for these images, which never occur in a thinned source endpoint. -/
def Subst.retract : Lift → Subst
  | .refl => .id
  | .skip ρ => (retract ρ).cons .proof
  | .cons ρ => (retract ρ).lift

/-- Retained variables are recovered exactly by the raw inverse. -/
theorem Subst.retract_liftVar (ρ : Lift) (i : Nat) :
    Subst.retract ρ (ρ.liftVar i) = .bvar i := by
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simpa only [retract, Lift.liftVar, cons] using ih i
  | cons ρ ih =>
    cases i <;> simp [retract, Lift.liftVar, Subst.lift, ih, ProofShape.liftN, _root_.Lean4Lean.liftVar] <;> omega

/-- Substitution absorbs general thinning whenever it agrees on retained variables. -/
theorem subst_lift'_agree (e : ProofShape) {σ τ : Subst}
    (H : ∀ i, τ (ρ.liftVar i) = σ i) :
    (e.lift' ρ).subst τ = e.subst σ := by
  induction e generalizing ρ σ τ with
  | proof | sort | const => rfl
  | bvar i => exact H i
  | app f a ihf iha => simp only [lift', subst, ihf H, iha H]
  | proj s i m ih => simp only [lift', subst, ih H]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    have HB : ∀ i, τ.lift (ρ.cons.liftVar i) = σ.lift i := by
      intro i
      cases i <;> simp only [Lift.liftVar, Subst.lift, H]
    simp only [lift', subst, ihA H, ihb HB]

/-- Retraction removes all inserted variables from every original proof shape. -/
theorem subst_retract_lift' (e : ProofShape) (ρ : Lift) :
    (e.lift' ρ).subst (Subst.retract ρ) = e := by
  rw [subst_lift'_agree e (Subst.retract_liftVar ρ)]
  exact ProofShape.subst_id e

/-- Any relation stable under raw substitution reflects through thinning. -/
theorem relation_lift'_reflect {R : ProofShape → ProofShape → Prop} {a b : ProofShape} {ρ : Lift}
    (hsubst : ∀ {a b} (σ : Subst), R a b → R (a.subst σ) (b.subst σ))
    (H : R (a.lift' ρ) (b.lift' ρ)) : R a b := by
  simpa only [subst_retract_lift'] using hsubst (Subst.retract ρ) H
/-- Substitution-stable relations are invariant under arbitrary thinning. -/
theorem relation_lift'_iff {R : ProofShape → ProofShape → Prop} {a b : ProofShape} {ρ : Lift}
    (hsubst : ∀ {a b} (σ : Subst), R a b → R (a.subst σ) (b.subst σ)) :
    R (a.lift' ρ) (b.lift' ρ) ↔ R a b := by
  refine ⟨relation_lift'_reflect hsubst, fun H => ?_⟩
  simpa only [lift'_eq_subst] using hsubst (fun i => .bvar (ρ.liftVar i)) H
end ProofShape

variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- Proof classification is invariant under every well-formed context thinning. -/
theorem isProof_lift' (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') (he : Γ ⊢ e : T) :
    IsProof Γ' (e.lift' ρ) ↔ IsProof Γ e :=
  ⟨fun ⟨_, hp, hP⟩ => IsProof.of_lift hΓ hΓ' W he hP hp, IsProof.lift' W⟩

/-- Typed erasure commutes with arbitrary context thinning. -/
theorem proofErase_lift' (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') (he : Γ ⊢ e : T) :
    proofErase Γ' (e.lift' ρ) = (proofErase Γ e).lift' ρ := by
  have hp := isProof_lift' hΓ hΓ' W he
  induction e generalizing Γ Γ' ρ T with
  | bvar | sort | const =>
    simp only [VExpr.lift'] at hp
    simp only [VExpr.lift', proofErase, hp]
    split <;> simp_all [ProofShape.lift']
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    simp only [VExpr.lift'] at hp
    simp only [VExpr.lift', proofErase, hp,
      ihf hΓ hΓ' W hf (isProof_lift' hΓ hΓ' W hf),
      iha hΓ hΓ' W ha (isProof_lift' hΓ hΓ' W ha)]
    split <;> simp_all [ProofShape.lift']
  | proj s i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    simp only [VExpr.lift'] at hp
    simp only [VExpr.lift', proofErase, hp,
      ih hΓ hΓ' W hm.hasType.2 (isProof_lift' hΓ hΓ' W hm.hasType.2)]
    split <;> simp_all [ProofShape.lift']
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hA.weak' henv.ordered W⟩
    simp only [VExpr.lift'] at hp
    simp only [VExpr.lift', proofErase, hp,
      ihA hΓ hΓ' W hA (isProof_lift' hΓ hΓ' W hA),
      ihb hΓA hΓA' W.cons hb (isProof_lift' hΓA hΓA' W.cons hb)]
    split <;> simp_all [ProofShape.lift']
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (Params.env.IsType univs) := ⟨hΓ', u, hA.weak' henv.ordered W⟩
    simp only [VExpr.lift'] at hp
    simp only [VExpr.lift', proofErase, hp,
      ihA hΓ hΓ' W hA (isProof_lift' hΓ hΓ' W hA),
      ihB hΓA hΓA' W.cons hB (isProof_lift' hΓA hΓA' W.cons hB)]
    split <;> simp_all [ProofShape.lift']

/-- Recursive erased comparison reflects through every thinning by its raw
substitution stability, before any original typing is used. -/
theorem ProofShape.Compare.of_lift'
    (H : ProofShape.Compare (ErasedComparedKStage D stage) mode (a.lift' ρ) (b.lift' ρ)) :
    ProofShape.Compare (ErasedComparedKStage D stage) mode a b :=
  ProofShape.relation_lift'_reflect
    (fun σ H => H.subst (σ := σ) (fun h => erased_compared_K_stage_subst stage h)) H

/-- The finite recursive comparison is invariant under arbitrary raw thinning,
with its stage and mode unchanged. -/
theorem ProofShape.Compare.lift'_iff :
    ProofShape.Compare (ErasedComparedKStage D stage) mode (a.lift' ρ) (b.lift' ρ) ↔
      ProofShape.Compare (ErasedComparedKStage D stage) mode a b :=
  ProofShape.relation_lift'_iff
    (fun σ H => H.subst (σ := σ) (fun h => erased_compared_K_stage_subst stage h))

/-- General context thinning reflects the concrete erased certificate at typed
endpoints in both modes. It needs no typed substitution into deleted binders. -/
theorem proofErase_compared_K_thinning (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.Compare (ErasedComparedKStage D stage) mode
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ))) :
    (env.IsDefEqU univs Γ A B → env.IsDefEqU univs Γ a b) ∧
    (mode = false → ¬ IsProof Γ a → env.IsDefEqU univs Γ a b) := by
  rw [proofErase_lift' hΓ hΓ' W ha, proofErase_lift' hΓ hΓ' W hb] at H
  exact proofErase_compare_reflect (erased_compared_K_stage_descent heq hs stage)
    hΓ ha hb H.of_lift'

end Lean4Lean.VEnv.Strengthening
