import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeRecovery

/-! # Existence of a recovered type for retained syntax

Exact recovery at a preselected type is false. Existence asks for any recovered
output, and is characterized here by three local head clauses. Unlike recovery
on original syntax, erased Pi formation must recover sorts for its two parts.
The clauses remain unproved for the finite compared-K stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

namespace ProofShape
/-- A recovered application contains a recovered Pi for its retained function,
even when its result has undergone further computation. -/
theorem TypeRecovery.app_inv (R : TypeRecovery Step σ (.app f a) T) :
    ∃ A B, TypeRecovery Step σ f (.forallE A B) := by
  generalize he : ProofShape.app f a = e at R
  induction R with
  | app R => cases he; exact ⟨_, _, R⟩
  | convert _ _ ih => exact ih he
  | bvar | sort | const | lam | forallE | proj => cases he

/-- Pi recovery retains sort recovery for the displayed domain. This remains
visible through every trailing conversion of the Pi's recovered type. -/
theorem TypeRecovery.forallE_domain_inv (R : TypeRecovery Step σ (.forallE A B) T) :
    ∃ u, TypeRecovery Step σ A (.sort u) := by
  generalize he : ProofShape.forallE A B = e at R
  induction R with
  | forallE RA _ => cases he; exact ⟨_, RA⟩
  | convert _ _ ih => exact ih he
  | bvar | sort | const | lam | app | proj => cases he

/-- Projection recovery contains a family recovery for its major. The field
recipe is irrelevant to this head obligation. -/
theorem TypeRecovery.proj_family_inv (R : TypeRecovery Step σ (.proj s j m) T) :
    ∃ ls args, TypeRecovery Step σ m (mkApps (.const s ls) args) := by
  generalize he : ProofShape.proj s j m = e at R
  induction R with
  | proj _ _ _ _ R => cases he; exact ⟨_, _, R⟩
  | convert _ _ ih => exact ih he
  | bvar | sort | const | lam | app | forallE => cases he
end ProofShape

/-- Every typed non-proof source has some recovered erased type. No output is
prescribed, and standalone proof markers need no recovery certificate. -/
def ErasedRecoveryExists (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e T}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    ¬ IsProof Γ e → ∃ out,
      ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ e) out

/-- Local head obligations for re-synthesis. The input certificate only assures
that the immediate subterm is already recoverable; a different output may be
selected. These clauses are unproved for the finite compared-K stages. -/
structure ErasedRecoveryHeads (Step : ProofShape → ProofShape → Prop) : Prop where
  sort : ∀ {Γ e u out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e (.sort u) →
    ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ e) out →
    ∃ v, ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ e) (.sort v)
  app : ∀ {Γ f a T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ (.app f a) T →
    ¬ IsProof Γ (.app f a) →
    ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ f) out →
    ∃ A B, ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ f) (.forallE A B)
  proj : ∀ {Γ s j m T out}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ (.proj s j m) T → ¬ IsProof Γ (.proj s j m) →
    ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ m) out →
    ∃ ls args, ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const s ls) args)

/-- The three head clauses synthesize every retained constructor. Projection
replay recovers the actual original family before deriving its field recipe. -/
theorem ErasedRecoveryHeads.exists (hstep : ErasedPrimitiveDescent Step)
    (H : ErasedRecoveryHeads Step) : ErasedRecoveryExists Step := by
  intro Γ e T hΓ ht hn
  induction e generalizing Γ T with
  | bvar i =>
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
    exact ⟨_, .bvar⟩
  | sort u =>
    rw [show proofErase Γ (.sort u) = .sort u from if_neg hn]
    exact ⟨_, .sort (HasType.sort_inv henv.ordered ht)⟩
  | const c ls =>
    obtain ⟨ci, hc, hls, hlen⟩ := HasType.const_inv henv hΓ ht
    rw [show proofErase Γ (.const c ls) = .const c ls from if_neg hn]
    exact ⟨_, .const hc hls hlen⟩
  | lam A b _ ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨B, R⟩ := ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (fun hp => hn (hp.lam hΓ hA))
    rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hn]
    exact ⟨_, .lam R⟩
  | app f a ihf _ =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨_, R⟩ := ihf hΓ hf (not_isProof_fn hΓ hf ha hn)
    obtain ⟨A, B, R⟩ := H.app hΓ ht hn R
    rw [show proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a)
      from if_neg hn]
    exact ⟨_, .app R⟩
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨_, RA⟩ := ihA hΓ hA (not_isProof_of_sort hΓ hA)
    obtain ⟨_, RB⟩ := ihB hΓA hB (not_isProof_of_sort hΓA hB)
    obtain ⟨u', RA⟩ := H.sort hΓ hA RA
    obtain ⟨v', RB⟩ := H.sort hΓA hB RB
    rw [show proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from if_neg hn]
    exact ⟨_, .forallE RA RB⟩
  | proj s j m ihm =>
    obtain ⟨info, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, R⟩ := ihm hΓ hm.hasType.2 (not_isProof_major hΓ ht hn)
    obtain ⟨ls, args, R⟩ := H.proj hΓ ht hn R
    obtain ⟨F, hmF, EF⟩ := proofErase_typeRecovery_replay hstep hΓ (erasedTypeOracle_valid hΓ)
      hm.hasType.2 R
    obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EF
    obtain ⟨F, _, RF⟩ := proofErase_projection_recovery_from_family hΓ hi ht hn hmF
      (by rw [EF]; exact R)
    exact ⟨_, RF⟩

/-- Existence already forces all three clauses. Sort recovery is tested by a
Pi whose domain is the source; this Pi is always retained. -/
theorem ErasedRecoveryExists.heads (H : ErasedRecoveryExists Step) :
    ErasedRecoveryHeads Step where
  sort hΓ he _ := by
    have hPi := HasType.forallE he (HasType.sort (l := VLevel.zero) (Γ := _ :: _) (by trivial))
    obtain ⟨_, R⟩ := H hΓ hPi (not_isProof_of_sort hΓ hPi)
    rw [show proofErase _ (.forallE _ (.sort .zero)) =
      .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)] at R
    exact R.forallE_domain_inv
  app hΓ ht hn _ := by
    obtain ⟨_, R⟩ := H hΓ ht hn
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg hn] at R
    exact R.app_inv
  proj hΓ ht hn _ := by
    obtain ⟨_, R⟩ := H hΓ ht hn
    rw [show proofErase _ (.proj _ _ _) = .proj _ _ _ from if_neg hn] at R
    exact R.proj_family_inv

/-- For any primitive computation with checked typed replay, the local clauses
are exactly recovery existence, not recovery at every convertible chosen type. -/
theorem erasedRecoveryExists_iff_heads (hstep : ErasedPrimitiveDescent Step) :
    ErasedRecoveryExists Step ↔ ErasedRecoveryHeads Step :=
  ⟨ErasedRecoveryExists.heads, ErasedRecoveryHeads.exists hstep⟩

/-- Existence re-synthesizes after any ordinary typed binder substitution. The
new output need only be convertible to the substituted old recovered type. -/
theorem erasedRecovery_resynthesize_instN (hstep : ErasedPrimitiveDescent Step)
    (H : ErasedRecoveryExists Step) (hΓ₁ : OnCtx Γ₁ (env.IsType univs))
    (hx : env.HasType univs Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : env.HasType univs Γ₁ e T) (hn : ¬ IsProof Γ₁ e)
    (R : ProofShape.TypeRecovery Step (erasedTypeOracle Γ₁) (proofErase Γ₁ e) out) :
    ∃ A A', env.HasType univs Γ₁ e A ∧ proofErase Γ₁ A = out ∧
      ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ (e.inst x k))
        (proofErase Γ A') ∧ env.IsDefEqU univs Γ (A.inst x k) A' := by
  obtain ⟨A, heA, EA⟩ := proofErase_typeRecovery_replay hstep hΓ₁
    (erasedTypeOracle_valid hΓ₁) ht R
  have hΓ := (W.wf henv hx hΓ₁).2
  have he' := heA.instN henv W hx
  have hn' := mt (isProof_instN hΓ₁ hx W heA).1 hn
  obtain ⟨_, R'⟩ := H hΓ he' hn'
  obtain ⟨A', heA', EA'⟩ := proofErase_typeRecovery_replay hstep hΓ
    (erasedTypeOracle_valid hΓ) he' R'
  exact ⟨A, A', heA, EA, EA' ▸ R', he'.uniqU henv hΓ heA'⟩

end Lean4Lean.VEnv.Strengthening
