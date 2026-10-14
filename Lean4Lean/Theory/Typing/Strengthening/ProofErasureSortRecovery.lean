import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryExistence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction

/-! # The exact computational content of sort recovery

The sort clause of recovery is equivalent to exposing a universe from any
sort-typed original expression convertible to one. Necessity uses a variable
at that declaration, then retracts raw computation out of the fresh context.
No inhabitant of the declaration is required below.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_sort_inv ProofShape.liftN_sort_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]

namespace ProofShape
/-- Recovery of a variable can only compute from its oracle assignment. -/
theorem TypeRecovery.bvar_compute (R : TypeRecovery Step σ (.bvar i) T) :
    Compute Step (σ i) T := by
  generalize E : ProofShape.bvar i = e at R
  induction R with
  | bvar => cases E; exact .refl
  | convert _ H ih => exact (ih E).trans H
  | sort | const | lam | app | forallE | proj => cases E
end ProofShape

/-- The sort part of recovery completeness, isolated from Pi and family heads.
The input certificate may have any recovered output. -/
def ErasedSortRecovery (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e u out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e (.sort u) →
    ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ e) out →
    ∃ v, ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ e) (.sort v)

/-- Universe head exposure on original types. The output universe may differ
syntactically from the given one; typed replay determines their equivalence.
This remains unproved for the concrete computational stages. -/
def ErasedSortExposure (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ T u v}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ T (.sort u) →
    env.IsDefEqU univs Γ T (.sort v) →
    ∃ w, ProofShape.Compute Step (proofErase Γ T) (.sort w)

/-- Head exposure computes the recovered type to a sort. Recovery replay
provides the actual original type needed to apply the exposure premise. -/
theorem ErasedSortExposure.recovery (hstep : ErasedPrimitiveDescent Step)
    (H : ErasedSortExposure Step) : ErasedSortRecovery Step := by
  intro Γ e u out hΓ he R
  obtain ⟨T, heT, ET⟩ := proofErase_typeRecovery_replay hstep hΓ (erasedTypeOracle_valid hΓ) he R
  obtain ⟨_, hT⟩ := heT.isType henv hΓ
  obtain ⟨w, C⟩ := H hΓ hT (heT.uniqU henv hΓ he)
  exact ⟨w, R.convert (ET ▸ C)⟩

/-- A fresh variable tests universe exposure of its declaration. The raw
substitution retraction removes that variable without supplying an inhabitant
below. Only substitution closure of primitive computation is needed here. -/
theorem ErasedSortRecovery.exposure
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : ErasedSortRecovery Step) : ErasedSortExposure Step := by
  intro Γ T u v hΓ hT HT
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hx : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
  have hxv : env.HasType univs (T :: Γ) (.bvar 0) (.sort v) :=
    ((HT.of_l henv hΓ hT).weak henv).defeq hx
  have Ex : proofErase (T :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_of_sort hΓT hxv)
  have R : ProofShape.TypeRecovery Step (erasedTypeOracle (T :: Γ))
      (proofErase (T :: Γ) (.bvar 0)) ((proofErase Γ T).liftN 1) := by
    rw [Ex]
    exact .bvar
  obtain ⟨w, R⟩ := H hΓT hxv R
  rw [Ex] at R
  have C : ProofShape.Compute Step ((proofErase Γ T).liftN 1) (.sort w) := R.bvar_compute
  exact ⟨w, ProofShape.relation_liftN_reflect (fun _ R => R.subst hsubst) C⟩

/-- Under checked descent and raw substitution, the sort recovery clause is
exactly universe head exposure. It is not an independent structural synthesis
lemma and is not asserted to be a sufficient strengthening front. -/
theorem erasedSortRecovery_iff_exposure (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ)) :
    ErasedSortRecovery Step ↔ ErasedSortExposure Step :=
  ⟨ErasedSortRecovery.exposure hsubst, ErasedSortExposure.recovery hstep⟩

/-- Global recovery existence already requires universe exposure, even though
it permits any recovered result type. -/
theorem ErasedRecoveryExists.sort_exposure
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : ErasedRecoveryExists Step) : ErasedSortExposure Step :=
  ErasedSortRecovery.exposure hsubst H.heads.sort

/-- Universe exposure descends equations with a literal sort endpoint. The
computed universe may change syntactically, so uniqueness aligns it with the
original upper endpoint before reconstructing the lower equation. -/
theorem ErasedSortExposure.sort_descend (hstep : ErasedPrimitiveDescent Step)
    (H : ErasedSortExposure Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hT : env.HasType univs Γ T (.sort u))
    (HT : env.IsDefEqU univs Γ' (T.liftN n k) (.sort v)) :
    env.IsDefEqU univs Γ T (.sort v) := by
  have hTw := hT.weakN henv W
  obtain ⟨w, C⟩ := H hΓ' hTw HT
  rw [proofErase_liftN hΓ hΓ' W hT] at C
  obtain ⟨out, HE, Eout⟩ := proofErase_compute_typed_descend hstep hΓ hΓ' W hT C
  obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Eout)
  have HW : env.IsDefEqU univs Γ' (.sort w) (.sort v) :=
    (show env.IsDefEqU univs Γ' (.sort w) (T.liftN n k) from
      ⟨_, (HE.weakN henv W).symm⟩).trans henv hΓ' HT
  have hw := HE.hasType.2.sort_inv henv
  have hv := (HT.of_l henv hΓ' hTw).hasType.2.sort_inv henv
  exact (show env.IsDefEqU univs Γ T (.sort w) from ⟨_, HE⟩).trans henv hΓ
    ⟨_, IsDefEq.sortDF hw hv (HW.sort_inv henv hΓ')⟩

/-- Any-output recovery completeness implies the literal-sort strengthening
fragment when primitive computation descends and substitutes. This conclusion
is strictly a fragment; no reduction of PropositionFront to it is asserted. -/
theorem ErasedRecoveryExists.sort_descend (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Step a b → Step (a.subst σ) (b.subst σ))
    (H : ErasedRecoveryExists Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hT : env.HasType univs Γ T (.sort u))
    (HT : env.IsDefEqU univs Γ' (T.liftN n k) (.sort v)) :
    env.IsDefEqU univs Γ T (.sort v) :=
  ErasedSortExposure.sort_descend hstep (ErasedRecoveryExists.sort_exposure hsubst H) hΓ hΓ' W hT HT

end Lean4Lean.VEnv.Strengthening
