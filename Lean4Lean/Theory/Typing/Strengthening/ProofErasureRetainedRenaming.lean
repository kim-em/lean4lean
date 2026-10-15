import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointWeakening
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # Renaming only variables retained by typed proof erasure

Proof variables need no exact recovery image: typed erasure removes them.
The remaining variables still rename with their exact oracle assignments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
namespace ProofShape

/-- Interpreted substitution that renames exactly every retained variable of
any typed realization. Erased proof variables impose no lookup requirement. -/
structure RetainedRenaming (Δ Δ' : List ProofShape) (τ : Subst) : Prop where
  interpretation : ContextSubstitution Δ Δ' τ
  lookup : ∀ {Γ i A}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ∃ j, τ i = .bvar j ∧ contextOracle Δ' j = (contextOracle Δ i).subst τ

/-- Exact context renaming satisfies the retained-variable condition. -/
theorem ContextRenaming.retained (W : ContextRenaming Δ Δ' τ) : RetainedRenaming Δ Δ' τ :=
  ⟨W.interpretation, fun _ _ _ _ => W.lookup _⟩

/-- Retained-variable transport extends under every displayed domain. -/
theorem RetainedRenaming.cons (W : RetainedRenaming Δ Δ' τ) :
    RetainedRenaming (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  refine ⟨ContextSubstitution.cons W.interpretation, ?_⟩
  intro Γ i T hΓ EΓ hl hn
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    cases hl with
    | zero =>
      refine ⟨0, rfl, ?_⟩
      simp only [contextOracle, TypeOracle.cons, lift_subst_lift]
    | @succ _ i T _ hl =>
      have hn₀ : ¬ IsProof Γ (.bvar i) :=
        fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
      obtain ⟨j, Ej, ET⟩ := W.lookup hΓ.1 EΓ hl hn₀
      refine ⟨j+1, ?_, ?_⟩
      · simp [Subst.lift, Ej, ProofShape.liftN, liftVar, Nat.add_comm]
      · simp only [contextOracle, TypeOracle.cons, lift_subst_lift] at ET ⊢
        exact congrArg (·.liftN 1) ET

/-- Sort witnesses transport along the underlying typed substitution. -/
theorem RetainedRenaming.sort (W : RetainedRenaming Δ Δ' τ) (S : DomainSort Δ A u) :
    DomainSort Δ' (A.subst τ) u := ContextSubstitution.sort W.interpretation S

/-- It suffices to check retained lookup transport in one typed source context;
equal context erasures convert every other realization to it. -/
theorem RetainedRenaming.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
      ∃ j, τ i = .bvar j ∧ contextOracle (proofEraseCtx Γ₀) j =
        (contextOracle (proofEraseCtx Γ) i).subst τ) :
    RetainedRenaming (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  refine ⟨ContextSubstitution.of_typed hΓ₀ W E, ?_⟩
  intro Γ' i A hΓ' EΓ hl hn
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  exact H hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- Instantiating a proposition-valued binder satisfies retained renaming.
The proof itself may be arbitrary; every retained older variable keeps its
exact oracle assignment after deleting the binder. -/
theorem RetainedRenaming.proof_inst
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) :
    RetainedRenaming (proofEraseCtx (P :: Γ)) (proofEraseCtx Γ) (Subst.one .proof) := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := P)).substEq hΓP hp
  have E : ErasedSubstAgreement (P :: Γ) Γ (VExpr.Subst.one p)
      (Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓP hp
  rw [proofErase_eq_proof.2 ⟨P, hp, hP⟩] at E
  refine RetainedRenaming.of_typed hΓ W E ?_
  intro i A hl hn
  cases hl with
  | zero => exact (hn ⟨P.lift, .bvar .zero, hP.weak henv⟩).elim
  | @succ _ i A _ hl =>
    refine ⟨i, rfl, ?_⟩
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id]

/-- Source-typed primitives may transport under retained renaming. A primitive
may be simulated by a finite computation in the target relation. -/
def RetainedPrimitiveTransport
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Δ Δ' τ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    proofEraseCtx Γ = Δ → RetainedRenaming Δ Δ' τ →
    Step Δ (proofErase Γ e) out → ScopedCompute Target Δ' ((proofErase Γ e).subst τ) (out.subst τ)

/-- Typed compatible paths transport using primitive simulation only at
realized sources; forward replay supplies all intermediate source typings. -/
theorem ScopedCompute.rename_retained
    (hstep : ErasedScopedPrimitiveDescent Step) (htrans : RetainedPrimitiveTransport Step Target)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : RetainedRenaming Δ Δ' τ) : ScopedCompute Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | base H =>
    subst Ee
    exact htrans hΓ ht EΓ W H
  | beta H => exact .beta H.subst
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact .trans (ih₁ hΓ ht EΓ Ee W) (ih₂ hΓ HE.hasType.2 EΓ EE W)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W) (iha hΓ ha EΓ Ea W)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ hA EΓ EA W)
      (ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) Eb W.cons)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB W.cons)

/-- Exact recovery transport requires variable images only at retained typed
occurrences. This covers deletion of proof binders without recovering a marker. -/
theorem ScopedTypeRecovery.rename_retained
    (hstep : ErasedScopedPrimitiveDescent Step) (htrans : RetainedPrimitiveTransport Step Target)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : RetainedRenaming Δ Δ' τ) : ScopedTypeRecovery Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    have hn : ¬ IsProof Γ (.bvar i) := by intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    obtain ⟨j, Ej, ET⟩ := W.lookup hΓ EΓ hl hn
    simp only [ProofShape.subst, Ej, ← ET]
    exact .bvar
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) Eb W.cons)
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    rw [subst_inst]
    exact .app (ih hΓ hf EΓ Ef W)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB W.cons)
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    have HR' := ih hΓ hm.hasType.2 EΓ Em W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR'
    rw [projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR'
  | convert R RC ih =>
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    exact .convert (ih hΓ ht EΓ Ee W) (RC.rename_retained hstep htrans hΓ hA EΓ EA W)

end ProofShape
end Lean4Lean.VEnv.Strengthening
