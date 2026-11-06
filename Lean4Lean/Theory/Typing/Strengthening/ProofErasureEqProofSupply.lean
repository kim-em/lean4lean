import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqUnusedEmbedding

/-! # Fill target-prefix slots with certified proof arguments

A native recovered proposition domain permits eta opening with a proof marker.
Reinsert that same domain backwards to remove the fresh binder while keeping
the target completion. No inhabitant or argument-image equality is requested.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Supplying a proof marker at an actually recovered proposition domain
preserves the bounded target completion, even when that prefix is underfilled.
Eta chooses the target proof; its erasure is already independent of the fresh
binder, so constructed reverse insertion discharges that binder exactly. -/
theorem EqTargetPrefixEmbedding.append_proof
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B))
    (SD : DomainSort Δ A .zero) :
    EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ [.proof])) := by
  have HE := H.eta heq hs hΓ ht RN SD
  have Eproof : etaArgument .zero = .proof := by
    unfold etaArgument
    exact if_pos rfl
  rw [Eproof] at HE
  have WK : ContextEmbedding Δ (A :: Δ) (fun i => .bvar (liftVar 1 i 0)) :=
    ContextEmbedding.insert .identity SD
  have HR : EqTargetPrefixEmbedding Γ v w original (A :: Δ)
      ((ProofShape.mkApps (.const ``Eq.rec ls) (args ++ [.proof])).subst
        (fun i => .bvar (liftVar 1 i 0))) := by
    simpa only [subst_bvar_liftN, ProofShape.mkApps_append, ProofShape.mkApps,
      List.foldl_cons, List.foldl_nil, ProofShape.liftN] using HE
  exact HR.pullback WK

/-- A concrete supply derivation: stop when the target prefix is full, stop
at an empty supply, or consume a literal proof marker using its recovered
proposition domain. Every certificate lives in the actual outgoing context.
This predicate contains no completion or semantic agreement hypothesis. -/
inductive EqProofPrefixSupply (D : Definitions) (Δ : List ProofShape)
    (ls : List VLevel) (slots : Nat) : List ProofShape → List ProofShape → Prop where
  | nil : EqProofPrefixSupply D Δ ls slots args []
  | saturated : slots ≤ args.length → EqProofPrefixSupply D Δ ls slots args pending
  | proof : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B) →
      DomainSort Δ A .zero →
      EqProofPrefixSupply D Δ ls slots (args ++ [.proof]) pending →
      EqProofPrefixSupply D Δ ls slots args (.proof :: pending)

/-- Every certified proof-supply chain preserves completion for the full
actual application. Once the target vector is full, all remaining arguments
are unrestricted, including non-proof values. -/
theorem EqTargetPrefixEmbedding.proof_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (H : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HS : EqProofPrefixSupply D Δ ls original.length args pending) :
    EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ pending)) := by
  induction HS with
  | nil => simpa only [List.append_nil] using H
  | saturated hlen => exact H.append_saturated hlen _
  | proof RN SD _ ih =>
    simpa only [List.append_assoc, List.singleton_append] using ih (H.append_proof heq hs hΓ ht RN SD)

/-- Failure of the concrete supply derivation implies a genuinely underfilled
prefix and nonempty actual pending vector. This is not a claim that arbitrary
proof markers have recovery certificates. -/
theorem EqProofPrefixSupply.failure_shape
    (H : ¬ EqProofPrefixSupply D Δ ls slots args pending) :
    args.length < slots ∧ pending ≠ [] := by
  constructor
  · by_contra h
    exact H (.saturated (by omega))
  · rintro rfl
    exact H .nil

/-- If the supply cannot be traversed, select its first unsupported argument.
All earlier pending arguments have a concrete proof-supply derivation, the
new prefix is still underfilled, and the selected argument either is not a
proof marker or lacks a recovered proposition domain. -/
theorem EqProofPrefixSupply.first_gap
    (H : ¬ EqProofPrefixSupply D Δ ls slots args pending) :
    ∃ supplied x rest, pending = supplied ++ x :: rest ∧
      EqProofPrefixSupply D Δ ls slots args supplied ∧
      (args ++ supplied).length < slots ∧
      ¬ (x = .proof ∧ ∃ n A B,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ supplied)) (.forallE A B) ∧
        DomainSort Δ A .zero) := by
  classical
  induction pending generalizing args with
  | nil => exact (H .nil).elim
  | cons x rest ih =>
    by_cases HC : x = .proof ∧ ∃ n A B,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B) ∧ DomainSort Δ A .zero
    · obtain ⟨rfl, n, A, B, RN, SD⟩ := HC
      have HF : ¬ EqProofPrefixSupply D Δ ls slots (args ++ [.proof]) rest :=
        fun HS => H (.proof RN SD HS)
      obtain ⟨supplied, x, tail, E, HS, hlen, Hgap⟩ := ih HF
      refine ⟨.proof :: supplied, x, tail, ?_, .proof RN SD HS, ?_, ?_⟩
      · simp only [List.cons_append, E]
      · simpa only [List.append_assoc, List.singleton_append] using hlen
      · simpa only [List.append_assoc, List.singleton_append] using Hgap
    · exact ⟨[], x, rest, rfl, .nil,
        by simpa only [List.append_nil] using (EqProofPrefixSupply.failure_shape H).1,
        by simpa only [List.append_nil] using HC⟩

/-- The first unsupported supply argument is preceded by an actually completed
prefix in the same outgoing scope. The returned decomposition and missing
domain certificate are derived from the concrete supply failure. -/
theorem EqTargetPrefixEmbedding.first_proof_supply_gap
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (H : ¬ EqProofPrefixSupply D Δ ls original.length args pending) :
    ∃ supplied x rest, pending = supplied ++ x :: rest ∧
      EqTargetPrefixEmbedding Γ v w original Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ supplied)) ∧
      (args ++ supplied).length < original.length ∧
      ¬ (x = .proof ∧ ∃ n A B,
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ
          (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ supplied)) (.forallE A B) ∧
        DomainSort Δ A .zero) := by
  obtain ⟨supplied, x, rest, E, HS, hlen, Hgap⟩ := EqProofPrefixSupply.first_gap H
  exact ⟨supplied, x, rest, E, HP.proof_supply heq hs hΓ ht HS, hlen, Hgap⟩

end Lean4Lean.VEnv.Strengthening
