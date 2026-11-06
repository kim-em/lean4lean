import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqProofSupply

/-! # Recover the proposition domain of an actual short Eq proof argument

Canonical Eq's literal telescope constructs native recovery directly. Actual
application typing aligns the supplied proof with that native domain. Thus
short typed proof supplies need no additional recovery certificate premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private piArity_inst_le from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaRoot
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem typed_native_spine_pi
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (HT : VExpr.WF env univs Γ (VExpr.mkApps f args)) (hlen : args.length < T.piArity)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) rawF (proofErase Γ T)) :
    ∃ A B, env.HasType univs Γ (VExpr.mkApps f args) (.forallE A B) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ)
        (ProofShape.mkApps rawF (args.map (proofErase Γ)))
        (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) := by
  induction args generalizing f T rawF with
  | nil =>
    cases T <;> simp only [VExpr.piArity, List.length_nil] at hlen
    all_goals try omega
    obtain ⟨u, hPi⟩ := hf.isType henv hΓ
    refine ⟨_, _, hf, ?_⟩
    simpa only [List.map_nil, ProofShape.mkApps, List.foldl_nil,
      proofErase, if_neg (not_isProof_of_sort hΓ hPi)] using RN
  | cons x xs ih =>
    cases T <;> simp only [VExpr.piArity, List.length_cons] at hlen
    all_goals try omega
    rename_i A B
    have happ : VExpr.WF env univs Γ (.app f x) := VExpr.WF.of_mkApps henv hΓ HT
    obtain ⟨_, _, hf', hx⟩ := happ.app_inv henv hΓ
    have hxA := argument_at_displayed_domain hΓ hf' hf hx
    obtain ⟨u, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hPi.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    have RNpi : ScopedTypeRecovery Step (proofEraseCtx Γ) rawF
        (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) := by
      simpa only [proofErase, if_neg (not_isProof_of_sort hΓ hPi)] using RN
    have RNapp := RNpi.app (a := proofErase Γ x)
    rw [← proofErase_instN hΓA hxA Ctx.InstN.zero hB] at RNapp
    exact ih (hf.app hxA) HT (by have := piArity_inst_le B x 0; omega) RNapp

/-- A short typed canonical Eq prefix has exact native Pi recovery at any
primitive relation. This uses only literal telescope supply, with no recovery
completeness or type-computation hypothesis. -/
theorem eq_rec_short_prefix_native_pi
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (HT : VExpr.WF env univs Γ (VExpr.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length ≤ 5) :
    ∃ A B, env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec ls) args) (.forallE A B) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ)
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (proofErase Γ)))
        (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) := by
  obtain ⟨_, hc⟩ := VExpr.WF.of_mkApps henv hΓ HT
  obtain ⟨ci, hci, hw, hl⟩ := HasType.const_inv henv hΓ hc
  rw [heq.2.2.1] at hci
  cases Option.some.inj hci
  have hf := HasType.const (Γ := Γ) heq.2.2.1 hw hl
  have hf₀ := HasType.const (Γ := []) heq.2.2.1 hw hl
  obtain ⟨u, hT⟩ := hf₀.isType henv (by trivial)
  have RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const ``Eq.rec ls)
      (proofErase Γ (canonicalEqRecType.instL ls)) := by
    rw [proofErase_closed_context ((henv.ordered.closedC heq.2.2.1).instL) hT hΓ]
    exact .const heq.2.2.1 hw hl
  exact typed_native_spine_pi hΓ hf HT (by change args.length < 6; omega) RN

/-- An actual proof argument on a short Eq spine derives the recovered
proposition domain needed for proof supply. The proof's own proposition is
aligned with the native telescope domain by ordinary type uniqueness. -/
theorem typed_eq_proof_argument_recovery
    (heq : env.HasCanonicalEq)
    (HT : TypedSource Δ (.app (ProofShape.mkApps (.const ``Eq.rec ls) args) .proof))
    (hlen : args.length ≤ 5) :
    ∃ A B, ScopedTypeRecovery Step Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE A B) ∧
      DomainSort Δ A .zero := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ef
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨A, B, hfPi, RN⟩ := eq_rec_short_prefix_native_pi (Step := Step) heq hΓ ⟨_, hf⟩
    (by simpa only [Eargs, List.length_map] using hlen)
  have hxA := argument_at_displayed_domain hΓ hf hfPi hx
  obtain ⟨P, hxP, hP⟩ := proofErase_eq_proof.1 Ex
  obtain ⟨_, HAP⟩ := hxA.uniqU henv hΓ hxP
  have hA := (HAP.symm.toU.of_l henv hΓ hP).hasType.2
  exact ⟨proofErase Γ A, proofErase (A :: Γ) B, by simpa only [Eargs] using RN,
    Γ, A, hΓ, rfl, hA, rfl⟩

/-- An actual typed proof application before saturation preserves completion
without a separately supplied native recovery or proposition-domain witness. -/
theorem EqTargetPrefixEmbedding.append_typed_proof
    {D : Definitions} (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HT : TypedSource Δ (.app (ProofShape.mkApps (.const ``Eq.rec ls) args) .proof))
    (hlen : args.length ≤ 5) :
    EqTargetPrefixEmbedding Γ v w original Δ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ [.proof])) := by
  obtain ⟨A, B, RN, SD⟩ := typed_eq_proof_argument_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq HT hlen
  exact HP.append_proof heq hs hΓ ht RN SD

/-- At any typed Eq application with at most six target slots, a failed
proof-supply derivation reaches an actual non-proof argument before saturation.
Missing native proposition recovery is impossible for a literal proof here. -/
theorem EqProofPrefixSupply.first_nonproof
    (heq : env.HasCanonicalEq) (hslots : slots ≤ 6)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ pending)))
    (H : ¬ EqProofPrefixSupply D Δ ls slots args pending) :
    ∃ supplied x rest, pending = supplied ++ x :: rest ∧
      EqProofPrefixSupply D Δ ls slots args supplied ∧
      (args ++ supplied).length < slots ∧ x ≠ .proof := by
  obtain ⟨supplied, x, rest, E, HS, hlen, Hgap⟩ := EqProofPrefixSupply.first_gap H
  refine ⟨supplied, x, rest, E, HS, hlen, ?_⟩
  intro Ex
  have HTapp : TypedSource Δ
      (.app (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ supplied)) x) := by
    rw [E, ← List.append_assoc, ProofShape.mkApps_append] at HT
    exact typed_spine_head HT
  rw [Ex] at HTapp
  obtain ⟨A, B, RN, SD⟩ := typed_eq_proof_argument_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq HTapp (by omega)
  exact Hgap ⟨Ex, 0, A, B, RN, SD⟩

/-- The first non-proof supply gap retains completion of the exact prefix
preceding that argument. Actual whole-spine typing removes the former missing
proposition-recovery alternative from the certificate-level gap theorem. -/
theorem EqTargetPrefixEmbedding.first_typed_supply_gap
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hslots : original.length ≤ 6)
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ pending)))
    (H : ¬ EqProofPrefixSupply D Δ ls original.length args pending) :
    ∃ supplied x rest, pending = supplied ++ x :: rest ∧
      EqProofPrefixSupply D Δ ls original.length args supplied ∧
      EqTargetPrefixEmbedding Γ v w original Δ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ supplied)) ∧
      (args ++ supplied).length < original.length ∧ x ≠ .proof := by
  obtain ⟨supplied, x, rest, E, HS, hlen, Hnonproof⟩ :=
    EqProofPrefixSupply.first_nonproof heq hslots HT H
  exact ⟨supplied, x, rest, E, HS, HP.proof_supply heq hs hΓ ht HS, hlen, Hnonproof⟩

end Lean4Lean.VEnv.Strengthening
