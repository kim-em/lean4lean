import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqFamilyGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierPropositions

/-! # Specialized Eq guards are general singleton family guards

The carrier certificate compares the literal reconstructed and requested Eq
families. Weakening under the fresh proof major gives the actual generated
family guard. No arbitrary carrier decoder or substitution assumption is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A typed joint carrier certificate supplies exactly the family comparison
of the canonical generated Eq prefix, including its fresh proof-major context. -/
theorem proofErase_joint_eq_family_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : w.WF univs)
    (hα : env.HasType univs Γ α (.sort w)) (ha : env.HasType univs Γ a α)
    (hb : env.HasType univs Γ b α)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec)
    (hz : data.sourceLevel [v,w] ≈ .zero)
    (hS : data.singletonLayout env [v,w] = some S) (hE : data.propElim [v,w] = some E)
    (H : JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      Γ data [v,w] [α,a,M,m,b] (canonicalEqPrefixProgram v w α a M m b reconstructed) S E := by
  apply (eqRec_family_guard_iff heq hr hn hz hS hE).2
  have hP := HasType.eqApp heq hw hα ha ha
  have hQ := HasType.eqApp heq hw hα ha hb
  have hΓQ : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have HP := proofErase_joint_carrier_propositions (mode := true) heq hw hΓ hα ha ha hb H
  have HL := HP.rename (erased_joint_union_rename heq hs)
    (ContextRenaming.of_liftN hΓ hΓQ Ctx.LiftN.one)
  change JointCompare (ErasedJointUnion D) (proofEraseCtx (eqApp w α a b :: Γ)) true
    (proofErase (eqApp w α a b :: Γ) (eqApp w α a a).lift)
    (proofErase (eqApp w α a b :: Γ) (eqApp w α a b).lift)
  rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hP, proofErase_liftN hΓ hΓQ Ctx.LiftN.one hQ]
  simpa only [subst_bvar_liftN, JointCheckKind.subst] using HL

private theorem eq_general
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hnp : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (H : JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    JointSingletonPrimitive (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  obtain ⟨hv, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hz := hr.eqRec_source_zero henv heq hn hΓ ⟨_, ht⟩
  have hl := hr.eqRec_large heq hn
  obtain ⟨_, _, _, hrest, hseq⟩ := hr.eqRec_singleton_equation heq hn hz
  obtain ⟨i, ho, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hpat := hr.patEquation_of_empty henv hrest hgen
  have hlevels : ∀ l ∈ [v,w], l.WF univs := by simp_all
  have hlen : [v,w].length = data.uvars := by simp [(hr.eqRec_target heq hn).1]
  obtain ⟨S, E, hS, hE, _⟩ := RecursorData.propElim_wf henv hr hl hz hlevels hlen ⟨i, ho⟩
  have hg := eqRec_prefix_generated (U := univs) (α := α) (a := a) (M := M) (m := m) (b := b)
    heq hr hn hz hS hE
  have hab := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ ha hb H
  have HC := canonicalEqPrefixProgram_check henv heq hΓ hpat ⟨_, ht⟩ ⟨_, hab⟩
  have HG := proofErase_joint_eq_family_guard (M := M) (m := m)
    (reconstructed := eqReflApp w α.lift a.lift) heq hs hΓ hw hα ha hb hr hn hz hS hE H
  obtain ⟨recType, hrec⟩ := hr.recursorType_exists
  let args := [α,a,M,m,b]
  let program := canonicalEqPrefixProgram v w α a M m b (eqReflApp w α.lift a.lift)
  let C : SingletonPrefixCode := ⟨data, [v,w], args.length, recType,
    program.equation, program.equationBody, S, E⟩
  obtain ⟨_, _, _, _, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  have V : C.Valid := ⟨hn ▸ hregistry.trans hlookup, hr, hl, hz, hlevels, hrec,
    heqn, hbody, hS, hE, args, program, rfl, hg⟩
  have HC : UnfoldingCheck env univs Γ (mkApps (.const data.name [v,w]) args) program := by
    simpa only [hn, args, program, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using HC
  have hnp : ¬ IsProof Γ (mkApps (.const data.name [v,w]) args) := by simpa only [hn, args, Strengthening.eqRecBeforeMajor, VExpr.mkApps, List.foldl] using hnp
  have HE := proofErase_const_spine hΓ HC.source_typed hnp
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const data.name [v,w]) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, HC.source_typed, HE⟩
  change JointSingletonPrimitive (ErasedJointUnion D) (proofEraseCtx Γ)
    (proofErase Γ (mkApps (.const ``Eq.rec [v,w]) args)) (proofErase Γ program.rhs)
  rw [← hn, HE, V.output_eq heq hΓ hg HC hnp]
  exact ⟨HT, .intro V (by simp only [List.length_map, C])
    (V.telescope_eq hΓ hg ⟨_, HC.source_typed⟩) ((V.guardWith_iff heq hΓ hg ⟨_, HC.source_typed⟩).2 HG)⟩

/-- At every actual typed source, a specialized carrier-guarded Eq primitive
is already a general singleton primitive with a joint proposition guard. Both
raw endpoints are retained literally. This uses registry agreement, but no
beta stability, arbitrary carrier decoding, or substitution hypothesis. -/
theorem proofErase_joint_prefix_as_general
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : JointPrefixPrimitive (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    JointSingletonPrimitive (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro α a b v w M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Hα, ← Ha, ← Hb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab : env.IsDefEqU univs Γ a₀ b₀ :=
      ⟨_, proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ ha hb HC⟩
    have HH := eqRecBeforeMajor_simAt henv heq hΓ hab T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at hsrc
      cases hsrc
    have HG := eq_general heq hs hregistry hΓ ht hn HC
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀))
        (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, Hα, Ha, Hb, Hm] at HG
    simpa only [hsrc] using HG

end Lean4Lean.VEnv.Strengthening
