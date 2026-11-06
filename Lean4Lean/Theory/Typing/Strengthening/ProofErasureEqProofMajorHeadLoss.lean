import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadCompletionHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSingletonBinderReadout

/-! # Head loss after eta introduces the Eq proof major

The fresh proof binder need not have a lower inhabitant. Singleton readout
removes it by certificate descent. At a losing root in the computed body
spine, only structure eta remains after the original equation is read out.
This does not assert that arbitrary later wrapper histories retain the same
component presentation, or that structure eta is impossible there.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private typed_const_levels_wf
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqEtaSingleton
variable [Params]

/-- Read either singleton after a full completed prefix opens its proof
binder and its body components compute. The existing completion's actual
realization supplies both binder descents; no target proof is introduced. -/
theorem EqHeadCompletion.read_singletons_after_full_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u)
    (HL : List.Forall₂ (· ≈ ·) ls rootLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: Ξ))
      (args.map (·.liftN 1) ++ [etaArgument u]) (rootArgs ++ pending))
    (HT : TypedSource (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs))
    (HG : CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target ∨
      ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
        (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨Γ, Γ', count, offset, v₀, w₀, pre, F, hΓ, hΓ', W, rfl, hf, hn, HP, E⟩ := H
  have Ehead := E
  rw [proofErase_const_spine hΓ hf hn, ProofShape.liftN_mkApps, ProofShape.liftN] at Ehead
  obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj Ehead
  have hfive : pre.length = 5 := by simpa only [List.length_map] using hlen
  obtain ⟨α', a', M', minor', b', rfl⟩ :
      ∃ α' a' M' minor' b', pre = [α',a',M',minor',b'] := by
    cases pre with | nil => simp at hfive | cons x xs =>
    cases xs with | nil => simp at hfive | cons y ys =>
    cases ys with | nil => simp at hfive | cons z zs =>
    cases zs with | nil => simp at hfive | cons q qs =>
    cases qs with | nil => simp at hfive | cons r rs =>
    cases rs with
    | nil => exact ⟨_, _, _, _, _, rfl⟩
    | cons s ss => simp at hfive
  obtain ⟨v₁, w₁, rfl⟩ : ∃ v₁ w₁, rootLs = [v₁,w₁] := by
    cases HL with | cons _ HL => cases HL with | cons _ HL => cases HL; exact ⟨_, _, rfl⟩
  obtain ⟨hv, hw, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have HW : ∀ l ∈ [v₀,w₀], l.WF univs := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hv
    · exact hw
  have HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v₀,w₀]) (.const ``Eq.rec [v₁,w₁]) :=
    ⟨_, .constDF heq.2.2.1 HW (typed_const_levels_wf HT) (by rfl) HL⟩
  exact HP.read_singletons_after_eta heq hs hΓ hΓ' W hΔ ht hf hn HC (E.symm ▸ RN) SD HA HG

/-- A head-losing root in a computed proof-major eta body either reads the
original equation or is native structure eta. Literal proof blocks core iota;
completion and binder descent read both singleton forms. All administrative
expansions, including function eta, preserve the head and are excluded. The
remaining structure witness is at the full six-argument root, with no pending
arguments, and uses the root's finite stage and exact source. -/
theorem EqHeadCompletion.read_proof_major_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqHeadCompletion Δ v w [α,a,M,minor,b] Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : args.length = 5)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) (.forallE rawA rawB))
    (SD : DomainSort Ξ rawA u)
    (HL : List.Forall₂ (· ≈ ·) ls rootLs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D bodyStage) (rawA :: Ξ))
      (args.map (·.liftN 1) ++ [etaArgument u]) (rootArgs ++ pending))
    (HT : TypedSource (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs))
    (HR : PiInertStage D rootStage (rawA :: Ξ)
      (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target) :
    env.IsDefEq univs Δ a b α ∨
      rootArgs.length = 6 ∧ pending = [] ∧
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D rootStage)
        (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target := by
  classical
  have HS := (WrappedConstHead.const (c := ``Eq.rec) (ls := rootLs)).mkApps rootArgs
  obtain ⟨Hlevel, Hconst, Hidentity, Heta⟩ := HS.loss_exclusions (Δ := rawA :: Ξ) HN
  by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D rootStage)
      (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target
  · exact .inl (H.read_singletons_after_full_eta heq hs hΔ ht hlen RN SD HL HA HT (.inr HQ))
  have Hcore : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target := by
    rintro (HC | HL)
    · have Eproof := H.full_eta_argument heq
        (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) hlen RN SD
      obtain ⟨rα, ra, rM, rm, rb, rfl⟩ : ∃ rα ra rM rm rb, args = [rα,ra,rM,rm,rb] := by
        cases args with | nil => simp at hlen | cons x xs =>
        cases xs with | nil => simp at hlen | cons y ys =>
        cases ys with | nil => simp at hlen | cons z zs =>
        cases zs with | nil => simp at hlen | cons q qs =>
        cases qs with | nil => simp at hlen | cons r rs =>
        cases rs with
        | nil => exact ⟨_, _, _, _, _, rfl⟩
        | cons s ss => simp at hlen
      exact pi_inert_eq_prefix_no_core_root hreg hoff hRec
        (by simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, Eproof] using HA) HC
    · exact Hlevel HL
  by_cases Hstruct : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D rootStage)
      (rawA :: Ξ) (ProofShape.mkApps (.const ``Eq.rec rootLs) rootArgs) target
  · have Hlong : ¬ rootArgs.length ≤ 5 := fun hshort =>
      typed_eq_short_prefix_no_structure heq
        (erased_static_structure_eta_expansion_stage_descent heq hs rootStage) HT hshort Hstruct
    have Htotal := HA.length_eq
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, hlen] at Htotal
    exact .inr ⟨by omega, List.eq_nil_of_length_eq_zero (by omega), Hstruct⟩
  rcases static_other_spine_root HR.1 Hcore HQ Hstruct with HC | ⟨k, hk, HG | HI | HE⟩
  · exact (Hconst HC).elim
  · exact .inl (H.read_singletons_after_full_eta heq hs hΔ ht hlen RN SD HL HA HT
      (.inl (HG.mono (erased_static_structure_eta_expansion_stage_mono (Nat.le_of_lt hk)))))
  · exact (Hidentity _ HI).elim
  · exact (Heta _ HE).elim

end Lean4Lean.VEnv.Strengthening
