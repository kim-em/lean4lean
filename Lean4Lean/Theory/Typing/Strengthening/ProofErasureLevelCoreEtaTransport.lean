import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFixedTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRawEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreBetaSquare

/-! # Typed eta comparison through the full level core

Fresh-argument reflection handles beta contraction across an eta body's
application boundary. Universe changes can first return to an ordinary reduct,
without returning to the original term. Neither eta endpoint must be fixed.
The definitions collection is arbitrary subject to soundness and level
compatibility, so the actual environment's quotient rules are included.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A typed level-core reduct computes back to some ordinary reduct of its
source. This only reverses structural universe variation; ordinary computation
is retained, so no returning-reference or normalization premise is needed. -/
theorem proofErase_level_core_ordinary_return
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ e) out) :
    ∃ mid, Compute (ErasedIotaPrimitive D) (proofErase Γ e) mid ∧
      Compute (ErasedLevelCore D) out mid := by
  obtain ⟨mid, RM, VM⟩ := proofErase_level_core_factor hs hl hcon R hΓ he rfl
  obtain ⟨m, HM, EM⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ he RM
  have V : StructuralVariant out (proofErase Γ m) := by rw [EM]; exact VM.symm
  refine ⟨mid, RM, ?_⟩
  simpa only [EM] using (proofErase_carrier_aligned_variant_level_compute V hΓ
    (HM.simAt hs hΓ _ he).hasType.2).mono (Step' := ErasedLevelCore D) (fun H => .inr H)

/-- Fresh application reflection for any sound ordinary core, including its
selected definition programs. Reflection retains either displayed eta or two
lambdas with one body; arbitrary annotation computation is allowed. -/
theorem proofErase_ordinary_fresh_application_raw
    (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : Compute (ErasedIotaPrimitive D)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) body) (X : ProofShape) :
    ∃ f', Compute (ErasedIotaPrimitive D) (proofErase Γ f) f' ∧
      EtaResidual (.lam X body) f' := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨out, R0, EO⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓA hopen (E.symm ▸ R)
  obtain ⟨f₀, RF, H⟩ := R0.fresh_application
  have HF := RF.simAt hs hΓ _ hf
  have hf₀ := HF.hasType.2
  have hn₀ := mt (isProof_congr hΓ HF).2 hn
  have RR := proofErase_pattern_compute_forward hs hcon hΓ hf RF
  refine ⟨proofErase Γ f₀, RR, ?_⟩
  rcases H with rfl | ⟨D₀, rfl⟩
  · have EB := EO.symm.trans (proofErase_eta_body hΓ hA hf₀ hn₀)
    rw [EB]
    classical
    unfold etaArgument
    split
    · exact .eta .proof
    · exact .eta .boundVar
  · obtain ⟨⟨v, hD⟩, _, hb⟩ := hf₀.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := ((HasType.lam hD hb).uniqU henv hΓ hf₀).forallE_inv henv hΓ
    have EB := proofErase_defeqCtx (Γ₁ := D₀ :: Γ) ⟨hΓ, _, hD⟩ (.succ .zero hDA) hb
    rw [show proofErase Γ (.lam D₀ out) =
      .lam (proofErase Γ D₀) (proofErase (D₀ :: Γ) out) from if_neg hn₀, EB, EO]
    exact .lam

/-- Eta residuals follow arbitrary short-endpoint level-core computation.
Lambda inversion replaces the computational-root hypothesis, which would
incorrectly exclude the core's sort and constant universe conversions. -/
theorem ProofShape.EtaResidual.level_compute_right
    (H : EtaResidual a b) (R : Compute (ErasedLevelCore D) b b') :
    ∃ a', Compute (ErasedLevelCore D) a a' ∧ EtaResidual a' b' := by
  have hweak {a b n k} (H : ErasedLevelCore D a b) :
      ErasedLevelCore D (a.liftN n k) (b.liftN n k) := by
    rcases H with H | H
    · exact .inl (erased_iota_primitive_liftN H)
    · cases H with
      | sort H hw => exact .inr (.sort H hw)
      | const H hw => exact .inr (.const H hw)
  cases H with
  | eta H =>
    cases H with
    | boundVar => exact ⟨_, .lam .refl (.app (R.liftN (fun H => hweak H)) .refl), .eta .boundVar⟩
    | proof => exact ⟨_, .lam .refl (.app (R.liftN (fun H => hweak H)) .refl), .eta .proof⟩
  | lam =>
    obtain ⟨D', body', rfl, _, RB⟩ := R.level_core_lam_inv
    exact ⟨_, .lam .refl RB, .lam⟩

/-- A canonical typed eta pair survives independent level-core computations,
including beta that consumes the opened application and arbitrary universe
changes. The comparison remains raw and in common mode. -/
theorem proofErase_level_core_eta_shape_forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (RL : Compute (ErasedLevelCore D)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) left)
    (RF : Compute (ErasedLevelCore D) (proofErase Γ f) right) :
    RawCheckedCompare (ErasedLevelCore D) true left right := by
  obtain ⟨X, body, rfl, _, RB⟩ := RL.level_core_lam_inv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  obtain ⟨_, _, hopen⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have E := proofErase_eta_body hΓ hA hf hn
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓA hopen (E.symm ▸ RB)
  obtain ⟨f', RR, Hη⟩ := proofErase_ordinary_fresh_application_raw hs hcon hΓ hA hf hn (E ▸ RM) X
  obtain ⟨common, RF', RR'⟩ := hc hΓ hf RF (RR.mono (fun H => .inl H))
  obtain ⟨left', RL', Hη'⟩ := Hη.level_compute_right RR'
  exact .compute ((ProofShape.Compute.lam .refl RT).trans RL') RF' Hη'.rawChecked

/-- Both displayed head-eta constructors at common original types transport
through the full level core. Typed classification supplies the correct erased
fresh argument, including proof-domain eta. No endpoint fixedness is assumed. -/
theorem proofErase_level_core_eta_head_forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (hf : env.HasType univs Γ f T)
    (H : EtaHead (proofErase Γ e) (proofErase Γ f))
    (RE : Compute (ErasedLevelCore D) (proofErase Γ e) left)
    (RF : Compute (ErasedLevelCore D) (proofErase Γ f) right) :
    RawCheckedCompare (ErasedLevelCore D) true left right := by
  obtain ⟨A, B, u, hA, hfPi, hn, E⟩ := proofErase_eta_head_classified hΓ he hf H
  exact proofErase_level_core_eta_shape_forward hs hl hcon hc hΓ hA hfPi hn (E ▸ RE) RF

end Lean4Lean.VEnv.Strengthening
