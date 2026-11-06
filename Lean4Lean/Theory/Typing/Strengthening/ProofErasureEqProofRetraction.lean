import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqConsumedArgument
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqUnusedConsumption

/-! # Lift head loss back across a consumed proof binder

Proof-valued variables have no retained occurrences in typed erasures.
Reverse renaming therefore restores the source exactly. The annotations
computed above the consumed binder are replayed before the reverse renaming.
No target assignment for unused ambient binders is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A proof endpoint admits a reverse variable renaming after replaying its
recorded annotation changes. The round trip fixes every retained variable
of the actual source context; the reverse map is identity or one insertion. -/
theorem ProofEndpointContext.retraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ProofEndpointContext D Ξ Ξ' τ)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Ξ) :
    ∃ Θ κ, PiInertContextHistory D Ξ Θ ∧ ContextRenaming Ξ' Θ κ ∧
      (∀ {i B}, Lookup Γ i B → ¬ IsProof Γ (.bvar i) → (τ i).subst κ = .bvar i) ∧
      (κ = ProofShape.Subst.id ∨ ∃ depth, κ = fun i => .bvar (liftVar 1 i depth)) := by
  induction H generalizing Γ with
  | identity =>
    exact ⟨_, ProofShape.Subst.id, .refl, ContextRenaming.identity,
      (fun _ _ => rfl), .inl rfl⟩
  | @inst Ξ rawA rawX SD _ =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      have SD' : DomainSort (proofEraseCtx Γ) rawA .zero := EΓ.symm ▸ SD
      obtain ⟨P, hP, EP⟩ := SD'.realize hΓ
      obtain ⟨_, HPA⟩ := (proofErase_reflect hΓ hP hA (EP.trans EA.symm)).2
        (not_isProof_of_sort hΓ hP)
      have hA₀ := ((HPA.defeq hΓ).of_l henv hΓ hP).hasType.2
      have W := ContextRenaming.of_liftN hΓ
        (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩) Ctx.LiftN.one
      refine ⟨rawA :: Ξ, (fun i => .bvar (liftVar 1 i 0)), .refl, ?_, ?_, .inr ⟨0, rfl⟩⟩
      · simpa only [proofEraseCtx, EA, EΓ] using W
      · intro i B hl hn
        cases i with
        | zero => exact (hn ⟨A.lift, .bvar .zero, hA₀.weak henv.ordered⟩).elim
        | succ i => simp [ProofShape.Subst.one, ProofShape.Subst.cons,
            ProofShape.Subst.id, ProofShape.subst, liftVar, Nat.add_comm]
  | @binder n Ξ rawA rawA' Ξ' τ RD H ih =>
    cases Γ with
    | nil => cases EΓ
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨Θ, κ, HH, WK, HK, EK⟩ := ih hΓ EΓ
      obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) hΓ hA EΓ EA RD
      have ER : (rawA'.subst τ).subst κ = rawA' := by
        rw [← EA', ProofShape.subst_subst]
        exact proofErase_subst_retained hΓ HA.hasType.2 HK
      have WK' := WK.cons (A := rawA'.subst τ)
      rw [ER] at WK'
      refine ⟨rawA' :: Θ, κ.lift, .step (.head RD) HH.tail, WK', ?_, ?_⟩
      · intro i B hl hn
        cases hl with
        | zero => rfl
        | succ hl =>
          have hn' : ¬ IsProof Γ (.bvar _) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
          simp only [ProofShape.Subst.lift, ProofShape.lift_subst_lift, HK hl hn']
          simp [ProofShape.liftN, liftVar, Nat.add_comm]
      · rcases EK with rfl | ⟨depth, rfl⟩
        · exact .inl ProofShape.Subst.id_lift
        · refine .inr ⟨depth+1, ?_⟩
          funext i
          cases i <;> simp [ProofShape.Subst.lift, ProofShape.liftN, liftVar, Nat.add_comm]
          split <;> omega

omit [Params] in
/-- Inserting a variable cannot create a wrapped constant occurrence. -/
theorem WrappedConstHead.of_liftN_one
    (H : WrappedConstHead c (e.liftN 1 depth)) : WrappedConstHead c e := by
  have HH := H.subst ((ProofShape.Subst.one .proof).liftN depth)
  simpa only [ProofShape.consume_unused_lift] using HH

/-- Bounded completion after an exact reverse renaming that is identity or
one binder insertion. This is a readout witness, not a claim of completion in
the current context. Closure through arbitrary later scope moves is open. -/
def EqTargetPrefixRetraction (Δ : List VExpr) (v w : VLevel) (original : List VExpr)
    (Ξ : List ProofShape) (source : ProofShape) : Prop :=
  ∃ Θ κ, ContextRenaming Ξ Θ κ ∧
    (κ = ProofShape.Subst.id ∨ ∃ depth, κ = fun i => .bvar (liftVar 1 i depth)) ∧
    EqTargetPrefixCompletion Δ v w original Θ (source.subst κ)

/-- The bounded prefix obtains a reverse-renaming completion after every
recorded proof endpoint. Its own typing suffices; additional source arguments
need neither target images nor a typing assumption in this construction. -/
theorem EqTargetPrefixCompletion.proof_endpoint_retraction
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqTargetPrefixCompletion Δ v w original Ξ source)
    (HC : ProofEndpointContext D Ξ Ξ' τ) :
    EqTargetPrefixRetraction Δ v w original Ξ' (source.subst τ) := by
  obtain ⟨ls, args, rfl, HP⟩ := HP
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef⟩ := HP.typed
  obtain ⟨Θ, κ, HH, WK, HK, EK⟩ := HC.retraction heq hs hΓ EΓ
  have ES : ((ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length)).subst τ).subst κ =
      ProofShape.mkApps (.const ``Eq.rec ls) (args.take original.length) := by
    rw [← Ef, ProofShape.subst_subst]
    exact proofErase_subst_retained hΓ hf HK
  refine ⟨Θ, κ, WK, EK, ls, (args.map (·.subst τ)).map (·.subst κ), ?_, ?_⟩
  · simp only [ProofShape.subst_mkApps, ProofShape.subst]
  · have HH := HP.context_history heq hs hΔ HH
    rw [← ES] at HH
    simpa only [ProofShape.subst_mkApps, ProofShape.subst, ← List.map_take] using HH

/-- An actual nonstructural head loss reads through the bounded reverse
renaming witness. The current typing bounds arity; renaming preserves the
primitive, and an insertion cannot create its missing wrapped Eq head. -/
theorem EqTargetPrefixRetraction.read_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixRetraction Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HT : TypedSource Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HR : PiInertStage D n Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) target) :
    env.IsDefEq univs Δ a b α := by
  have hlen := (typed_nonstructural_eq_head_loss_singleton heq hreg hoff hD HT HR HN Hstruct).1
  obtain ⟨Θ, κ, WK, EK, HP⟩ := HP
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP
  have hlen' : (args.map (·.subst κ)).length ≤ [α,a,M,minor,b].length := by
    simpa only [List.length_map, List.length_cons, List.length_nil] using hlen
  have HC : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Θ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst κ))) := by
    simpa only [List.take_of_length_le hlen'] using HP.prefix
  have HR' := pi_inert_stage_rename heq hs n HR WK
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR'
  apply HC.read_loss heq hs hreg hoff hD hΔ ht HR'
  intro Hhead
  rcases EK with rfl | ⟨depth, rfl⟩
  · exact HN (by simpa only [ProofShape.subst_id] using Hhead)
  · exact HN (WrappedConstHead.of_liftN_one (by simpa only [subst_bvar_liftN] using Hhead))

/-- A primitive head loss after proof-valued endpoint consumption reads the
same target equation, even when completion contains arbitrary unused ambient
insertions. The primitive is renamed back to the completed source after its
recorded annotation history; no target inhabitants for those insertions enter. -/
theorem IteratedAmbientEqCompletion.read_proof_endpoint_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ source)
    (HC : ProofEndpointContext D Ξ Ξ' τ)
    (HR : PiInertStage D n Ξ' (source.subst τ) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target) : env.IsDefEq univs Δ a b α := by
  obtain ⟨Γ, f, F, hΓ, EΓ, hf, Ef⟩ := HP.typed
  obtain ⟨Θ, κ, HH, WK, HK, EK⟩ := HC.retraction heq hs hΓ EΓ
  have ES : (source.subst τ).subst κ = source := by
    rw [← Ef, ProofShape.subst_subst]
    exact proofErase_subst_retained hΓ hf HK
  have HR' := pi_inert_stage_rename heq hs n HR WK
  rw [ES] at HR'
  apply (HP.context_history heq hs hΔ HH).read_loss heq hs hreg hoff hD hΔ ht HR'
  intro Hhead
  rcases EK with rfl | ⟨depth, rfl⟩
  · exact HN (by simpa only [ProofShape.subst_id] using Hhead)
  · apply HN
    exact WrappedConstHead.of_liftN_one (by simpa only [subst_bvar_liftN] using Hhead)

/-- At a nonstructural head loss, the bounded target prefix suffices after
proof-valued consumption. Typing of the actual resulting spine bounds its
arity before the reverse-renaming readout is applied. -/
theorem EqTargetPrefixCompletion.read_proof_endpoint_loss
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : ProofEndpointContext D Ξ Ξ' τ)
    (HT : TypedSource Ξ' (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))))
    (HR : PiInertStage D n Ξ' (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Ξ'
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))) target) :
    env.IsDefEq univs Δ a b α := by
  have hlen : args.length ≤ 5 := by
    simpa only [List.length_map] using
      (typed_nonstructural_eq_head_loss_singleton heq hreg hoff hD HT HR HN Hstruct).1
  have HP' : IteratedAmbientEqCompletion Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args) := by
    simpa only [List.length_cons, List.length_nil, List.take_of_length_le hlen] using HP.prefix
  exact HP'.read_proof_endpoint_loss heq hs hreg hoff hD hΔ ht HC
    (by simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HR) HN

/-- The actual consumed endpoint at a nonstructural head loss either reads
the target equation or identifies its particular base binder without a Prop
domain witness. This exclusion applies to arbitrary iterated unused ambient
insertions; it does not require a complete source-to-target assignment. -/
theorem EqTargetPrefixCompletion.endpoint_loss_or_unwitnessed_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Δ v w [α,a,M,minor,b] Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : PiInertEndpointContext D Ξ Ξ' τ)
    (HT : TypedSource Ξ' (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))))
    (HR : PiInertStage D n Ξ' (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))) target)
    (HN : ¬ WrappedConstHead ``Eq.rec target)
    (Hstruct : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Ξ'
      (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ))) target) :
    env.IsDefEq univs Δ a b α ∨
      ∃ Θ A rawX depth, ContextSubstitution (A :: Θ) Θ (ProofShape.Subst.one rawX) ∧
        ¬ DomainSort Θ A .zero ∧ τ = (ProofShape.Subst.one rawX).liftN depth := by
  rcases HC.proof_or_unwitnessed_domain with HC | HNdomain
  · exact .inl (HP.read_proof_endpoint_loss heq hs hreg hoff hD hΔ ht HC HT HR HN Hstruct)
  · exact .inr HNdomain

end Lean4Lean.VEnv.Strengthening
