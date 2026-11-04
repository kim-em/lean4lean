import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlObservationTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBackwardContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadout

/-! # Pi readout with full masked structure eta

A closed control type is a sort or arrow, and therefore cannot be a registered
structure family. Structure expansion cannot destroy a marked control frame.
Certificate descent and backward binder transport preserve the original
component histories through every finite stage of the enriched language.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.ControlObservation
variable [Params] {D : PureObservation.Definitions}

/-- Closed control frames cannot be structure majors: their sort or arrow
assignment is separated from every registered rigid family by type uniqueness. -/
theorem ControlTyping.no_masked_structure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e t) (R : NativeMaskedStructureExpansion Step Δ e out) : False := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  cases R with
  | intro hi hx ha hp RN =>
    obtain ⟨A, hFA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
    obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv EA
    obtain ⟨_, hA⟩ := hFA.isType henv hΓ
    have HE := hFA.uniqU henv hΓ hf
    cases t with
    | sort u =>
      exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ hA).symm
    | arrow A B => exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hA HE

/-- Every enriched primitive preserves typed marked Pi observations. The
new structure branch is impossible at the observation's closed control type. -/
theorem erased_static_structure_stage_controlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) : ∀ stage {Δ a b P n S t o},
    ErasedStaticStructureEtaExpansionStage D stage Δ a b → Obs P n Δ S a t o → Obs P n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b P n S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b P n S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure (erased_static_structure_eta_expansion_stage_descent heq hs stage) R).elim

/-- All finite structure/function-eta guard depths preserve the observation. -/
theorem erased_static_structure_union_controlObservation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b) (H : Obs P n Δ S a t o) : Obs P n Δ S b t o := by
  obtain ⟨stage, R⟩ := R
  exact erased_static_structure_stage_controlObservation heq hs stage R H

/-- A payload records actual component representatives and computation from
the initial Pi. Its codomain history stays in the initial binder context. -/
def StaticStructurePiOrigin (D : PureObservation.Definitions) (Γ : List VExpr)
    (A B : VExpr) (u v : VLevel) (X Y : ProofShape) : Prop :=
  ∃ A' B', env.IsDefEq univs Γ A A' (.sort u) ∧
    env.HasType univs (A' :: Γ) B' (.sort v) ∧
    proofErase Γ A' = X ∧ proofErase (A' :: Γ) B' = Y ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) X ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) Y

/-- An initial typed Pi supplies a payload with reflexive component histories. -/
theorem StaticStructurePiOrigin.refl
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v)) :
    StaticStructurePiOrigin D Γ A B u v (proofErase Γ A) (proofErase (A :: Γ) B) :=
  ⟨A, B, hA, hB, rfl, rfl, .refl, .refl⟩

/-- Component computation of a marked Pi lowers through every temporary
prefix, then appends both histories. Later codomain paths are pulled back to
the initial domain using its retained computation and actual equality. -/
theorem static_structure_piOrigin_componentClosure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D) Γ (StaticStructurePiOrigin D Γ A B u v) := by
  intro Γ' n X Y outX outY hΓ' W HP RX RY
  obtain ⟨A₀, B₀, HA₀, hB₀, rfl, rfl, RA₀, RB₀⟩ := HP
  have hA₀ := HA₀.hasType.2
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA₀⟩
  have hΓA₀' : OnCtx (A₀.liftN n :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀.weakN henv W⟩
  obtain ⟨A₁, HA₁, RA₁, EA₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs) hΓ hΓ' W hA₀ rfl RX
  have EΓB : proofEraseCtx (A₀.liftN n :: Γ') =
      (proofErase Γ A₀).liftN n :: proofEraseCtx Γ' := by
    rw [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA₀]
  obtain ⟨B₁, HB₁, RB₁, EB₁⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs) hΓA₀ hΓA₀' W.succ hB₀ EΓB RY
  have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A₁ :: Γ) := .succ .zero HA₁
  have hB₁ := HB₁.hasType.2.defeqDFC henv HC
  have EB₁' := proofErase_defeqCtx hΓA₀ HC HB₁.hasType.2
  have RPB := proofErase_static_structure_union_compute_backward_context heq hs hΓ HA₀ RA₀ hB₀ RB₁
  have EB₀ := proofErase_defeqCtx hΓA₀ (IsDefEqCtx.succ .zero HA₀.symm) hB₀
  rw [← EB₀, EB₁'] at RPB
  refine ⟨proofErase Γ A₁, proofErase (A₁ :: Γ) B₁,
    ⟨A₁, B₁, HA₀.trans HA₁, hB₁, rfl, rfl, RA₀.trans RA₁, RB₀.trans RPB⟩, EA₁.symm, ?_⟩
  rw [EB₁'] at EB₁
  exact EB₁.symm

/-- Arbitrary compatible expanded computation from a typed Pi retains its
actual lower payload and both original component histories. Applications,
computed constant/identity functions, native eta, beta interleavings and changed binders
are all covered by the same marked-observation induction. -/
theorem proofErase_static_structure_union_pi_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ X Y, StaticStructurePiOrigin D Γ A B u v X Y ∧ ProofShape.BetaRed out (.forallE X Y) := by
  have hPi := HasType.forallE hA hB
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HC : ControlTyping (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) :=
    ⟨Γ, .forallE A B, hΓ, rfl, hPi, E⟩
  have H : Obs (StaticStructurePiOrigin D Γ A B u v) 0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HC) (StaticStructurePiOrigin.refl hA hB))
  have HO := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs) (erased_static_structure_union_controlObservation heq hs)
    (static_structure_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero []) hPi rfl E (fun _ _ _ h => h.elim) H
  exact HO.readout

/-- At a literal Pi endpoint the marked payload is already exposed; no
additional beta cleanup or normalization of either component is needed. -/
theorem ProofShape.ControlObservation.Obs.literal_pi_payload
    (H : Obs P 0 Δ S (.forallE X Y) t o) : P X Y := by
  generalize HE : ProofShape.forallE X Y = e at H
  cases H with
  | payload _ HP =>
    simp only [ProofShape.liftN_zero] at HE
    cases HE
    exact HP
  | var | app | lam => cases HE

/-- A typed Pi-to-Pi path has exact component histories, including a codomain
path in the original binder context. Unlike general readout, no residual beta
step is needed at the prescribed literal endpoint. -/
theorem proofErase_static_structure_union_pi_components
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.forallE X Y)) :
    StaticStructurePiOrigin D Γ A B u v X Y := by
  have hPi := HasType.forallE hA hB
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have HC : ControlTyping (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) :=
    ⟨Γ, .forallE A B, hΓ, rfl, hPi, E⟩
  have H : Obs (StaticStructurePiOrigin D Γ A B u v) 0 (proofEraseCtx Γ) (fun _ _ _ => False)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) .pi := by
    simpa only [ProofShape.liftN_zero] using
      (Obs.payload (n := 0) (S := fun _ _ _ => False)
        (by simpa only [ProofShape.liftN_zero] using HC) (StaticStructurePiOrigin.refl hA hB))
  exact (proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_controlObservation heq hs)
    (static_structure_piOrigin_componentClosure heq hs hΓ) R hΓ (Ctx.LiftN.zero []) hPi
    rfl E (fun _ _ _ h => h.elim) H).literal_pi_payload

/-- Full PiReadout coverage for every typed Pi and every expanded union path.
Both component paths remain in the original scopes, including the dependent
codomain. No native recovery or image-coverage assumption is required. -/
theorem proofErase_static_structure_union_pi_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    PiReadout (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, ⟨A', B', _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB R
  exact ⟨X, Y, RA, by simpa only [proofEraseCtx] using RB, Rβ⟩

/-- A finite input stage has a finite later component bound. This extracts
only the stages actually used by the retained domain and codomain histories;
the enclosing wrapper computations need not be native recovered outputs. -/
theorem proofErase_static_structure_stage_pi_readout_later
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out) :
    ∃ later, stage ≤ later ∧ PiReadout (ErasedStaticStructureEtaExpansionStage D later) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) out := by
  obtain ⟨X, Y, RA, RB, Rβ⟩ := proofErase_static_structure_union_pi_readout heq hs hΓ hA hB
    (R.mono (fun H => ⟨stage, H⟩))
  obtain ⟨n, RA⟩ := RA.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  obtain ⟨m, RB⟩ := RB.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  refine ⟨max stage (max n m), by omega, X, Y, ?_, ?_, Rβ⟩
  · exact RA.mono (fun H => erased_static_structure_eta_expansion_stage_mono (by omega) H)
  · exact RB.mono (fun H => erased_static_structure_eta_expansion_stage_mono (by omega) H)

end Lean4Lean.VEnv.Strengthening
