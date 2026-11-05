import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeaderApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorParameterBoundary

/-! # Directed native header histories are not beta stable

Identity wrappers expose the weakness of the extensional history predicate:
their native outputs depend on the written annotation, while contraction
exposes the argument's independently selected native types. A registered
unit-parameter constructor supplies an actual typed counterexample. Packaging
the argument as a constant function also gives a counterexample at a Pi header.
This does not refute preservation for a stronger term-provenance invariant.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Computation of a source typed below insertion cannot introduce a fresh
variable as a retained application argument. This concerns the type path itself,
not failure of exact native recovery at its endpoint. -/
theorem computed_source_no_inserted_argument
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n)
    (R : ScopedCompute Step (proofEraseCtx Γ')
      (proofErase Γ' (e.liftN n k)) (.app f (.bvar j))) : False := by
  rw [proofErase_liftN hΓ hΓ' W ht] at R
  obtain ⟨e', _, E⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ht rfl R
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv E
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar] at hj hj'
  split at hj <;> simp_all <;> omega

/-- A typed identity wrapper has the assigned header's history even when its
contractum does not. Thus arbitrary preservation cannot follow from the current
source's native histories alone. The body needs its own ancestry information. -/
theorem native_header_identity_beta_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e A)
    (hn : ¬ IsProof Γ e)
    (Hno : ¬ NativeHeaderHistory D Γ (proofErase Γ A) (proofErase Γ e)) :
    NativeHeaderHistory D Γ (proofErase Γ A)
        (proofErase Γ (.app (.lam A (.bvar 0)) e)) ∧
      BetaRed (proofErase Γ (.app (.lam A (.bvar 0)) e)) (proofErase Γ e) ∧
      ¬ NativeHeaderHistory D Γ (proofErase Γ A) (proofErase Γ e) := by
  refine ⟨?_, proofErase_identity_wrapper_beta hΓ he hn, Hno⟩
  rw [proofErase_nativeIdentityExpansion hΓ he hn]
  exact NativeHeaderHistory.identity heq hs hΓ he hn .refl

/-- A constant function cannot conceal failure of directed header ancestry.
Applying it to Prop, whose native type is exact, reflects a Pi-header history
back to a history for the original body. -/
theorem native_header_constant_function_reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e A)
    (hn : ¬ IsProof Γ e)
    (H : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.sort (.succ .zero)) A.lift))
      (proofErase Γ (.lam (.sort (.succ .zero)) e.lift))) :
    NativeHeaderHistory D Γ (proofErase Γ A) (proofErase Γ e) := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hx : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΓS : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  obtain ⟨u, hA⟩ := he.isType henv hΓ
  have HR : ¬ IsProof Γ (.sort .zero) → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.sort .zero)) (proofErase Γ (.sort (.succ .zero))) := by
    intro _
    rw [show proofErase Γ (.sort .zero) = .sort .zero from if_neg (not_isProof_of_sort hΓ hx),
      show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
        if_neg (not_isProof_of_sort hΓ hS)]
    exact .sort (by trivial)
  have HA : NativeHeaderHistory D Γ (proofErase Γ A)
      (.app (proofErase Γ (.lam (.sort (.succ .zero)) e.lift)) (proofErase Γ (.sort .zero))) := by
    intro out RN
    simpa only [VExpr.inst_lift] using H.application heq hs hΓ hS
      (hA.weakN henv Ctx.LiftN.one) hx HR .refl RN
  intro out RN
  have RI := (static_structure_constant_beta_native_iff heq hs hΓ he hx).2 RN
  have hne := mt (isProof_congr hΓ (constantExpansion_equal he)).1 hn
  rw [show proofErase Γ (.app (.lam (.sort (.succ .zero)) e.lift) (.sort .zero)) =
    .app _ _ from if_neg hne] at RI
  exact HA RI

/-- The beta counterexample can be placed at a well-typed function header.
Restricting the history predicate to Pi assignments does not fix its missing
information about the body of an identity frame. -/
theorem native_header_beta_failure_at_function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e A)
    (hn : ¬ IsProof Γ e)
    (Hno : ¬ NativeHeaderHistory D Γ (proofErase Γ A) (proofErase Γ e)) :
    ∃ f Q, env.HasType univs Γ f Q ∧ ¬ IsProof Γ f ∧
      (∃ X Y, Q = .forallE X Y) ∧
      NativeHeaderHistory D Γ (proofErase Γ Q)
        (proofErase Γ (.app (.lam Q (.bvar 0)) f)) ∧
      BetaRed (proofErase Γ (.app (.lam Q (.bvar 0)) f)) (proofErase Γ f) ∧
      ¬ NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ f) := by
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hf := HasType.lam hS (he.weakN henv (Ctx.LiftN.one (A := .sort (.succ .zero))))
  have hx : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hne := mt (isProof_congr hΓ (constantExpansion_equal he)).1 hn
  have hnf := not_isProof_fn hΓ hf hx hne
  have Hnf : ¬ NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.sort (.succ .zero)) A.lift))
      (proofErase Γ (.lam (.sort (.succ .zero)) e.lift)) :=
    fun H => Hno (native_header_constant_function_reflect heq hs hΓ he hn H)
  exact ⟨_, _, hf, hnf, ⟨_, _, rfl⟩, native_header_identity_beta_failure heq hs hΓ hf hnf Hnf⟩

/-- A retained constructor assigned Tag q has a native Tag p output. The
assigned type cannot compute to that output: p is an unused inserted variable
relative to the context in which Tag q was already typed. Unit equality provides
the ordinary assignment, but it does not provide that directed computation. -/
theorem registered_constructor_without_assigned_header_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) :
    ∃ Γ e A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e A ∧
      ¬ IsProof Γ e ∧ ¬ NativeHeaderHistory D Γ (proofErase Γ A) (proofErase Γ e) := by
  let S := VExpr.const s []
  let Γ₀ := [S]
  let Γ := [S, S]
  let e := VExpr.app (.const c []) (.bvar 1)
  let A := VExpr.app (.const t []) (.bvar 0)
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨trivial, _, hS⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hS.weak0 henv.ordered⟩
  have hC : env.HasType univs Γ (.const c [])
      (.forallE S (.app (.const t []) (.bvar 0))) :=
    .const (henv.ordered.projectionConstructor hTag) (by simp) rfl
  have hP : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hQ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have he : env.HasType univs Γ e (.app (.const t []) (.bvar 1)) := .app hC hP
  have hFP : env.HasType univs Γ (.app (.const t []) (.bvar 1)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hP
  have HE := IsDefEq.appDF (hF.weak0 (Γ := Γ) henv.ordered)
    (IsDefEq.unitLike hi (params := []) hp.symm hx hz hP hQ)
  have heA : env.HasType univs Γ e A := HE.defeq he
  have hn := not_proof_at_positive_type hΓ hFP he
  have EP : proofErase Γ (.bvar 1) = .bvar 1 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hP)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.app (.const t []) (.bvar 1)) := by
    simpa [PositiveHeaderRegistration.info, ProofShape.mkApps, EP] using
      (proofErase_structure_constructor_native (Step := ErasedStaticStructureEtaExpansionUnion D)
        hΓ hTag rfl (args := [.bvar 1]) (levels := []) rfl he hn)
  have hA₀ : env.HasType univs Γ₀ A (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) (HasType.bvar .zero)
  have W : Ctx.LiftN 1 1 Γ₀ Γ := (Ctx.LiftN.one (Γ := []) (A := S)).succ
  refine ⟨Γ, e, A, hΓ, heA, hn, ?_⟩
  intro H
  have R := H RN
  exact computed_source_no_inserted_argument
    (erased_static_structure_eta_expansion_union_descent heq hs)
    hΓ₀ hΓ W hA₀ (by decide) (by decide) R

/-- In the same registered unit/phantom-family setting, directed header
ancestry is lost by one typed identity beta contraction at a Pi assignment.
The source history is constructed, not assumed. This refutes general beta
closure of NativeHeaderHistory, not canonical-Eq strengthening or the earlier
root-expansion theorem with its stronger construction history. -/
theorem registered_function_header_beta_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) :
    ∃ Γ f Q, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ f Q ∧
      ¬ IsProof Γ f ∧ (∃ X Y, Q = .forallE X Y) ∧
      NativeHeaderHistory D Γ (proofErase Γ Q)
        (proofErase Γ (.app (.lam Q (.bvar 0)) f)) ∧
      BetaRed (proofErase Γ (.app (.lam Q (.bvar 0)) f)) (proofErase Γ f) ∧
      ¬ NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ f) := by
  obtain ⟨Γ, e, A, hΓ, he, hn, Hno⟩ :=
    registered_constructor_without_assigned_header_history heq hs hi hp hx hz hS hTag hF
  obtain ⟨f, Q, hf, hn, hPi, HH, RB, Hno⟩ :=
    native_header_beta_failure_at_function heq hs hΓ he hn Hno
  exact ⟨Γ, f, Q, hΓ, hf, hn, hPi, HH, RB, Hno⟩

/-- Even actual native-guarded wrapper creation does not make the extensional
header invariant beta stable. The initial function both has the history and
recovers the header exactly; its native identity expansion has the history too,
but beta computation of the generated term reaches a function without it.
This still does not refute the stronger special provenance of a bare constructor. -/
theorem registered_generated_header_beta_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
    (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
    (hF : env.HasType univs [] (.const t [])
      (.forallE (.const s []) (.sort (.succ .zero)))) :
    ∃ Γ start frame out Q, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ start Q ∧ env.HasType univs Γ frame Q ∧ env.HasType univs Γ out Q ∧
      (∃ X Y, Q = .forallE X Y) ∧
      NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ start) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ start) (proofErase Γ Q) ∧
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ start) (proofErase Γ frame) ∧
      NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ frame) ∧
      BetaRed (proofErase Γ frame) (proofErase Γ out) ∧
      ¬ NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ out) := by
  obtain ⟨Γ, f, Q, hΓ, hf, hn, hPi, HH, RB, Hno⟩ :=
    registered_function_header_beta_failure heq hs hi hp hx hz hS hTag hF
  let start := VExpr.app (.lam Q (.bvar 0)) f
  let frame := VExpr.app (.lam Q (.bvar 0)) start
  have hstart : env.HasType univs Γ start Q := (nativeIdentityExpansion_equal hf).hasType.1
  have hframe : env.HasType univs Γ frame Q := (nativeIdentityExpansion_equal hstart).hasType.1
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ start) (proofErase Γ Q) := proofErase_identity_wrapper_native hΓ hf hn
  have hnstart : ¬ IsProof Γ start := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  have HHframe : NativeHeaderHistory D Γ (proofErase Γ Q) (proofErase Γ frame) := by
    rw [show proofErase Γ frame =
      .app (.lam (proofErase Γ Q) (.bvar 0)) (proofErase Γ start) from
      proofErase_nativeIdentityExpansion hΓ hstart hnstart]
    exact NativeHeaderHistory.identity heq hs hΓ hstart hnstart .refl
  refine ⟨Γ, start, frame, f, Q, hΓ, hstart, hframe, hf, hPi, HH, RN, ?_, HHframe, ?_, Hno⟩
  · rw [show proofErase Γ frame =
      .app (.lam (proofErase Γ Q) (.bvar 0)) (proofErase Γ start) from
      proofErase_nativeIdentityExpansion hΓ hstart hnstart]
    exact .intro RN
  · exact (proofErase_identity_wrapper_beta hΓ hstart hnstart).trans RB

end Lean4Lean.VEnv.Strengthening
