import Lean4Lean.Theory.Typing.Strengthening.RecoveryFullHeads
import Lean4Lean.Theory.Typing.Strengthening.RecoveryReplay
import Lean4Lean.Theory.Typing.Strengthening.EtaScope

/-! # Unconditional recovery existence over full reduction

Under canonical Eq, every well-formed term has a syntactically reconstructed
type if its type computations may use full reduction. This needs only ambient
replay and confluence, not strengthening. Full reduction fails exact scoped
descent, so this is a completeness baseline, not a solution to strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Ordinary full reduction using the canonical environment's confluence
parameters. This relation has ambient replay but not exact scoped descent. -/
def FullRecoveryCompute (Γ : List VExpr) (e out : VExpr) : Prop :=
  @FullReduction (henv.params univs) Γ e out

/-- Full subject reduction gives the weaker replay interface. -/
theorem FullRecoveryCompute.replay : ComputeReplay FullRecoveryCompute := by
  intro Γ e out R hΓ T ht
  exact @FullReduction.defeq (henv.params univs) _ _ _ _ hΓ R ht

/-- Confluence already supplies complete computational Pi exposure in this
unrestricted base. -/
theorem FullRecoveryCompute.piExposure (heq : env.HasCanonicalEq) :
    RecoveryPiExposure FullRecoveryCompute := by
  intro Γ T A B u hΓ hT H
  exact defeq_pi_full_exposure henv heq hΓ (H.of_l henv hΓ hT)

/-- Full family exposure and field totality supply the projection clause,
including the typing needed for replay of its selected field. -/
theorem FullRecoveryCompute.projectionExposure (heq : env.HasCanonicalEq) :
    RecoveryProjectionExposure FullRecoveryCompute := by
  intro Γ s i m T hΓ ht hm
  obtain ⟨ls, args, R⟩ := projection_type_full_exposure henv heq hΓ ht hm
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  have hm' := (replay R hΓ _ hT).defeq hm
  obtain ⟨_, ht'⟩ := ht
  obtain ⟨info, _, _, _, _, _, _, hi, _⟩ := HasType.proj_inv henv hΓ ht'
  obtain ⟨F, hF⟩ := projection_recovered_field_exists henv hΓ hi ⟨_, ht'⟩ hm'
  exact ⟨info, ls, args, F, hi, R, hF⟩

/-- Every well-formed expression has a full-reduction recovery certificate.
No scoped computation or strengthening assumption occurs in this theorem. -/
theorem full_recovery_exists (heq : env.HasCanonicalEq) :
    RecoveryExists FullRecoveryCompute :=
  (RecoveryHeads.of_replay_exposure FullRecoveryCompute.replay
    (FullRecoveryCompute.piExposure heq) (FullRecoveryCompute.projectionExposure heq)).exists

/-- The synthesized output is convertible to any originally supplied type.
This is completeness at some output, not exact-output completeness. -/
theorem full_recovery_complete_up_to_conversion (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ T', TypeRecoveryWith FullRecoveryCompute Γ e T' ∧
      env.HasType univs Γ e T' ∧ env.IsDefEqU univs Γ T T' := by
  obtain ⟨T', R⟩ := full_recovery_exists heq hΓ ⟨_, ht⟩
  have ht' := R.hasType_of_replay FullRecoveryCompute.replay hΓ ⟨_, ht⟩
  exact ⟨T', R, ht', ht.uniqU henv hΓ ht'⟩

/-- Full recovery's computational base cannot be fed directly into the scoped
descent machinery: an actual typed eta step introduces a captured annotation.
This refutes that interface, not recovery existence or strengthening. -/
theorem FullRecoveryCompute.not_computeDescent : ¬ ComputeDescent FullRecoveryCompute := by
  intro hc
  have R : FullRecoveryCompute [.sort .zero] (Developments.ident 0).lift
      (EtaScope.expanded (.sort .zero)) :=
    .tail .rfl (@EtaScope.captured_step (henv.params univs) (.sort .zero) [])
  rw [lift_eq_lift'] at R
  have hΓ : OnCtx [.sort .zero] (env.IsType univs) :=
    ⟨trivial, _, HasType.sort (by trivial)⟩
  obtain ⟨out, hout, _⟩ := hc R (.skip .refl) trivial hΓ
    (Developments.ident_typed env univs [] 0)
  have hscope : (EtaScope.expanded (.sort .zero)).Skips 1 0 := by
    rw [hout, ← lift_eq_lift']
    exact .liftN
  exact EtaScope.captured_not_lift hscope

end Lean4Lean.VEnv.Strengthening
