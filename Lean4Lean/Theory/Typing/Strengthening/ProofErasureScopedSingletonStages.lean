import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive

/-! # Finite stages of general scoped singleton computation

Every stage permits arbitrary registered singleton layouts, guarded by family
comparison in the previous stage. Descent and exact operational replay hold at
all stages. Forward coverage still requires the actual family certificate;
neither unrestricted substitution stability nor certificate coverage is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A checked generated prefix with a scoped family certificate computes in the
general raw primitive relation. Proof-valued whole sources give identity. -/
theorem proofErase_scoped_singleton_prefix_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ProofShape.ScopedSingletonPrefixPrimitive Step) (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const data.name levels) args)) (proofErase Γ program.rhs) := by
  by_cases hp : IsProof Γ (mkApps (.const data.name levels) args)
  · rw [proofErase_eq_proof.2 hp,
      proofErase_eq_proof.2 ((isProof_congr hΓ (HC.defeq henv hΓ)).1 hp)]
    exact .refl
  let C : SingletonPrefixCode := ⟨data, levels, args.length, recType,
    program.equation, program.equationBody, S, E⟩
  obtain ⟨_, _, _, _, heqn, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  have V : C.Valid := ⟨hreg, H, hl, hz, hw, hrec, heqn, hbody, hS, hE, args, program, rfl, hg⟩
  have ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args) := ⟨_, HC.source_typed⟩
  rw [proofErase_const_spine hΓ HC.source_typed hp, V.output_eq heq hΓ hg HC hp]
  exact .base (.intro V (by simp only [List.length_map, C]) (V.telescope_eq hΓ hg ht)
    ((V.guard_iff heq hΓ hg ht).2 HG))

/-- Core primitives followed by finitely many layers of general singleton
prefixes. Each family guard uses only the preceding stage. -/
def ErasedScopedSingletonStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedScopedSingletonStage D stage Δ a b ∨
      ProofShape.ScopedSingletonPrefixPrimitive (ErasedScopedSingletonStage D stage) Δ a b

/-- Every finite general-singleton stage descends below arbitrary block insertion. -/
theorem erased_scoped_singleton_stage_descent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedScopedSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_scoped_singleton_prefix_descent heq ih hΓ hΓ' W ht R

/-- Every finite general-singleton stage replays through actual registered
prefix computation, preserving its exact raw target. -/
theorem erased_scoped_singleton_stage_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedScopedSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ e T out hΓ ht R
    obtain ⟨e', HR, HE⟩ := erased_iota_replay hs hΓ ht R
    exact ⟨e', .base HR, HE⟩
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    rcases R with R | R
    · exact ih hΓ ht R
    · exact erased_scoped_singleton_prefix_replay heq
        (erased_scoped_singleton_stage_descent heq hs stage) hΓ ht R

/-- All compatible computations at a finite stage have typed operational replay. -/
theorem proofErase_scoped_singleton_stage_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedScopedSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_scoped_singleton_stage_prefix_replay heq hs stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- A checked original prefix whose family guard has a stage certificate erases
to a computation at the next stage, with its exact original erased output. -/
theorem proofErase_scoped_singleton_stage_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison (ErasedScopedSingletonStage D stage))
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ErasedScopedSingletonStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const data.name levels) args)) (proofErase Γ program.rhs) :=
  (proofErase_scoped_singleton_prefix_forward heq hΓ hreg H hl hz hw hrec hS hE hg HC HG).mono
    (fun H => .inr H)

end Lean4Lean.VEnv.Strengthening
