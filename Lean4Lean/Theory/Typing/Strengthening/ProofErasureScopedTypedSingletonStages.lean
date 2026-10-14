import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedSingletonSubstitution

/-! # Substitution-stable finite stages of general singleton computation

Every general singleton primitive records existence of a typed source realization.
All stages then have substitution stability, block descent, and exact operational
replay. Actual checked singleton prefixes are admitted at every layout whenever
their family guard is certified at the preceding stage. Coverage of those guards
and raw confluence remain separate obligations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Typed core computation with finitely nested general singleton family guards. -/
def ErasedScopedTypedSingletonStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedScopedTypedSingletonStage D stage Δ a b ∨
      ProofShape.ScopedTypedSingletonPrimitive (ErasedScopedTypedSingletonStage D stage) Δ a b

/-- Every finite typed-singleton stage descends below any inserted binder block. -/
theorem erased_scoped_typed_singleton_stage_descent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedScopedTypedSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_scoped_typed_singleton_descent heq ih hΓ hΓ' W ht R

/-- Every finite general stage substitutes along an interpreted raw context
substitution, without increasing its stage or changing its exact raw endpoints. -/
theorem erased_scoped_typed_singleton_stage_subst (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ∀ stage {Δ Δ' a b τ},
    ErasedScopedTypedSingletonStage D stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
    ErasedScopedTypedSingletonStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero => exact fun H _ => erased_iota_primitive_subst H
  | succ stage ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H
    · exact .inl (ih H W)
    · exact .inr (H.subst heq (erased_scoped_typed_singleton_stage_descent heq hs stage) ih W)

/-- Every finite typed-singleton stage has exact original operational replay. -/
theorem erased_scoped_typed_singleton_stage_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedScopedTypedSingletonStage D stage) := by
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
    · exact erased_scoped_typed_singleton_replay heq
        (erased_scoped_typed_singleton_stage_descent heq hs stage) hΓ ht R

/-- Typed general-singleton stage computation reconstructs a type-preserving
original path and exactly its displayed raw output. -/
theorem proofErase_scoped_typed_singleton_stage_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_scoped_typed_singleton_stage_replay heq hs stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- Actual checked prefixes at arbitrary singleton layouts satisfy the typed
source restriction automatically. Their sole recursive premise is the family
certificate, and proof-valued whole sources still erase to identity. -/
theorem proofErase_scoped_typed_singleton_prefix_forward (heq : env.HasCanonicalEq)
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
    ProofShape.ScopedCompute (ProofShape.ScopedTypedSingletonPrimitive Step) (proofEraseCtx Γ)
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
  apply ProofShape.ScopedCompute.base
  refine ⟨⟨Γ, _, _, hΓ, rfl, HC.source_typed, rfl⟩, ?_⟩
  rw [proofErase_const_spine hΓ HC.source_typed hp, V.output_eq heq hΓ hg HC hp]
  exact .intro V (by simp only [List.length_map, C]) (V.telescope_eq hΓ hg ht)
    ((V.guard_iff heq hΓ hg ht).2 HG)

/-- Every checked original prefix with a preceding-stage family certificate
erases into the next substitution-stable general stage. -/
theorem proofErase_scoped_typed_singleton_stage_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison (ErasedScopedTypedSingletonStage D stage))
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const data.name levels) args)) (proofErase Γ program.rhs) :=
  (proofErase_scoped_typed_singleton_prefix_forward heq hΓ hreg H hl hz hw hrec hS hE hg HC HG).mono
    (fun H => .inr H)

end Lean4Lean.VEnv.Strengthening
