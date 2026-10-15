import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationSingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationStages

/-! # Recovered application checking throughout singleton computation

Every general singleton family guard now uses recursive recovered-application
checking, just like the specialized Eq prefix. All earlier application stages embed. Descent and operational replay are proved;
substitution closure is not assumed or asserted for this enlarged family.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Core, arbitrary singleton family guards with recovered application checking,
structure-carrier prefixes, and the specialized application-checked Eq prefix. -/
def ErasedRecursiveSingletonStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage+1 => fun Δ a b => ErasedRecursiveSingletonStage D stage Δ a b ∨
      ProofShape.ApplicationSingletonPrimitive (ErasedRecursiveSingletonStage D stage) Δ a b ∨
      ProofShape.ScopedStructurePrefixPrimitive (ErasedRecursiveSingletonStage D stage) Δ a b ∨
      ProofShape.ApplicationPrefixPrimitive (ErasedRecursiveSingletonStage D stage) Δ a b

/-- Every enlarged stage has source-typed descent through any binder block. -/
theorem erased_recursive_singleton_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedRecursiveSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R | R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_application_singleton_descent heq ih hΓ hΓ' W ht R
    · exact erased_structure_prefix_descent heq ih hΓ hΓ' W ht R
    · exact erased_application_prefix_descent heq ih hΓ hΓ' W ht R

/-- Every preceding application stage embeds at the same bound, including
its typed general singleton, structure and specialized Eq prefix primitives. -/
theorem erased_application_into_recursive_singleton : ∀ stage {Δ a b},
    ErasedApplicationStage D stage Δ a b → ErasedRecursiveSingletonStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.application.mono ih))
    · exact .inr (.inr (.inl (H.mono ih)))
    · exact .inr (.inr (.inr (H.mono ih)))

/-- Stage bounds may increase without changing contexts or syntax. -/
theorem erased_recursive_singleton_stage_mono (hle : stage ≤ later) {Δ a b}
    (H : ErasedRecursiveSingletonStage D stage Δ a b) : ErasedRecursiveSingletonStage D later Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- New guards still contract only constant/projection-headed primitives. -/
theorem erased_recursive_singleton_stage_head : ∀ stage {Δ a b},
    ErasedRecursiveSingletonStage D stage Δ a b → ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H | H
    · exact ih H
    · exact H.2.head
    · exact H.head
    · exact H.head

/-- Every stage replays as an actual original prefix computation, with exact
captures and erasure. No certificate-substitution hypothesis is required. -/
theorem erased_recursive_singleton_stage_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedRecursiveSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ e T out hΓ ht R
    obtain ⟨e', HR, HE⟩ := erased_iota_replay hs hΓ ht R
    exact ⟨e', .base HR, HE⟩
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    rcases R with R | R | R | R
    · exact ih hΓ ht R
    · exact erased_application_singleton_replay heq
        (erased_recursive_singleton_stage_descent heq hs stage) hΓ ht R
    · exact erased_structure_prefix_replay heq hs
        (erased_recursive_singleton_stage_descent heq hs stage) hregistry hΓ ht R
    · exact erased_application_prefix_replay heq hs
        (erased_recursive_singleton_stage_descent heq hs stage) hregistry hΓ ht R

/-- Compatible enlarged computations retain an original typed operational path. -/
theorem proofErase_recursive_singleton_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedRecursiveSingletonStage D stage) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_recursive_singleton_stage_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- An application-checked Eq prefix computes at the next stage. -/
theorem proofErase_recursive_singleton_prefix_stage_forward (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.ApplicationCompare (ErasedRecursiveSingletonStage D stage) (proofEraseCtx Γ)
      true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedRecursiveSingletonStage D (stage+1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_application_prefix_forward heq (erased_recursive_singleton_stage_descent heq hs stage)
    hΓ ht HC).mono (fun H => .inr (.inr (.inr H)))

/-- Supplying the proof major completes an application-checked Eq reduction
by beta, with arbitrary dependent motives and source-typed captures. -/
theorem proofErase_recursive_singleton_full_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.ApplicationCompare (ErasedRecursiveSingletonStage D stage) (proofEraseCtx Γ)
      true (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedRecursiveSingletonStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_application_compare_reflect
    (erased_recursive_singleton_stage_descent heq hs stage) hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    have HR : ProofShape.ScopedCompute (ErasedRecursiveSingletonStage D (stage + 1)) (proofEraseCtx Γ)
        (ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
          (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
        (.lam (ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
          ((proofErase Γ m).liftN 1)) := .base (.inr (.inr (.inr (.intro HC))))
    apply ProofShape.ScopedCompute.trans (.app HR (.refl (e := proofErase Γ p)))
    apply ProofShape.ScopedCompute.beta
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (ProofShape.BetaRed.beta
        (A := ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
        (b := (proofErase Γ m).liftN 1) (a := proofErase Γ p))


/-- A checked generated prefix with a scoped family certificate computes in the
general raw primitive relation. Proof-valued whole sources give identity. -/
theorem proofErase_recursive_singleton_general_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (HG : GuardedSingleton.FamilyGuard (ErasedFamilyComparison (fun Δ => ProofShape.ApplicationCompare (ErasedRecursiveSingletonStage D stage) Δ true))
      Γ data levels args program S E) :
    ProofShape.ScopedCompute (ErasedRecursiveSingletonStage D (stage + 1)) (proofEraseCtx Γ)
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
  have HE := proofErase_const_spine hΓ HC.source_typed hp
  have HT : ProofShape.TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const data.name levels) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, HC.source_typed, HE⟩
  rw [HE, V.output_eq heq hΓ hg HC hp]
  exact .base (.inr (.inl ⟨HT, .intro V (by simp only [List.length_map, C])
    (V.telescope_eq hΓ hg ht) ((V.guardWith_iff heq hΓ hg ht).2 HG)⟩))

end Lean4Lean.VEnv.Strengthening
