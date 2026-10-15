import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructurePrefix

/-! # General singleton stages with explicit structure-carrier guards

Recursive carrier comparisons use computation from the preceding stage.
Closed proof-field certificates skip mixed proof fields. These stages preserve
all preceding unit and general-singleton computations, together with descent,
substitution and exact operational replay. Full guard coverage remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- General singleton guards can use all earlier computations, including the
structure-carrier Eq rule. The stage-zero ordinary core is unchanged. -/
def ErasedStructureSingletonStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedStructureSingletonStage D stage Δ a b ∨
      ProofShape.ScopedTypedSingletonPrimitive (ErasedStructureSingletonStage D stage) Δ a b ∨
      ProofShape.ScopedStructurePrefixPrimitive (ErasedStructureSingletonStage D stage) Δ a b

/-- Every augmented stage descends below arbitrary block insertion. -/
theorem erased_structure_singleton_stage_descent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedStructureSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_scoped_typed_singleton_descent heq ih hΓ hΓ' W ht R
    · exact erased_structure_prefix_descent heq ih hΓ hΓ' W ht R

/-- Typed context substitution preserves the exact stage and endpoints. The
structure rule transports field comparisons and introduces no recovery premise. -/
theorem erased_structure_singleton_stage_subst (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ∀ stage {Δ Δ' a b τ},
    ErasedStructureSingletonStage D stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
    ErasedStructureSingletonStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero => exact fun H _ => erased_iota_primitive_subst H
  | succ stage ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H | H
    · exact .inl (ih H W)
    · exact .inr (.inl (H.subst heq (erased_structure_singleton_stage_descent heq hs stage) ih W))
    · exact .inr (.inr (H.subst ih W))

/-- The new stages retain all existing general-singleton computations at the
same bound, including their recursively compared family guards. -/
theorem erased_typed_singleton_into_structure : ∀ stage {Δ a b},
    ErasedScopedTypedSingletonStage D stage Δ a b → ErasedStructureSingletonStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))

/-- Ordinary scoped K-prefix stages also embed at the same bound: their
endpoint certificates use the ordinary-checking leaf of the carrier guard. -/
theorem erased_scoped_prefix_into_structure : ∀ stage {Δ a b},
    ErasedScopedPrefixStage D stage Δ a b → ErasedStructureSingletonStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro HC => exact .inr (.inr (.intro (.checked (HC.mono ih))))

/-- All primitive steps still have constant or projection heads. In particular,
adding the new computational rule does not itself add neutral comparison rules. -/
theorem erased_structure_singleton_stage_head : ∀ stage {Δ a b},
    ErasedStructureSingletonStage D stage Δ a b → ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact ih H
    · cases H.2
      have aux : ∀ (args : List ProofShape) (f : ProofShape), ProofShape.PrimitiveHead f →
          ProofShape.PrimitiveHead (ProofShape.mkApps f args) := by
        intro args
        induction args with
        | nil => exact fun _ H => H
        | cons a args ih => exact fun f H => ih (.app f a) H
      exact aux _ _ trivial
    · exact H.head

/-- Exact operational replay holds at every augmented stage, including guards
that themselves use a structure-carrier prefix computation. -/
theorem erased_structure_singleton_stage_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedStructureSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ e T out hΓ ht R
    obtain ⟨e', HR, HE⟩ := erased_iota_replay hs hΓ ht R
    exact ⟨e', .base HR, HE⟩
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    rcases R with R | R | R
    · exact ih hΓ ht R
    · exact erased_scoped_typed_singleton_replay heq
        (erased_structure_singleton_stage_descent heq hs stage) hΓ ht R
    · exact erased_structure_prefix_replay heq hs
        (erased_structure_singleton_stage_descent heq hs stage) hregistry hΓ ht R

/-- Compatible augmented computation reconstructs an actual type-preserving
original prefix path with the same erased target. -/
theorem proofErase_structure_singleton_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedStructureSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_structure_singleton_stage_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- Every earlier unit-augmented stage embeds at the same finite bound. The
unit carrier is the zero-field instance of the new structural carrier guard. -/
theorem erased_unit_singleton_into_structure : ∀ stage {Δ a b},
    ErasedUnitSingletonStage D stage Δ a b → ErasedStructureSingletonStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr H.structure)

/-- A typed carrier-guarded Eq prefix enters the next finite stage. -/
theorem proofErase_structure_singleton_prefix_forward (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D stage) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedStructureSingletonStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_structure_prefix_forward heq (erased_structure_singleton_stage_descent heq hs stage)
    hΓ ht HC).mono (fun H => .inr (.inr H))

/-- Supplying the proof major completes a carrier-guarded Eq reduction by beta.
This covers arbitrary dependent motives and mixed proof/data fields. -/
theorem proofErase_structure_singleton_full_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D stage) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute (ErasedStructureSingletonStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab : env.IsDefEqU univs Γ a b := ⟨_, proofErase_structure_carrier_reflect
    (erased_structure_singleton_stage_descent heq hs stage) hΓ ha hb HC⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hp)]
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    have HR : ProofShape.ScopedCompute (ErasedStructureSingletonStage D (stage + 1)) (proofEraseCtx Γ)
        (ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
          (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
        (.lam (ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
          ((proofErase Γ m).liftN 1)) := .base (.inr (.inr (.intro HC)))
    apply ProofShape.ScopedCompute.trans (.app HR (.refl (e := proofErase Γ p)))
    apply ProofShape.ScopedCompute.beta
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using
      (ProofShape.BetaRed.beta
        (A := ProofShape.eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b))
        (b := (proofErase Γ m).liftN 1) (a := proofErase Γ p))


end Lean4Lean.VEnv.Strengthening
