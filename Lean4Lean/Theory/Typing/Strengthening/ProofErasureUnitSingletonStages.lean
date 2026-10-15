import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitPrefix

/-! # General singleton stages augmented by unit-carrier Eq prefixes

The new rule participates in guards of later singleton stages. All previous
stages embed. Descent, typed context substitution and exact original operational
replay are preserved; full comparison coverage and confluence remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Monotonicity of the existing typed singleton primitive in its recursive
comparison relation. The source witness and generated program are unchanged. -/
theorem ProofShape.ScopedTypedSingletonPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ScopedTypedSingletonPrimitive Step Δ a b) :
    ScopedTypedSingletonPrimitive Step' Δ a b := by
  refine ⟨H.1, ?_⟩
  cases H.2 with
  | intro V ha hcalc HG => exact .intro V ha hcalc (ProofShape.ScopedCompare.mono hstep HG)

/-- General singleton guards can use all earlier computations, including the
unit-carrier Eq rule. The stage-zero ordinary core is unchanged. -/
def ErasedUnitSingletonStage (D : PureObservation.Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => fun _ => ErasedIotaPrimitive D
  | stage + 1 => fun Δ a b => ErasedUnitSingletonStage D stage Δ a b ∨
      ProofShape.ScopedTypedSingletonPrimitive (ErasedUnitSingletonStage D stage) Δ a b ∨
      ProofShape.UnitPrefixPrimitive a b

/-- Every augmented stage descends below arbitrary block insertion. -/
theorem erased_unit_singleton_stage_descent (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveDescent (ErasedUnitSingletonStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_scoped_typed_singleton_descent heq ih hΓ hΓ' W ht R
    · exact erased_unit_prefix_descent heq hΓ hΓ' W ht R

/-- Typed context substitution preserves the exact stage and endpoints. The
unit rule needs only raw substitution, so it introduces no recovery premise. -/
theorem erased_unit_singleton_stage_subst (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : ∀ stage {Δ Δ' a b τ},
    ErasedUnitSingletonStage D stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
    ErasedUnitSingletonStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero => exact fun H _ => erased_iota_primitive_subst H
  | succ stage ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H | H
    · exact .inl (ih H W)
    · exact .inr (.inl (H.subst heq (erased_unit_singleton_stage_descent heq hs stage) ih W))
    · exact .inr (.inr (H.subst τ))

/-- The new stages retain all existing general-singleton computations at the
same bound, including their recursively compared family guards. -/
theorem erased_typed_singleton_into_unit : ∀ stage {Δ a b},
    ErasedScopedTypedSingletonStage D stage Δ a b → ErasedUnitSingletonStage D stage Δ a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))

/-- All primitive steps still have constant or projection heads. In particular,
adding the new computational rule does not itself add neutral comparison rules. -/
theorem erased_unit_singleton_stage_head : ∀ stage {Δ a b},
    ErasedUnitSingletonStage D stage Δ a b → ProofShape.PrimitiveHead a := by
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
that themselves use a unit-carrier prefix computation. -/
theorem erased_unit_singleton_stage_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedUnitSingletonStage D stage) := by
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
        (erased_unit_singleton_stage_descent heq hs stage) hΓ ht R
    · exact erased_unit_prefix_replay heq hs hregistry hΓ ht R

/-- Compatible augmented computation reconstructs an actual type-preserving
original prefix path with the same erased target. -/
theorem proofErase_unit_singleton_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedUnitSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', PureObservation.PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_unit_singleton_stage_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

/-- A unit-carrier prefix enters the augmented computation at stage one,
without a separate certificate comparing its endpoints. -/
theorem proofErase_unit_singleton_prefix_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b) T) :
    ProofShape.ScopedCompute (ErasedUnitSingletonStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w (mkApps (.const family ls) ps) a M m b))
      (proofErase Γ (.lam (eqApp w (mkApps (.const family ls) ps) a b) m.lift)) :=
  (proofErase_unit_prefix_forward heq hΓ hi hx hf hp ht).scoped (fun H => .base (.inr (.inr H)))

/-- Supplying the proof major completes the unit-carrier prefix reduction by
beta. Motives may depend on both the endpoint and its equality proof. -/
theorem proofErase_unit_singleton_full_forward (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (ht : env.HasType univs Γ (eqRecApp v w (mkApps (.const family ls) ps) a M m b q) T) :
    ProofShape.ScopedCompute (ErasedUnitSingletonStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp v w (mkApps (.const family ls) ps) a M m b q)) (proofErase Γ m) := by
  obtain ⟨_, hw, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab : env.IsDefEqU univs Γ a b := ⟨_, IsDefEq.unitLike hi hp hx hf ha hb⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hproof : IsProof Γ (eqRecApp v w (mkApps (.const family ls) ps) a M m b q)
  · rw [proofErase_eq_proof.2 hproof,
      proofErase_eq_proof.2 ((isProof_congr hΓ HH).1 hproof)]
    exact .refl
  have HE := proofErase_const_spine hΓ (args := [mkApps (.const family ls) ps, a, M, m, b, q]) ht hproof
  change proofErase Γ (eqRecApp v w (mkApps (.const family ls) ps) a M m b q) = _ at HE
  rw [HE]
  simp only [List.map_cons, List.map_nil,
    proofErase_const_spine hΓ hα (not_isProof_of_sort hΓ hα)]
  have HR : ProofShape.ScopedCompute (ErasedUnitSingletonStage D 1) (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor v w (ProofShape.mkApps (.const family ls) (ps.map (proofErase Γ)))
        (proofErase Γ a) (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
      (.lam (ProofShape.eqProofType w (ProofShape.mkApps (.const family ls) (ps.map (proofErase Γ)))
        (proofErase Γ a) (proofErase Γ b)) ((proofErase Γ m).liftN 1)) :=
    .base (.inr (.inr (.intro hi hx hf (by simpa only [List.length_map] using hp))))
  apply ProofShape.ScopedCompute.trans (.app HR (.refl (e := proofErase Γ q)))
  apply ProofShape.ScopedCompute.beta
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta
      (A := ProofShape.eqProofType w (ProofShape.mkApps (.const family ls) (ps.map (proofErase Γ)))
        (proofErase Γ a) (proofErase Γ b))
      (b := (proofErase Γ m).liftN 1) (a := proofErase Γ q))

end Lean4Lean.VEnv.Strengthening
