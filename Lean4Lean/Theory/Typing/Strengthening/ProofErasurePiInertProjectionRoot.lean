import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionTerminal
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRigidSortFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureProjectionResidual

/-! # Root competitors of a type-valued projection selection

At a projection assigned a universe, every primitive of the full staged
language is projection iota or a beta wrapper returning to that projection.
Consequently every root competitor of an enabled selection reduces to the
same selected field using only the ordinary level core. This settles the
root/root peak without native recovery of the selected field. The administrative
expansions of a closed record major also return to the same field. General
compatible computation and forward transport of comparisons remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private rigid_spine_eq_closed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout
variable [Params] {D : Definitions}

/-- Two projection iota primitives at the same raw source select exactly the
same field. Registration uniqueness and the complete constructor spine fix
the index; no typing or reduction confluence is needed. -/
theorem ProofShape.Primitive.projection_deterministic
    (R : Primitive D (.proj s i m) a) (S : Primitive D (.proj s i m) b) : a = b := by
  cases R with
  | projIota hi hl hg =>
    generalize E : ProofShape.proj s i (ProofShape.mkApps (.const _ _) _) = source at S
    cases S with
    | projIota hi' hl' hg' =>
      obtain ⟨rfl, rfl, EM⟩ := ProofShape.proj.inj E
      cases henv.ordered.projections_unique hi hi'
      obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj EM
      exact Option.some.inj (hg.symm.trans hg')
    | delta => cases E

/-- Even the unrestricted ambient stage has only selection and two removable
beta wrappers at a sorted projection root. In particular, native function and
structure eta cannot act there, regardless of guard depth. -/
theorem static_structure_sorted_projection_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (R : ErasedStaticStructureEtaExpansionStage D n Δ (.proj s i m) out) :
    Primitive D (.proj s i m) out ∨
      ConstantExpansion (.proj s i m) out ∨
      ∃ k, k < n ∧ NativeIdentityExpansion (ErasedStaticStructureEtaExpansionStage D k)
        Δ (.proj s i m) out := by
  induction n with
  | zero =>
    rcases R with R | R
    · obtain ⟨info, ls, args, hi, rfl, hl, hg⟩ := erased_level_core_projection_root R
      exact .inl (.projIota hi hl hg)
    · exact .inr (.inl R)
  | succ n ih =>
    rcases R with R | R | R | R | R | R
    · rcases ih R with R | R | ⟨k, hk, R⟩
      · exact .inl R
      · exact .inr (.inl R)
      · exact .inr (.inr ⟨k, by omega, R⟩)
    · obtain ⟨_, R⟩ := R
      generalize E : ProofShape.proj s i m = source at R
      cases R with
      | intro =>
        have H := congrArg ProofShape.constHead E
        simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at H
        cases H
    · cases R
    · exact .inr (.inr ⟨n, by omega, R⟩)
    · exact (HT.no_eta_sort (erased_static_structure_eta_expansion_stage_descent heq hs n) R).elim
    · exact (HT.no_masked_structure (erased_static_structure_eta_expansion_stage_descent heq hs n) R).elim

/-- Every competing root step reduces to the selected field in the ordinary
core. Beta expansion guards are discarded by beta; the selected field needs
no native recovery certificate and may have arbitrary type syntax. -/
theorem static_structure_sorted_projection_root_triangle
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (RI : Primitive D (.proj s i m) field)
    (R : ErasedStaticStructureEtaExpansionStage D n Δ (.proj s i m) out) :
    Compute (ErasedLevelCore D) out field := by
  rcases static_structure_sorted_projection_root heq hs HT R with R | R | ⟨_, _, R⟩
  · exact R.projection_deterministic RI ▸ Compute.refl
  · exact (Compute.beta R.beta_back).trans (.base (.inl (.inl (.inl RI))))
  · exact (Compute.beta R.beta_back).trans (.base (.inl (.inl (.inl RI))))

/-- The same exact triangle holds for a primitive at any finite guard depth.
This does not assume confluence of the expanded language. -/
theorem static_structure_sorted_projection_union_triangle
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (RI : Primitive D (.proj s i m) field)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ (.proj s i m) out) :
    Compute (ErasedLevelCore D) out field := by
  obtain ⟨n, R⟩ := R
  exact static_structure_sorted_projection_root_triangle heq hs HT RI R

/-- Independently chosen primitive competitors, even from different ambient
stages, have a comparison at every Pi-inert stage. Both computations join the
same selected payload; no comparison transitivity is used. -/
theorem pi_inert_sorted_projection_root_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.proj s i m) (.sort u))
    (RI : Primitive D (.proj s i m) field)
    (RL : ErasedStaticStructureEtaExpansionUnion D Δ (.proj s i m) left)
    (RR : ErasedStaticStructureEtaExpansionUnion D Δ (.proj s i m) right) :
    ComputedJointCompare (PiInertStage D n) Δ mode left right :=
  .compute (static_structure_sorted_projection_union_triangle heq hs HT RI RL).in_pi_inert_stage
    (static_structure_sorted_projection_union_triangle heq hs HT RI RR).in_pi_inert_stage (.leaf .refl)

/-- Native structure eta of a closed record returns each type-valued field
to its original projection using ordinary projection iota. Actual uniqueness
identifies the recovered family and its empty parameter/universe spine. The
static field mask cannot erase a type, even if the selected recovery used
arbitrary conversions. -/
theorem proofErase_closed_structure_type_projection_return
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections s info) (hj : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const s []))
    (ht : env.HasType univs Γ (.proj s i m) (.sort u))
    (R : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    Compute (ErasedLevelCore D) (.proj s i out) (.proj s i (proofErase Γ m)) := by
  cases R with
  | intro hi' hx ha hp RN =>
    obtain ⟨A, hmA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hm RN
    obtain ⟨v, hA⟩ := hmA.isType henv hΓ
    have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi) (henv.projectionRigid hi')
      hA (hmA.uniqU henv hΓ hm) EA
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj (ps' := []) EC
    cases henv.ordered.projections_unique hi hi'
    have hc := (StructureReplay.expansion_typed_iff henv hΓ hi (params := []) hp hx hm).2 ha
    have hn : ¬ StructureReplay.ProofField env univs info [] i := by
      intro H
      exact not_isProof_of_sort hΓ ht ((structure_proofField_iff hΓ hi hp hj hc).1 H)
    have RR := ProofShape.nativeStructureOutput_projection (D := D) (ls := []) (m := proofErase Γ m) hi hp hj
    rw [nativeStructureField, if_neg hn] at RR
    exact RR.mono (fun H => .inl (.inl (.inl H)))

/-- Structure eta at the major commutes with an already enabled type-field
selection. After expanding, two ordinary selections reach the exact original
field, without any computation or native evidence at that field. -/
theorem proofErase_closed_structure_type_projection_triangle
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections s info) (hj : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const s []))
    (ht : env.HasType univs Γ (.proj s i m) (.sort u))
    (RI : Primitive D (.proj s i (proofErase Γ m)) field)
    (R : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    Compute (ErasedLevelCore D) (.proj s i out) field :=
  (proofErase_closed_structure_type_projection_return hstep hi hj hΓ hm ht R).trans
    (.base (.inl (.inl (.inl RI))))

/-- All four administrative expansion kinds at a closed record major preserve
the selected type field up to ordinary core computation. Function eta is
impossible at that family; beta wrappers return to the major; structure eta
returns to its original projected field. No new guard is needed after iota. -/
theorem proofErase_closed_projection_major_expansion_triangle
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections s info) (hj : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const s []))
    (ht : env.HasType univs Γ (.proj s i m) (.sort u))
    (RI : Primitive D (.proj s i (proofErase Γ m)) field)
    (R : ConstantExpansion (proofErase Γ m) out ∨
      NativeIdentityExpansion Step (proofEraseCtx Γ) (proofErase Γ m) out ∨
      NativeEtaExpansion Step (proofEraseCtx Γ) (proofErase Γ m) out ∨
      NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) out) :
    Compute (ErasedLevelCore D) (.proj s i out) field := by
  rcases R with R | R | R | R
  · exact (Compute.proj (.beta R.beta_back)).trans (.base (.inl (.inl (.inl RI))))
  · exact (Compute.proj (.beta R.beta_back)).trans (.base (.inl (.inl (.inl RI))))
  · cases R with
    | intro RN SD =>
      obtain ⟨A, B, hmPi, _, _⟩ := proofErase_scoped_recovered_pi_descend
        hstep hΓ hΓ (Ctx.LiftN.zero []) hm
        (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
      obtain ⟨v, hS⟩ := hm.isType henv hΓ
      exact (IsDefEqU.rigidApp_forallE_inv (args := []) (ls := []) henv hΓ (henv.projectionRigid hi)
        hS (hm.uniqU henv hΓ hmPi)).elim
  · exact proofErase_closed_structure_type_projection_triangle hstep hi hj hΓ hm ht RI R

end Lean4Lean.VEnv.Strengthening
