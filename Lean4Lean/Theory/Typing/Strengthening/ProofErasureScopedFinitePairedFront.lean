import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFinitePaired
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTypedSingletonStages
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence

/-! # A finite paired-instantiation front implication and its limitation

The parameter-retaining recursive family turns every proposition conversion
into a common-type diagonal comparison. Even if paired substitution may choose
any finite output stage, loop readout and certificate descent recover the
parameter equation below the inserted binder. Recursive parameter injectivity
uses a diagonal inhabitant, never an inverse weakening theorem.

`RecursiveFunctionInhabitants` separately proves this environment's proposition
front without paired instantiation, by a Curry diagonal and canonical Eq. Thus
the implication below does not establish a new irreducible obligation or show
that the paired law is as difficult as strengthening in arbitrary environments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- In an environment containing the admitted parameter-retaining recursive
family, even stage-zero common paired instantiation with any finite output stage
implies the entire proposition front. This implication is not an equivalence
or a strictness result: `RecursiveProbe.propositionFront` proves the conclusion
independently in this family, using its logical collapse. -/
theorem scopedFinitePaired_implies_propositionFront
    (hc : env.constants c = some (RecursiveProbe.declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveProbe.familyValue c)
      RecursiveProbe.familyType)
    (hstep : ∀ stage, ErasedScopedPrimitiveDescent (Stages stage))
    (hhead : ∀ stage {Δ a b}, Stages stage Δ a b → PrimitiveHead a)
    (H : ScopedFinitePairedInstantiation Stages) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  have HP := RecursiveProbe.recursive hδ hΓ' hP'
  have HD := IsDefEq.appDF (RecursiveProbe.family_typed hc univs (Q :: Γ))
    (HE.of_l henv hΓ' hP')
  obtain ⟨stage, HC⟩ := H.recursive_function_coverage hhead hΓ' HP HD
  have hDP := RecursiveProbe.domain_typed hc hP
  have hDR := RecursiveProbe.domain_typed hc hR
  have Hlift : ScopedCompare (Stages stage) (proofEraseCtx (Q :: Γ)) true
      ((proofErase Γ (RecursiveProbe.domain c P)).liftN 1)
      ((proofErase Γ (RecursiveProbe.domain c R)).liftN 1) := by
    rw [← proofErase_liftN hΓ hΓ' Ctx.LiftN.one hDP,
      ← proofErase_liftN hΓ hΓ' Ctx.LiftN.one hDR]
    exact HC
  have HR := (proofErase_scoped_compare_descend (hstep stage) hΓ hΓ'
    Ctx.LiftN.one rfl hDP hDR Hlift).1
    (IsDefEqU.refl ⟨_, HasType.sort (by trivial)⟩)
  exact RecursiveProbe.parameter_injective hδ hΓ hP hR HR

/-- General singleton primitives retain a constant head at every finite stage,
so the loop annotation readout applies without any normalization hypothesis. -/
theorem erased_scoped_typed_singleton_stage_head : ∀ stage {Δ a b},
    ErasedScopedTypedSingletonStage D stage Δ a b → PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H
    · exact ih H
    · cases H.2
      have aux : ∀ (args : List ProofShape) (f : ProofShape), PrimitiveHead f →
          PrimitiveHead (ProofShape.mkApps f args) := by
        intro args
        induction args with
        | nil => exact fun _ H => H
        | cons a args ih => exact fun f H => ih (.app f a) H
      exact aux _ _ trivial

/-- The finite paired law implies the proposition front in this admitted family
when stages are the actual general singleton stages.
The inputs to the closure law still use only stage zero. -/
theorem scopedTypedSingletonFinitePaired_implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.constants c = some (RecursiveProbe.declaration c).toVConstant)
    (hδ : ∀ Γ, env.IsDefEq univs Γ (.const c []) (RecursiveProbe.familyValue c)
      RecursiveProbe.familyType)
    (H : ScopedFinitePairedInstantiation (ErasedScopedTypedSingletonStage D)) : PropositionFront :=
  scopedFinitePaired_implies_propositionFront hc hδ
    (erased_scoped_typed_singleton_stage_descent heq hs)
    erased_scoped_typed_singleton_stage_head H

omit [Params] in
/-- The implication is realized in an actual well-formed extension preserving
canonical Eq, with all installed ordinary-core equations and arbitrary finite
general singleton stages. It does not require a hypothetical recursive axiom. -/
theorem canonical_finite_paired_implies_front (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (RecursiveProbe.extended base c).HasCanonicalEq ∧
    letI := (RecursiveProbe.extended_wf hbase hfresh).params 0
    ScopedFinitePairedInstantiation (ErasedScopedTypedSingletonStage ErasedCore.definitions) →
      PropositionFront := by
  have heq' := RecursiveProbe.extended_canonicalEq heq hfresh
  refine ⟨heq', ?_⟩
  letI := (RecursiveProbe.extended_wf hbase hfresh).params 0
  intro H
  refine scopedTypedSingletonFinitePaired_implies_propositionFront heq'
    (RegisteredStructure.definitions_sound (PureObservation.Definitions.ofEnv_sound henv))
    (c := c) ?_ ?_ H
  · change (RecursiveProbe.extended base c).constants c = _
    simp [RecursiveProbe.extended, RecursiveProbe.stub, VEnv.addDefEq]
  · exact fun Γ => RecursiveProbe.equation 0 Γ

end Lean4Lean.VEnv.Strengthening
