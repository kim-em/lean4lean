import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonJoinedGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecursiveTransport

/-! # General singleton/core squares with recursive family certificates

Rigid index spines and lambda bodies may contain typed eta leaves. The old
certificate transports to a scoped guard for the new generated program, so
both prefix contractions remain certified at stage one.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open PureObservation
open private core_arguments_replay from Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonCoreResidual
variable [Params]

/-- Family comparison using the recursive core fragment, including eta at
nested rigid indices and finite computations before recursive comparison. -/
def CoreRecursiveFamily (Γ : List VExpr) (a b : VExpr) : Prop :=
  ErasedCore.RecursiveGuard true (proofErase Γ a) (proofErase Γ b)

/-- A recursive family certificate supplies a stage-zero scoped guard. -/
theorem CoreRecursiveFamily.scoped
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : CoreRecursiveFamily Γ a b) :
    GuardedSingleton.ScopedFamilyComparison (fun _ => ErasedCore.Step) Γ a b :=
  (H.forward hcon .refl .refl).scoped (fun H => .base H)

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- Recursive family certificates survive core argument computation, including
conversion to the newly generated residual telescope. The resulting guard uses
only stage-zero computation; it need not belong to the input fragment. -/
theorem Valid.recursive_guard_core (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (hg' : C.data.singletonUnfolding env univs C.levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HA : List.Forall₂ (PatternCompute ErasedCore.definitions) args args')
    (HG : GuardedSingleton.FamilyGuard CoreRecursiveFamily
      Γ C.data C.levels args program C.layout C.elim) :
    GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison (fun _ => ErasedCore.Step))
      Γ C.data C.levels args' program' C.layout C.elim := by
  have H := V.family_core_transport heq hcon
    (Cmp := ErasedCore.RecursiveGuard true)
    (Cmp' := ProofShape.RawCheckedCompare ErasedCore.Step true)
    (fun _ _ _ H RA RB => H.forward hcon RA RB) hΓ hg hg' ht HA HG
  exact H.scoped (fun H => .base H)

/-- General singleton unfolding with a recursive family guard commutes with
arbitrary finite raw core computation of all supplied arguments. Both prefix
edges are certified at stage one, and both horizontal edges use only core
computation. New original arguments and the checked generated output are
reconstructed; whole-proof sources are included by forward erasure. -/
theorem Valid.recursive_prefix_core_peak (V : C.Valid) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args))
    (HG : GuardedSingleton.FamilyGuard CoreRecursiveFamily
      Γ C.data C.levels args program C.layout C.elim)
    (HA : List.Forall₂ (ProofShape.Compute ErasedCore.Step) (args.map (proofErase Γ)) rawArgs) :
    ∃ args' program', args'.map (proofErase Γ) = rawArgs ∧
      C.data.singletonUnfolding env univs C.levels args' = some program' ∧
      ProofShape.Compute ErasedCore.Step
        (proofErase Γ (mkApps (.const C.data.name C.levels) args))
        (proofErase Γ (mkApps (.const C.data.name C.levels) args')) ∧
      ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage ErasedCore.definitions 1)
        (proofEraseCtx Γ) (proofErase Γ (mkApps (.const C.data.name C.levels) args))
        (proofErase Γ program.rhs) ∧
      ProofShape.ScopedCompute (ErasedScopedTypedSingletonStage ErasedCore.definitions 1)
        (proofEraseCtx Γ) (proofErase Γ (mkApps (.const C.data.name C.levels) args'))
        (proofErase Γ program'.rhs) ∧
      ProofShape.Compute ErasedCore.Step (proofErase Γ program.rhs) (proofErase Γ program'.rhs) := by
  have hs : ErasedCore.definitions.Sound env univs :=
    RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have hstep : ErasedScopedPrimitiveDescent
      (ErasedScopedTypedSingletonStage ErasedCore.definitions 0) :=
    erased_scoped_typed_singleton_stage_descent heq hs 0
  have HGS : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison
        (ErasedScopedTypedSingletonStage ErasedCore.definitions 0))
      Γ C.data C.levels args program C.layout C.elim := HG.scoped hcon
  have HC := V.check heq hstep hΓ hg ht HGS
  obtain ⟨args', Hargs, Eargs⟩ := core_arguments_replay hs hΓ
    (mkApps_arguments_wf henv hΓ ht).2 HA
  obtain ⟨program', hg'⟩ := RecursorData.singletonUnfolding_sameArity hg Hargs.length_eq.symm
  have HG' := V.recursive_guard_core heq hcon hΓ hg hg' ht Hargs HG
  have HGS' : GuardedSingleton.FamilyGuard
      (GuardedSingleton.ScopedFamilyComparison
        (ErasedScopedTypedSingletonStage ErasedCore.definitions 0))
      Γ C.data C.levels args' program' C.layout C.elim := HG'
  have Rsource : PatternCompute ErasedCore.definitions
      (mkApps (.const C.data.name C.levels) args)
      (mkApps (.const C.data.name C.levels) args') :=
    patternCompute_congrRel.mkApps (Γ := Γ) .refl Hargs
  have ht' : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args') :=
    ⟨_, (Rsource.simAt hs hΓ _ HC.source_typed).hasType.2⟩
  have HC' := V.check heq hstep hΓ hg' ht' HGS'
  have HP : PrefixUnfold env univs recursorData Γ C.data.name C.levels args program.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC
  have HP' : PrefixUnfold env univs recursorData Γ C.data.name C.levels args' program'.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg' HC'
  have Rout := singleton_program_congr patternCompute_congrRel HP HP' (Γ := Γ) Hargs
  refine ⟨args', program', Eargs, hg',
    proofErase_pattern_compute_forward hs hcon hΓ HC.source_typed Rsource, ?_, ?_,
    proofErase_pattern_compute_forward hs hcon hΓ (HC.defeq henv hΓ).hasType.2 Rout⟩
  · exact proofErase_scoped_typed_singleton_stage_forward heq hΓ V.lookup V.registered
      V.large V.zero V.levels_wf V.recType_eq V.layout_eq V.elim_eq hg HC HGS
  · exact proofErase_scoped_typed_singleton_stage_forward heq hΓ V.lookup V.registered
      V.large V.zero V.levels_wf V.recType_eq V.layout_eq V.elim_eq hg' HC' HGS'


end SingletonPrefixCode
end Lean4Lean.VEnv.Strengthening
