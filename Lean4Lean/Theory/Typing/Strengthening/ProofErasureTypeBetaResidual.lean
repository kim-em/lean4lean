import Lean4Lean.Theory.Typing.Strengthening.ProofErasureForwardBinderFork

/-! # Type instantiation as a beta fork

Computing a type below a binder and then instantiating it forms one branch
of a typed beta fork. Contracting beta first forms the other. This construction
needs no native certificate for the argument and no substitution law for the
primitive relation. Joining this particular fork is an explicit open premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Any computation of a type under a binder supplies a typed beta fork after
an arbitrary typed argument is supplied. The second branch computes under the
lambda before beta; it does not transport primitive guards by substitution. -/
theorem type_instantiation_compute_peak
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (hx : env.HasType univs Γ x A)
    (RB : ScopedCompute Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B) out) :
    env.HasType univs Γ (.app (.lam A B) x) (.sort v) ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.app (.lam A B) x))
        (proofErase Γ (B.inst x)) ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.app (.lam A B) x))
        (out.inst (proofErase Γ x)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hf := HasType.lam hA hB
  have ht : env.HasType univs Γ (.app (.lam A B) x) (.sort v) := .app hf hx
  have EF : proofErase Γ (.lam A B) = .lam (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EE : proofErase Γ (.app (.lam A B) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A B) x) = .app _ _ from if_neg (not_isProof_of_sort hΓ ht), EF]
  have EI := proofErase_instN hΓA hx Ctx.InstN.zero hB
  refine ⟨ht, ?_, ?_⟩
  · rw [EE, EI]
    exact .beta .beta
  · rw [EE]
    have RB' : ScopedCompute Step (proofErase Γ A :: proofEraseCtx Γ)
        (proofErase (A :: Γ) B) out := by simpa only [proofEraseCtx] using RB
    exact (ScopedCompute.app (ScopedCompute.lam .refl RB') .refl).trans (.beta .beta)

/-- The open type-instantiation obligation: the original instantiated type
and an instantiated computed body have a common reduct. Only one type-valued
beta fork is requested. No proof of this obligation or native image coverage
is included in the definition. -/
def TypeInstantiationJoin (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A B x u v out}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ A (.sort u) → env.HasType univs (A :: Γ) B (.sort v) →
    env.HasType univs Γ x A →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) out →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) shared

/-- Joining forks at typed types suffices for the explicit instantiation
obligation. The only fork invoked is rooted at the type-valued beta redex
constructed above. Neither branch uses an argument's native recovery. -/
theorem type_instantiation_join_of_type_forks
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared) :
    TypeInstantiationJoin D := by
  intro Γ A B x u v out hΓ hA hB hx RB
  obtain ⟨ht, RL, RR⟩ := type_instantiation_compute_peak hΓ hA hB hx RB
  exact HF hΓ ht RL RR

/-- Forward native binder transport already implies all type forks, and
therefore supplies this weaker type-instantiation joining consequence. No
converse or strictly smaller sufficient strengthening claim is made here. -/
theorem NativeForwardBinder.type_instantiation_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : NativeForwardBinder D) : TypeInstantiationJoin D :=
  type_instantiation_join_of_type_forks (HF.type_fork heq hs)

end Lean4Lean.VEnv.Strengthening
