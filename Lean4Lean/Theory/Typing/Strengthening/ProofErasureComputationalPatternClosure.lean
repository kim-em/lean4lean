import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalSingletonPattern
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationPatterns
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongChainTyping

/-! # Computational pattern closure from declaration certificates

The strong induction's computational source typing supplies actual singleton
alignment. Nonzero-source patterns already compute in the ordinary core.
Remaining assumptions are type-fork joining and two declaration certificates;
this is conditional completeness, not a strict reduction of strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
variable [Params] {D : PureObservation.Definitions}

/-- Generic data-domain chains for every registered proposition-source singleton
layout. These are derived from computational typings of the generic constructor
indices, but those typings have not yet been supplied by environment induction. -/
def RegisteredSingletonDomainChains (D : PureObservation.Definitions) : Prop :=
  ∀ {data levels}, RecursorRegistered env data → data.largeTarget = true →
    (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero →
    (∀ l ∈ levels, l.WF univs) → levels.length = data.uvars →
    ∀ S E, data.singletonLayout env levels = some S → data.propElim levels = some E →
      SingletonGenericDataDomainChains D S (data.propParams levels) E

/-- Structural source certificates close all actual patterns under type-fork
joining and declaration certificates. The checks are irrelevant here because
well-formed environments store only the covered empty-check patterns. -/
theorem computational_pattern_closure_of_declarations
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hRigid : ∀ c, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HN : SingletonDeclarationChains D) (HD : RegisteredSingletonDomainChains D) :
    ComputationallyTypedPatternClosure D := by
  intro Γ p r e A levels captures chk hΓ hp hm hJ hR _ _
  obtain ⟨_, _, _, _, data, he, hl, _, _, _⟩ := henv.pats_guarded hp
  have hreg : env.recursorRegistry p.headConst = some data := by
    rw [he, SimplePattern.iota_headConst]; exact hl
  by_cases hz : data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero
  · obtain ⟨_, _, _, _, hAt, _⟩ := recursorRegistry_entry hreg
    exact TypedComputationEq.computational_singleton_pattern heq hs HF hRigid hregistry HN
      hΓ hp hreg hz.1 hz.2 (fun hw hl => HD hAt.registered hz.1 hz.2 hw hl) hm hJ hR.hasType
  · exact TypedComputationEq.pattern_nonzero hs hcon hguard hΓ hp hreg hz hm hJ.hasType

/-- Ordinary derivations produce chains and structural computational typings
once the joining and declaration obligations are supplied. This result does
not assert those obligations, nor that they are strictly smaller than the
original strengthening theorem. -/
theorem computational_typing_of_declarations
    (heq : env.HasCanonicalEq)
    (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HN : SingletonDeclarationChains EnvironmentCore.definitions)
    (HD : RegisteredSingletonDomainChains EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A ∧
      HasTypeC EnvironmentCore.definitions Γ a A ∧ HasTypeC EnvironmentCore.definitions Γ b A :=
  computational_typing_of_defeq heq hcon hqpat
    (computational_pattern_closure_of_declarations heq EnvironmentCore.sound HF
      (fun _ hc => EnvironmentCore.no_rigid hc) hregistry hcon hguard HN HD) hΓ H

end Lean4Lean.VEnv.Strengthening
