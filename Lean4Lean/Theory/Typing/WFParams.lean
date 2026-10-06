import Lean4Lean.Theory.Typing.ConcreteParams
import Lean4Lean.Theory.Typing.NativeIotaSoundness
import Lean4Lean.Theory.Typing.StructureMajorProvenance
import Lean4Lean.Theory.Typing.EliminatorCoherence

/-! The `Params` instance of a well-formed environment with coherent
eliminator registrations. Every field is a theorem. -/

namespace Lean4Lean.VEnv
open InductiveSignature CanonicalDataHead

/-- The chosen declaration history and canonical registry of a well-formed
environment. -/
noncomputable def WF.registry {env : VEnv} (henv : env.WF) : Registry :=
  Classical.choose (Classical.choose_spec henv.canonicalRegistry)

theorem WF.registry_contract {env : VEnv} (henv : env.WF) :
    henv.registry.EnvironmentContract env (Classical.choose henv.canonicalRegistry) :=
  Classical.choose_spec (Classical.choose_spec henv.canonicalRegistry)

/-- The confluence parameters of a well-formed environment at universe
bound `U`. Only the case-schema structure fact needs `EliminatorsCoherent`. -/
@[instance_reducible] noncomputable def WF.params {env : VEnv} (henv : env.WF) (hcoh : env.EliminatorsCoherent)
    (U : Nat) : Params :=
  Params.ofRegistry henv henv.registry_contract U
    (fun hΓ h hm ht => NativeIotaPattern.sound henv hΓ
      (fun _ _ h => let ⟨a, b, _⟩ := henv.registry_contract.natives _ _ h; ⟨a, b⟩) h hm ht)
    (fun h hΓ hl hs hlen => ConcretePattern.struct_major henv henv.registry_contract h hΓ hl hs hlen)
    (fun h hl hcc hm hm' hps hps' =>
      ConcretePattern.iota_params henv henv.registry_contract h hl hcc hm hm' hps hps')
    (fun hm hΓ hl hs => MatchedCaseStep.struct_major henv hcoh hm hΓ hl hs)

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv
open InductiveSignature CanonicalDataHead

/-- Zero-source large-elimination coverage for the concrete instance: every
native singleton equation, at a universe specialization where the native iota
guard fails, is joinable. -/
def WF.SingletonCoverage {env : VEnv} (henv : env.WF) (hcoh : env.EliminatorsCoherent) (U : Nat) :
    Prop :=
  letI := henv.params hcoh U
  ∀ {Γ : List VExpr} {data : NativeRecursorData}
    {index : Fin data.schema.signature.constructors.size} {equation : VDefEq}
    {levels : List VLevel}, OnCtx Γ (env.IsType U) →
    henv.registry.natives data.name = some data → NativeRecursorRegistered env data →
    data.schema.signature.constructors[index].owner = data.owner →
    data.equation index = some equation →
    (∀ level ∈ levels, level.WF U) → levels.length = equation.uvars →
    data.largeTarget = true →
    (data.schema.sourceLevel data.owner data.levels).inst levels ≈ .zero →
    ∃ left right, FullReduction Γ (equation.lhs.instL levels) left ∧
      FullReduction Γ (equation.rhs.instL levels) right ∧ NormalEq Γ left right

theorem WF.equationCoverage {env : VEnv} (henv : env.WF) (hcoh : env.EliminatorsCoherent)
    (hzero : henv.SingletonCoverage hcoh U) :
    @FullEquationCoverage (henv.params hcoh U) := by
  letI := henv.params hcoh U
  refine ⟨fun hΓ hdf hw hl => equation_covered_of_registry henv.registry_contract
    (fun h => .inl h) (fun h => .inr (.inl ⟨h, .intro (henv.registry_contract.quotientRegistered h)⟩))
    (fun h => .inr (.inr h)) rfl (fun hΓ' hl' hr' ho' hg' hw' hlen' h1 h2 =>
      hzero hΓ' hl' hr' ho' hg' hw' hlen' h1 h2) hΓ hdf hw hl⟩

/-- Confluence of definitional equality in a well-formed environment with
coherent eliminator registrations, given zero-source singleton coverage. -/
theorem WF.church_rosser_of_singletonCoverage {env : VEnv} (henv : env.WF)
    (hcoh : env.EliminatorsCoherent) (hzero : henv.SingletonCoverage hcoh U)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params hcoh U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂' := by
  letI := henv.params hcoh U
  haveI := henv.equationCoverage hcoh hzero
  obtain ⟨-, -, h⟩ := IsDefEq.full_church_rosser (Γ := Γ) hΓ H
  exact h

end Lean4Lean.VEnv
