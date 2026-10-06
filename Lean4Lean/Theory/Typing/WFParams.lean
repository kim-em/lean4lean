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
