import Lean4Lean.Theory.Typing.ShapeModel.EnvSigHead

/-!
# Head separation of a well-formed environment from the validity of its rules

`headSeparation_of_valid`: for the semantic signature `envSig env` of a well-formed environment
(`EnvSig.lean`), head separation follows from three facts about the model, which are what the
milestone M4c proves: the semantic form of the structure types (`FamTypeSem`), the validity of
the stored equations (`ExtraValid`) and the validity of the eliminator rules (`ElimValidIn`).
Everything else is discharged here: coherence (`envSig_coherent_of_wf`), the environment facts
(`envSig_envFactsIn_of_wf`), and the head facts (`envSig_headFacts`), and then
`headSeparation_of_shapeModel_of_wf` (`Head.lean`) applies.
-/

namespace Lean4Lean.ShapeModel

variable {env : VEnv}

theorem headSeparation_of_valid (H : env.WF)
    (hsem : ∀ {s info}, env.projections s info → FamTypeSem env s info)
    (hextra : ∀ df, env.defeqs df → letI := envSig env; ExtraValid env df)
    (helim : letI := envSig env; ElimValidIn env env) :
    env.HeadSeparation := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  exact headSeparation_of_shapeModel_of_wf H (envSig_envFactsIn_of_wf H VEnv.LE.rfl hsem)
    (envSig_headFacts H) hextra helim

end Lean4Lean.ShapeModel
