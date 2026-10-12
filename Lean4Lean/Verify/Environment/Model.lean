import Lean4Lean.Verify.Environment.Blocks

/-!
# The environment model

The model of a kernel environment the checker verification is stated against: one abstract
environment per safety level (`VEnvs`), each related to the kernel environment by the
translation `TrEnv`, with the primitives, and with every inductive constant belonging to a
complete installed block (`InstalledBlocks`, `Verify/Environment/Blocks.lean`).  `VEnvAt` is the
view at one safety level.  The facts the checker reads about inductive constants are
projections of the invariant, stated here as theorems.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

structure VEnvs where
  venv : DefinitionSafety → VEnv

/-- The translation part of the well-formedness invariant of the checker's environment model:
`VEnvs.WF` without context strengthening. -/
structure VEnvs.WFCore (env : Environment) (ves : VEnvs) where
  tr : TrEnv safety env (ves.venv safety)
  hasPrimitives : VEnv.HasPrimitives (ves.venv safety)
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  /-- Every inductive header, constructor and recursor belongs to a complete installed
  block (`InstalledBlocks`). -/
  blocks : InstalledBlocks safety env (ves.venv safety) .complete
  mono : safety ≤ safety' → ves.venv safety' ≤ ves.venv safety

/-- The well-formedness invariant of the checker's environment model. Every checked declaration
preserves it (`addDecl.WF`). Besides the translation (`VEnvs.WFCore`) it records context
strengthening in every well-formed extension of the model (`VEnv.StrengtheningAbove`): the
checker's caches and equivalence manager persist across binders, and their facts are moved out
of a binder's scope with it. An environment with canonical `Eq` has it
(`VEnvs.WFCore.toWF_of_canonicalEq`, on the open proof `IsDefEqU.weakN_iff`). -/
structure VEnvs.WF (env : Environment) (ves : VEnvs) extends VEnvs.WFCore env ves where
  strengthening : (ves.venv safety).StrengtheningAbove

/-- Canonical `Eq` supplies the strengthening field of the invariant. -/
theorem VEnvs.WFCore.toWF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) : ves.WF env :=
  { wf with strengthening := fun {safety} => (heq safety).strengtheningAbove }

namespace VEnvs.WF
variable {env : Environment} {ves : VEnvs}

theorem inductivesClosed (wf : ves.WF env) : VerifyInductive.MutualInductivesClosed env :=
  (wf.blocks (safety := .unsafe)).mutualInductivesClosed (by decide)

theorem constructorOwners (wf : ves.WF env) :
    VerifyInductive.ConstructorOwnersPresent env :=
  (wf.blocks (safety := .unsafe)).constructorOwnersPresent

theorem constructorParameterAlignment (wf : ves.WF env) {safety : DefinitionSafety} :
    VerifyInductive.ConstructorParameterAlignment safety env (ves.venv safety) :=
  wf.blocks.constructorParameterAlignment

/-- Every constructor a header lists is present. -/
theorem listedConstructorsPresent (wf : ves.WF env) :
    VerifyInductive.ListedConstructorsPresent env :=
  (wf.blocks (safety := .unsafe)).listedConstructorsPresent (by decide)

theorem inductiveConstructorsCoherent (wf : ves.WF env) :
    VerifyInductive.InductiveConstructorsCoherent env :=
  (wf.blocks (safety := .unsafe)).inductiveConstructorsCoherent (by decide)

theorem projectionRegistryCoherent (wf : ves.WF env) {safety : DefinitionSafety} :
    ProjectionRegistryCoherent safety env.constants (ves.venv safety) :=
  wf.blocks.projectionRegistryCoherent (wf.tr (safety := safety)).map_wf

/-- Every visible kernel family is a family of an installed declaration. -/
theorem inductFamiliesInstalled (wf : ves.WF env) {safety : DefinitionSafety}
    (hfind : env.find? familyName = some (.inductInfo familyInfo))
    (hvisible : safety ≤ (ConstantInfo.inductInfo familyInfo).safety) :
    familyName = familyInfo.name ∧
      Nonempty (InductFamilyInstalledAt (ves.venv safety) familyInfo) :=
  wf.blocks.familyInstalled hfind hvisible

end VEnvs.WF

/-- Assemble a `VEnvs` from a pointwise existential. `DefinitionSafety` has three elements, so
this is a finite case split rather than an appeal to choice -- the name records what it replaces. -/
theorem VEnvs.axiom_of_choice {P : DefinitionSafety → VEnv → Prop} (H : ∀ sf, ∃ x, P sf x) :
    ∃ x : VEnvs, ∀ sf, P sf (x.venv sf) := by
  have ⟨x1, _⟩ := H .safe; have ⟨x2, _⟩ := H .partial; have ⟨x3, _⟩ := H .unsafe
  exact ⟨⟨fun | .safe => x1 | .partial => x2 | .unsafe => x3⟩, by rintro ⟨⟩ <;> assumption⟩

/-- Assemble a `VEnvs` from a pointwise existential by case analysis on the
three safety levels. -/
theorem VEnvs.ofPointwiseExists {P : DefinitionSafety → VEnv → Prop}
    (H : ∀ sf, ∃ x, P sf x) :
    ∃ x : VEnvs, ∀ sf, P sf (x.venv sf) := by
  have ⟨x1, _⟩ := H .safe; have ⟨x2, _⟩ := H .partial; have ⟨x3, _⟩ := H .unsafe
  exact ⟨⟨fun | .safe => x1 | .partial => x2 | .unsafe => x3⟩, by rintro ⟨⟩ <;> assumption⟩

/-- The type checker's model of `env` at one safety level: the translation, the primitives,
the installed blocks of every inductive constant (all complete), and context strengthening. -/
structure VEnvAt (env : Environment) (safety : DefinitionSafety) (venv : VEnv) : Prop where
  tr : TrEnv safety env venv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  blocks : InstalledBlocks safety env venv .complete
  strengthening : venv.StrengtheningAbove

/-- Recursor coherence of a single-level model. -/
theorem VEnvAt.recursors (wf : VEnvAt env safety venv) :
    RecursorEnvCoherent safety env.constants venv :=
  wf.blocks.recursorEnvCoherent wf.tr.map_wf wf.tr.equationHeads

/-- Quotient coherence of a single-level model, derived from its translation. -/
theorem VEnvAt.quot (wf : VEnvAt env safety venv) (hq : env.quotInit = true) :
    QuotEnvCoherent env.constants venv :=
  wf.tr.quotEnvCoherent hq

/-- The checking invariant of a single-level model. -/
theorem VEnvAt.toCheckingValid (wf : VEnvAt env safety venv) :
    CheckingEnv.Valid safety env venv :=
  wf.tr.toCheckingValid wf.hasPrimitives wf.safePrimitives wf.blocks

theorem VEnvs.WF.toVEnvAt {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) : VEnvAt env safety (ves.venv safety) where
  tr := wf.tr
  hasPrimitives := wf.hasPrimitives
  safePrimitives := wf.safePrimitives
  blocks := wf.blocks
  strengthening := wf.strengthening

/-- The checking invariant at one safety level of a well-formed model. -/
theorem VEnvs.WF.toCheckingValid {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) : CheckingEnv.Valid safety env (ves.venv safety) :=
  (wf.toVEnvAt safety).toCheckingValid

end Lean4Lean
