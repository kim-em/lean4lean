import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction

/-! Application expression-query reindexing reconstructs the destination
query at its own original children. Child replies are finite graded source
queries; no result-type certificate or application semantics is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive RichApplicationReplies
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (rightFunction : EndpointState rightEnv U rightSource rightFn (.forallE A B))
    (rightArgument : EndpointState rightEnv U rightSource rightArg A)
    (rightLocals : List Nat) (τ : Subst) (rightAvailable : Valuation) :
    {atoms : List (Atom n)} →
    RichApplicationSeeds root env registry target source locals σ f a footprint atoms → Type where
  | nil : RichApplicationReplies rightFunction rightArgument rightLocals τ rightAvailable .nil
  | cons {origin : RichAppOrigin root env registry target source locals σ f a}
      {path : GeneralOutputPath env U registry target origin.output atom}
      {included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint}
      {rest : RichApplicationSeeds root env registry target source locals σ f a footprint atoms}
      (function : RichGradedResult rightEnv env U registry target rightFunction rightLocals τ
        rightAvailable (Profile.fn origin.key origin.output))
      (argument : RichGradedResult rightEnv env U registry target rightArgument rightLocals τ
        rightAvailable origin.rawInput)
      (tail : RichApplicationReplies rightFunction rightArgument rightLocals τ rightAvailable rest) :
      RichApplicationReplies rightFunction rightArgument rightLocals τ rightAvailable
        (.cons origin path included rest)

/-- One original application output is rebuilt through its complete finite
code-action path, even when the destination typing uses different domains. -/
theorem RichAppOrigin.reindexApplication
    {A B : VExpr} {u v : VLevel}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {rightFunction : EndpointState rightEnv U rightSource rightFn (.forallE A B)}
    {rightArgument : EndpointState rightEnv U rightSource rightArg A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : rightAvailable.AtomClosed)
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (path : GeneralOutputPath env U registry target origin.output atom)
    (sorted : (Profile.singleton atom).HasType (.sort relevant))
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (argumentEq : a.subst σ = rightArg.subst τ)
    (function : RichGradedResult rightEnv env U registry target rightFunction rightLocals τ
      rightAvailable (Profile.fn origin.key origin.output))
    (argument : RichGradedResult rightEnv env U registry target rightArgument rightLocals τ
      rightAvailable origin.rawInput) :
    ∃ required, Nonempty (RichCert rightEnv env U registry target
      (.app hu hv domain codomain rightFunction rightArgument result) rightLocals τ relevant
      (.singleton atom) required) ∧ required.Available rightAvailable := by
  obtain ⟨flag, inputSorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  have admitted : Admitted env U registry target origin.key (rightArg.subst τ) (rightArg.subst τ) :=
    argumentEq ▸ origin.admitted
  obtain ⟨application⟩ := RichGradedResult.app henv hscoped formed closed domain codomain result hu hv
    function argument origin.arguments admitted
  obtain ⟨_, ⟨certificate⟩, resources⟩ := application.code henv inputSorted
  exact certificate.codeAction action resources

open private typeSubset from Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationReplay

/-- The whole application query is rebuilt from the exact finite original
seed ledger and its child replies. Empty requests require no recursive calls. -/
theorem RichApplicationReplies.reindex
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {rightFunction : EndpointState rightEnv U rightSource rightFn (.forallE A B)}
    {rightArgument : EndpointState rightEnv U rightSource rightArg A}
    {seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : rightAvailable.AtomClosed)
    (replies : RichApplicationReplies rightFunction rightArgument rightLocals τ rightAvailable seeds)
    (sorted : (Profile.mk atoms).HasType (.sort relevant))
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (argumentEq : a.subst σ = rightArg.subst τ) :
    ∃ required, Nonempty (RichCert rightEnv env U registry target
      (.app hu hv domain codomain rightFunction rightArgument result) rightLocals τ relevant
      (.mk atoms) required) ∧ required.Available rightAvailable := by
  induction replies with
  | nil => exact ⟨[], ⟨.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)))⟩,
      fun _ _ h => nomatch h⟩
  | cons fn arg tail ih =>
    rename_i footprint atoms origin path included rest
    obtain ⟨_, ⟨head⟩, headResources⟩ := origin.reindexApplication henv hscoped formed closed path
      (sorted.singleton_of_mem List.mem_cons_self) domain codomain result hu hv argumentEq fn arg
    obtain ⟨_, ⟨tail⟩, tailResources⟩ := ih henv hscoped formed
      (typeSubset (fun _ h => List.mem_cons_of_mem _ h) sorted) argumentEq
    exact ⟨_, ⟨.union head tail⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (headResources i need) (tailResources i need)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
