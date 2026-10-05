import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFundedFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidFamilyConsumption

/-! The caller consumption retains either genuine telescope history or the
actual finite rigid input. Both alternatives compute the same request-level
result; callers never need to assume which declaration shape was stored. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private raiseAtom_twice from Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyConsumption
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

inductive WorldFamilyProgramConsumption
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (parent : World strata.rules.length)
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (requested : Atom n) : Type where
  | telescope
      (seed : WorldFundedFamilyHeaderAt controls U registry target name levels frontier parent)
      (cursor : RichFamilyPlanConsumption root (seed.header.origin.familyHeader seed.header.seedWF).reference
        env registry target locals σ available name seed.header.seed seed.header.signature arguments requested)
      (queries : cursor.observed.Queries (ControlledFamilyQuery controls frontier)) :
      WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
        name levels arguments requested
  | rigid (seed : WorldRigidFamilyProgram strata U registry target name levels frontier)
      (cursor : WorldRigidFamilyConsumption controls frontier root registry target locals σ available
        name seed.leaf.frozenLevels arguments requested) :
      WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
        name levels arguments requested

section
variable {env : VEnv} {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U source rootExpression rootType}

noncomputable def WorldFamilyProgramAt.consume
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (seed : WorldFamilyProgramAt controls U registry target name levels frontier parent)
    (path : GeneralOutputPath env U registry target seed.atom requested) :
    WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels [] requested := by
  cases seed with
  | telescope seed =>
    let cursor := seed.header.atCaller (locals := locals) (σ := σ) (available := available) root
    exact .telescope seed (cursor.outputPath henv hscoped formed path)
      (cursor.outputPath_queries henv hscoped formed path _ trivial)
  | rigid seed =>
    let cursor := WorldRigidFamilyConsumption.bare (controls := controls) (frontier := frontier)
      (root := root) (locals := locals) (σ := σ) (available := available)
      (name := name) (levels := seed.leaf.frozenLevels) seed.leaf.plan seed.leaf.input.ready
    exact .rigid seed (cursor.outputPath henv hscoped formed path)

noncomputable def WorldFamilyProgramConsumption.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (consumed : WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments requested)
    (path : GeneralOutputPath env U registry target requested next) :
    WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments next := by
  cases consumed with
  | telescope seed cursor queries =>
    exact .telescope seed (cursor.outputPath henv hscoped formed path)
      (cursor.outputPath_queries henv hscoped formed path _ queries)
  | rigid seed cursor => exact .rigid seed (cursor.outputPath henv hscoped formed path)

noncomputable def WorldFamilyProgramConsumption.adaptRequest
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {requested : Atom n} {next : Atom k}
    (consumed : WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments requested)
    (bound : k ≤ n)
    (adapter : GeneralNormalAtomAdapter env U registry target requested (raiseAtom n bound next)) :
    WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments next := by
  cases consumed with
  | telescope seed cursor queries =>
    let selected : RichFamilyPlanConsumption root (seed.header.origin.familyHeader seed.header.seedWF).reference
        env registry target locals σ available name seed.header.seed seed.header.signature arguments next :=
      { cursor with bound := Nat.le_trans bound cursor.bound
                    adapter := by simpa only [raiseAtom_twice] using
                      cursor.adapter.comp (adapter.raise henv hscoped formed cursor.bound) }
    exact .telescope seed selected queries
  | rigid seed cursor => exact .rigid seed (cursor.adaptRequest henv hscoped formed bound adapter)

theorem WorldFamilyProgramConsumption.appOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (consumed : WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments (n := origin.rank+1) (.fn origin.key origin.output))
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (live : Profile.Live env U registry target origin.rawInput)
    (path : GeneralOutputPath env U registry target origin.output requested)
    (argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument)) :
    Nonempty (WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels (arguments ++ [a]) requested) := by
  cases consumed with
  | telescope seed cursor queries =>
    obtain ⟨next, nextQueries⟩ := cursor.appOriginPreserving henv hscoped
      (seed.header.origin.sourceBelow.trans seed.header.below) formed origin resources live path
      (property := ControlledFamilyQuery controls frontier)
      (fun _ bound controlled => controlled.elim (fun value => value.raise bound)) queries ⟨argumentReady⟩
    exact ⟨.telescope seed next nextQueries⟩
  | rigid seed cursor =>
    obtain ⟨next⟩ := cursor.app henv hscoped formed (.appArgument origin.location) origin.admitted
    exact ⟨.rigid seed (next.outputPath henv hscoped formed path)⟩

theorem WorldFamilyProgramConsumption.familyRequests
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (consumed : WorldFamilyProgramConsumption controls frontier parent root registry target locals σ available
      name levels arguments (n := n+1) (.family demand)) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels arguments demand := by
  cases consumed with
  | telescope seed cursor queries =>
    have requests := cursor.familyWorldRequests henv hscoped formed queries
    refine ⟨requests.1, ?_, requests.2.2⟩
    exact Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      requests.2.1 seed.header.equivalent
  | rigid seed cursor =>
    have requests := cursor.familyRequests henv hscoped formed
    refine ⟨requests.1, ?_, requests.2.2⟩
    exact Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
      requests.2.1 seed.leaf.input.frozenLevelsEq

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
