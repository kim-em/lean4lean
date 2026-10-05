import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySourceRequests
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationOrigins

/-! Consume actual application queries through their finite output wrappers.
All original argument locations come from applicationOrigin; declaration
seed/header indices and the finite argument spine are kept unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {root : EndpointRef sourceEnv U source rootExpression rootType}
  {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}

noncomputable def RichFamilyPlanConsumption.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments a)
    (action : AtomAction env U registry target a b) :
    RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments b :=
  { result with adapter := result.adapter.comp ((action.raise result.bound).toGeneralAdapter henv hscoped formed) }

noncomputable def RichFamilyPlanConsumption.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (a : Atom n)) :
    RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n+1) (.pad a) := by
  let raised := result.raiseTo henv hscoped formed (result.rank+1) (Nat.le_succ _)
  have bound : n+1 ≤ raised.rank := Nat.succ_le_succ result.bound
  exact { raised with bound := bound, adapter := by simpa only [raiseAtom_pad] using raised.adapter }

noncomputable def RichFamilyPlanConsumption.unpad
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := n+1) (.pad (a : Atom n))) :
    RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments a :=
  { result with bound := Nat.le_trans (Nat.le_succ _) result.bound
                adapter := by simpa only [raiseAtom_pad] using result.adapter }

noncomputable def RichFamilyPlanConsumption.code
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (a : Atom n))
    (action : SortableCodeAction env U registry target relevant (.singleton a) next (.singleton (b : Atom m)))
    (sorted : (Profile.singleton a).HasType (.sort relevant)) :
    RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments b := by
  let N := max result.rank m
  let raised := result.raiseTo henv hscoped formed N (Nat.le_max_left _ _)
  have outputBound : m ≤ raised.rank := Nat.le_max_right _ _
  have program : GeneralNormalProfileAdapter env U registry target
      (.singleton (raiseAtom raised.rank raised.bound a))
      (.singleton (raiseAtom raised.rank outputBound b)) := by
    simpa only [raiseProfile_singleton] using
      (action.atGrade raised.bound outputBound).toGeneralAdapter (Profile.HasType.raise_sort raised.bound sorted)
  have selected : Nonempty (GeneralNormalAtomAdapter env U registry target
      (raiseAtom raised.rank raised.bound a) (raiseAtom raised.rank outputBound b)) := by
    obtain ⟨origin, member, ⟨entry⟩⟩ := program.origin (List.mem_singleton_self _)
    have same := List.mem_singleton.mp member
    subst origin
    exact ⟨entry⟩
  exact { raised with bound := outputBound, adapter := raised.adapter.comp (Classical.choice selected) }

/-- Output code actions and grading are replayed on the consumed plan;
none changes the retained source argument owners. -/
noncomputable def RichFamilyPlanConsumption.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments a)
    (path : GeneralOutputPath env U registry target a b) :
    RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments b := by
  induction path with
  | refl => exact result
  | action path action ih => exact ih.action henv hscoped formed action
  | code path action sorted ih => exact ih.code henv hscoped formed action sorted
  | pad path ih => exact ih.pad henv hscoped formed
  | unpad path ih => exact ih.unpad

/-- The concrete app origin includes both actual source child queries,
original locations and the admission used to consume the retained binder. -/
theorem RichFamilyPlanConsumption.appOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments (n := origin.rank+1) (.fn origin.key origin.output))
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (live : Profile.Live env U registry target origin.rawInput)
    (path : GeneralOutputPath env U registry target origin.output requested) :
    Nonempty (RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature (arguments ++ [a]) requested) := by
  obtain ⟨next⟩ := result.app henv hscoped headerBelow formed (.appArgument origin.location)
    origin.argument (fun i need member => resources i need (List.mem_append_right _ member))
    live origin.arguments origin.admitted
  exact ⟨next.outputPath henv hscoped formed path⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
