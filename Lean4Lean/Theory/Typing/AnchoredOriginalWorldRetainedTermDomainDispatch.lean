import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDomainWitness
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiLeafSelection
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermChargedWitness

/-! Domain dispatch retains the actual child program and pending action in a
typed edge, including legacy Pi leaves whose row table is empty. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldLegacyPiLeafSelection.enterTermDomainWitness
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput)
    {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
    (expressionEq : before.expression = .forallE A B)
    {domainNode : EndpointState before.sourceEnv U before.source A (.sort u)}
    {bodyNode : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
    {budget : WorldPiDomainBudget strata}
    {n : Nat} {support : Profile n} {rows : List (Key n × Profile n)} {atom : Atom n}
    (selection : WorldLegacyPiLeafSelection env budget U registry target before.locals before.left A B before.available
      sizeBudget before.programSize (show Atom (n+1) from .pi nextDomain nextBody support rows))
    (route : PrefixRoute before.sourceEnv U before.source (.forallE A B)
      (before.node.cast expressionEq rfl) (.pi hu hv domainNode bodyNode))
    (within : WithinAbove before.controls.cutoff before.controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (worlds : budget.worlds ⊆ before.annotation.certificate.worlds)
    (depth : ∀ policy, budget.depth policy ≤ before.program.certificate.headDepth policy)
    (inputPath : GeneralOutputPath env U registry target before.selected
      (show Atom (n+1) from .pi nextDomain nextBody support rows))
    (member : atom ∈ support.atoms)
    (continuation : RetainedTermDemand env U registry target goal goalOutput A atom)
    (readback : continuation.readback before.right = before.demand.readback before.right)
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      (expressionEq ▸ before.demand) (.domain inputPath member continuation)) :
    ∃ next : RetainedTermProgramState env U registry target strata P frontier goal goalOutput,
      next.programSize < before.programSize ∧ Nonempty (RetainedTermDomainTransitionWitness before next) := by
  rcases selection with ⟨⟨rank, original, leaf, path, syntaxBound⟩, annotation, included, smaller, childDepth⟩
  dsimp only at annotation included smaller childDepth
  cases leaf with
  | plain domain guard rows resources =>
    cases annotation with
    | plain domainAnnotation rowsAnnotation =>
      obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
      apply enterTermDomainProgramWitness before expressionEq route (.legacy (.plain domain)) (.legacy (.plain domainAnnotation))
        (by
          intro control active
          apply Nat.le_trans _ (within control active)
          simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth,
            LegacyRowBody.certificate, SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (childDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
        (fun world member => sponsored world (included (List.mem_append_left _ member)))
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun world hm => worlds (included (List.mem_append_left _ hm)))
        (by
          intro policy
          apply Nat.le_trans _ (depth policy)
          simpa only [RetainedTypedProgram.certificate, RichCert.headDepth, LegacyRowBody.certificate,
            SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (childDepth policy))
        (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) smaller) pending inputPath member continuation readback normalized
  | sortable domain guard rows resources =>
    cases annotation with
    | sortable domainAnnotation rowsAnnotation =>
      obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain path
      apply enterTermDomainProgramWitness before expressionEq route (.legacy (.sortable domain)) (.legacy (.sortable domainAnnotation))
        (by
          intro control active
          apply Nat.le_trans _ (within control active)
          simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth,
            LegacyRowBody.certificate, SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (childDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
        (fun world member => sponsored world (included (List.mem_append_left _ member)))
        (fun i need member => resources i need (List.mem_append_left _ member))
        (fun world hm => worlds (included (List.mem_append_left _ hm)))
        (by
          intro policy
          apply Nat.le_trans _ (depth policy)
          simpa only [RetainedTypedProgram.certificate, RichCert.headDepth, LegacyRowBody.certificate,
            SortableCert.headDepth, LegacyPiLeaf.headDepth] using
            Nat.le_trans (Nat.le_max_left _ _) (childDepth policy))
        (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) smaller) pending inputPath member continuation readback normalized

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
