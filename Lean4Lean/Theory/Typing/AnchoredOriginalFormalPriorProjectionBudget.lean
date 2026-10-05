import Lean4Lean.Theory.Typing.AnchoredOriginalFormalPriorProjection
import Lean4Lean.Theory.Typing.AnchoredOriginalDerivationRenamingBudget
import Lean4Lean.Theory.Typing.AnchoredOriginalPriorProjectionCaptureBudget

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

@[simp] theorem EndpointRef.dependencyOrigin_weakNOriginal
    (ordered : env.Ordered) (insertion : Ctx.LiftN n k source destination)
    (reference : EndpointRef env U source expression type) :
    (reference.weakNOriginal ordered insertion).dependencyOrigin ordered =
      reference.dependencyOrigin ordered := by
  cases reference <;> simp only [EndpointRef.weakNOriginal,
    EndpointRef.dependencyOrigin, Derivation.dependencyOrigin_weakN]

@[simp] theorem EndpointRef.reflexiveOriginal_dependencyWeight
    (ordered : env.Ordered) (reference : EndpointRef env U source expression type) :
    (reference.reflexiveOriginal.dependencyOrigin ordered).weight =
      2 * (reference.dependencyOrigin ordered).weight + 2 := by
  cases reference <;> simp only [EndpointRef.reflexiveOriginal,
    EndpointRef.dependencyOrigin, Derivation.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;> omega

theorem FamilyFormationRef.dependencyWeight_le
    {major : Derivation env U source left right (mkApps (.const name levels) args)}
    (formation : FamilyFormationRef major) (ordered : env.Ordered) :
    (formation.reference.dependencyOrigin ordered).weight ≤
      (major.dependencyOrigin ordered).weight := by
  have bound := major.typeFormation_dependency_weight_le ordered
  simpa only [formation.exactNode, EndpointState.dependencyOrigin] using bound

theorem formalFirstProjectionOriginal_exposed_weight
    (ordered : env.Ordered)
    (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters 0 sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef env U source fieldType (.sort fieldLevel))
    (major : Derivation env U source sourceMajor expression
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (two : info.nparams = 2) (noIndices : info.nindices = 0) :
    ((formalFirstProjectionOriginal ordered registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed relevance).expose.2.dependencyOrigin ordered).weight ≤
      256 * ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed relevance).dependencyOrigin ordered).weight := by
  have fpositive := (field.dependencyOrigin ordered).weight_pos
  have mpositive := Derivation.dependencyWeight_two_of_nonsort ordered major
    (fun level => mkApps_ne_sort (fn := .const name levels)
      (by intro level same; cases same) (parameters ++ indices))
  have formationBound := major.familyFormationRef.dependencyWeight_le ordered
  have fieldBound : 2 * (field.dependencyOrigin ordered).weight + 2 ≤
      4 * (field.dependencyOrigin ordered).weight := by omega
  have majorBound : 1 + (2 * (major.familyFormationRef.reference.dependencyOrigin ordered).weight + 2) ≤
      4 * (major.dependencyOrigin ordered).weight := by omega
  let header := selectOriginalHeader ordered (ordered.projectionConstructor registered) levelsWF
  let roots := projectionParameterDependencies ordered registered levelsWF
  have scale := firstProjectionDependencyWeight_four_bound
    (header := (header.original.dependencyOrigin header.ordered).weight)
    (equalities := (roots.map fun root => (root.root.original.dependencyOrigin root.ordered).weight).sum)
    registered two noIndices fieldBound majorBound
  dsimp only [header, roots] at scale
  simp only [formalFirstProjectionOriginal, formalMajorVariableOriginal, Derivation.expose, EndpointState.dependencyOrigin,
    EndpointRef.dependencyOrigin, Derivation.dependencyOrigin_castIndices,
    Derivation.dependencyOrigin_weakN, Derivation.dependencyOrigin,
    Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    reserveOrigin_weight, EndpointRef.reflexiveOriginal_dependencyWeight,
    two, noIndices, Nat.add_zero, Nat.max_self] at *
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
