import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionParameters
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterReserve

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- One actual earlier declaration proof with its original open context.
The count bound is uniform in the final Ordered witness, not in universes. -/
structure SelectedParameterDependency (env : VEnv) (U : Nat) where
  source : VEnv
  ordered : source.Ordered
  root : ParameterEqualityRoot source U
  smaller : ∀ final : env.Ordered, ordered.constantCount < final.constantCount

noncomputable def OriginalProjectionParameters.baseDependency
    (packet : OriginalProjectionParameters env U name info levels)
    (root : ParameterEqualityRoot packet.origin.base U) : SelectedParameterDependency env U :=
  ⟨packet.origin.base, packet.origin.baseOrdered, root, packet.origin.base_count_lt⟩

noncomputable def OriginalProjectionParameters.typeDependency
    (packet : OriginalProjectionParameters env U name info levels)
    (root : ParameterEqualityRoot packet.origin.types U) : SelectedParameterDependency env U :=
  ⟨packet.origin.types, packet.origin.typesOrdered, root, packet.origin.types_count_lt⟩

noncomputable def projectionParameterDependencies
    {levels : List VLevel}
    (ordered : env.Ordered) (registered : env.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U) : List (SelectedParameterDependency env U) :=
  let packet := selectProjectionParameters ordered registered levelsWF
  packet.instantiated.baseRoots.map packet.baseDependency ++
    packet.instantiated.typeRoots.map packet.typeDependency

/-- The original constant seed, its displayed universe instance, and their
common-context bridge all appear in the same finite dependency ledger. -/
noncomputable def constantParameterDependencies
    {leftLevels rightLevels : List VLevel}
    (ordered : env.Ordered) (name : Lean.Name)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    List (SelectedParameterDependency env U) := by
  classical
  exact if found : ∃ info, env.projections name info then
    let packet := selectProjectionParameters ordered (Classical.choose_spec found) leftWF
    let right := packet.shape.instance rightWF
    let bridge := packet.shape.commonUniverse leftWF rightWF equivalent
    (packet.instantiated.baseRoots ++ right.baseRoots ++ bridge.roots).map packet.baseDependency ++
      (packet.instantiated.typeRoots ++ right.typeRoots).map packet.typeDependency
  else []

theorem constantParameterDependencies_registered
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    {leftLevels rightLevels : List VLevel}
    (ordered : env.Ordered) (registered : env.projections name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    constantParameterDependencies ordered name leftWF rightWF equivalent =
      let packet := selectProjectionParameters ordered registered leftWF
      let right := packet.shape.instance rightWF
      let bridge := packet.shape.commonUniverse leftWF rightWF equivalent
      (packet.instantiated.baseRoots ++ right.baseRoots ++ bridge.roots).map packet.baseDependency ++
        (packet.instantiated.typeRoots ++ right.typeRoots).map packet.typeDependency := by
  classical
  unfold constantParameterDependencies
  rw [dif_pos ⟨info, registered⟩]
  have equal := ordered.projections_unique (Classical.choose_spec (show ∃ i, env.projections name i from ⟨info, registered⟩)) registered
  let build (selected : {i // env.projections name i}) : List (SelectedParameterDependency env U) :=
    let packet := selectProjectionParameters ordered selected.property leftWF
    let right := packet.shape.instance rightWF
    let bridge := packet.shape.commonUniverse leftWF rightWF equivalent
    (packet.instantiated.baseRoots ++ right.baseRoots ++ bridge.roots).map packet.baseDependency ++
      (packet.instantiated.typeRoots ++ right.typeRoots).map packet.typeDependency
  change build ⟨_, _⟩ = build ⟨info, registered⟩
  exact congrArg build (Subtype.ext equal)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
