import Lean4Lean.Theory.Typing.AnchoredOriginalParameterSpineStep

/-! The first parameter's original cell calls are paid by the actual
projection parent. The finite declaration ledger is inspected before any
alignment result is produced. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false

def FirstParameterCell.root
    {trace : OriginalContextEquality sourceEnv U source destination}
    (cell : FirstParameterCell trace A B) : ParameterEqualityRoot sourceEnv U :=
  ⟨[], .nil, A, B, .sort cell.level, cell.original⟩

theorem FamilyParameterLedger.seedBase_mem
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) (registered : sourceEnv.projections name info)
    (root : ParameterEqualityRoot (selectProjectionParameters ordered registered selection.seedWF).origin.base U)
    (member : root ∈ (selectProjectionParameters ordered registered selection.seedWF).instantiated.baseRoots) :
    (selectProjectionParameters ordered registered selection.seedWF).baseDependency root ∈ ledger.dependencies := by
  rw [FamilyParameterLedger.dependencies, constantParameterDependencies_registered ordered registered]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨root,
    List.mem_append_left _ (List.mem_append_left _ member), rfl⟩)

theorem FamilyParameterLedger.universe_mem
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (ledger : FamilyParameterLedger selection) (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U) (displayed : levels = ledger.otherLevels)
    (root : ParameterEqualityRoot (selectProjectionParameters ordered registered selection.seedWF).origin.base U)
    (member : root ∈ ((selectProjectionParameters ordered registered selection.seedWF).shape.commonUniverse
      selection.seedWF levelsWF selection.equivalent).roots) :
    (selectProjectionParameters ordered registered selection.seedWF).baseDependency root ∈ ledger.dependencies := by
  cases ledger with
  | mk otherLevels otherWF equivalent display =>
    dsimp only at displayed
    subst otherLevels
    rw [FamilyParameterLedger.dependencies, constantParameterDependencies_registered ordered registered]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨root, List.mem_append_right _ member, rfl⟩)

theorem FirstProjectionParameterCells.constructor_mem
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (registered : sourceEnv.projections name info) (levelsWF : ∀ level ∈ levels, level.WF U)
    (cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
      levelsWF selection.seedWF selection.equivalent) :
    (selectProjectionParameters ordered registered levelsWF).typeDependency cells.constructorCell.root ∈
      projectionParameterDependencies ordered registered levelsWF := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨cells.constructorCell.root,
    cells.constructorCell.retained, rfl⟩)

noncomputable def FirstConstructorParameterPrefix.domainLocation
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    (head : FirstConstructorParameterPrefix ordered cells) :
    Located (.left (selectOriginalHeader ordered packet.origin.constructorPresent requestedWF).original)
      (.ref head.domainOriginal) :=
  head.domain_eq ▸ Located.piDomain head.selected.view.location

/-- These are the ordinary closed-source clauses of the mutual original
induction. Each invocation supplies its exact original pair, literal source
agreement, and strict schedule; no semantic parameter-alignment supplier is
part of the conclusion. -/
structure ClosedParameterInduction (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst) (limit : Nat) : Prop where
  reindex : ∀ {leftEnv rightEnv : VEnv} {A B : VExpr} {u v : VLevel}
    (leftOrdered : leftEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (left : EndpointRef leftEnv U [] A (.sort u)) (right : EndpointRef rightEnv U [] B (.sort v)),
    A = B →
    richSchedule .expressionReindex
      ((Closure.close (left.dependencyOrigin leftOrdered) []).cost +
        (Closure.close (right.dependencyOrigin rightOrdered) []).cost) < limit →
    RichCodeTransfer env U registry target (.ref left) (.ref right)
      [] [] σ σ (fun _ => []) (fun _ => [])
  equality : ∀ {sourceEnv : VEnv} {A B : VExpr} {u : VLevel}
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (original : Derivation sourceEnv U [] A B (.sort u)) (forward : Bool),
    richSchedule .fundamental (Closure.close (original.dependencyOrigin ordered) []).cost < limit →
    if forward then
      RichCodeTransfer env U registry target (.ref (.left original)) (.ref (.right original))
        [] [] σ σ (fun _ => []) (fun _ => [])
    else
      RichCodeTransfer env U registry target (.ref (.right original)) (.ref (.left original))
        [] [] σ σ (fun _ => []) (fun _ => [])

private theorem selectedHeader_weight_congr
    {sourceEnv : VEnv} {U : Nat} {levels : List VLevel}
    {leftName rightName : Name} {leftInfo rightInfo : VConstant}
    (ordered : sourceEnv.Ordered)
    (left : sourceEnv.constants leftName = some leftInfo)
    (right : sourceEnv.constants rightName = some rightInfo)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (names : leftName = rightName) (infos : leftInfo = rightInfo) :
    ((selectOriginalHeader ordered left levelsWF).original.dependencyOrigin
      (selectOriginalHeader ordered left levelsWF).ordered).weight =
    ((selectOriginalHeader ordered right levelsWF).original.dependencyOrigin
      (selectOriginalHeader ordered right levelsWF).ordered).weight := by
  cases names
  cases infos
  rfl

private theorem FirstConstructorParameterPrefix.weight_le
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    (registered : sourceEnv.projections name info) (levelsWF : ∀ level ∈ levels, level.WF U)
    {cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
      levelsWF selection.seedWF selection.equivalent}
    (head : FirstConstructorParameterPrefix ordered cells) :
    (head.domainOriginal.dependencyOrigin
      (selectOriginalHeader ordered (selectProjectionParameters ordered registered selection.seedWF).origin.constructorPresent levelsWF).ordered).weight ≤
    ((selectOriginalHeader ordered (ordered.projectionConstructor registered) levelsWF).original.dependencyOrigin
      (selectOriginalHeader ordered (ordered.projectionConstructor registered) levelsWF).ordered).weight := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have names : packet.origin.constructor.name = info.ctorName :=
    (congrArg VProjectionInfo.ctorName packet.origin.info_eq).symm
  have infos : packet.origin.constructor.toVConstant = ({uvars := info.uvars, type := info.ctorType} : VConstant) := by
    apply Option.some.inj
    exact packet.origin.constructorPresent.symm.trans
      ((congrArg sourceEnv.constants names).trans (ordered.projectionConstructor registered))
  have equal := selectedHeader_weight_congr ordered packet.origin.constructorPresent
    (ordered.projectionConstructor registered) levelsWF names infos
  exact Nat.le_trans (head.domainLocation.dependency_weight_le _) (Nat.le_of_eq equal)


/-- All first-slot transfers consume the exact closed original roots in the
retained seed/requested ledgers. The only semantic premises are the smaller
mutual F/R clauses, and every strict call bound is proved here. -/
theorem firstParameterCellCalls_ofProjection
    {sourceEnv : VEnv} {U : Nat}
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams) (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (initial : List Closure) (positive : 0 < info.nparams)
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (ledger : FamilyParameterLedger selection)
    (bounded : ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight)
    (cells : FirstProjectionParameterCells (selectProjectionParameters ordered registered selection.seedWF)
      levelsWF selection.seedWF selection.equivalent)
    (induction : ClosedParameterInduction env U registry target σ
      (richSchedule .fundamental (Closure.close
        ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
          selected fieldWF (.ref field) major closed allowed).dependencyOrigin ordered) initial).cost)) :
    FirstParameterCellCalls cells
      (normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) positive)
      (firstConstructorParameterPrefix ordered cells positive) env registry target σ := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have baseBelow := packet.origin.baseBelow.trans below
  have typesBelow := packet.origin.typesBelow.trans below
  have ctorBelow : (selectOriginalHeader ordered packet.origin.constructorPresent levelsWF).source ≤ env :=
    (show (selectOriginalHeader ordered packet.origin.constructorPresent levelsWF).source ≤ sourceEnv from
      (Classical.choice (ordered.constantHeaderOrigin packet.origin.constructorPresent)).sourceBelow).trans below
  let familyHead := normalizedFamilyPrefix packet positive
  let ctorHead := firstConstructorParameterPrefix ordered cells positive
  let limit := richSchedule .fundamental (Closure.close
    ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF (.ref field) major closed allowed).dependencyOrigin ordered) initial).cost
  let seedHeader : EndpointRef selection.header.source U [] _ _ := .left selection.header.original
  let requestedHeader := selectOriginalHeader ordered (ordered.projectionConstructor registered) levelsWF
  let normRoot : ParameterEqualityRoot packet.origin.base U :=
    ⟨[], .nil, _, _, _, packet.instantiated.normalization⟩
  let normDependency := packet.baseDependency normRoot
  let familyDependency := packet.baseDependency cells.familyCell.root
  let constructorDependency := (selectProjectionParameters ordered registered levelsWF).typeDependency
    cells.constructorCell.root
  have normMember : normDependency ∈ ledger.dependencies :=
    ledger.seedBase_mem registered normRoot List.mem_cons_self
  have familyMember : familyDependency ∈ ledger.dependencies :=
    ledger.seedBase_mem registered cells.familyCell.root (List.mem_cons_of_mem _ cells.familyCell.retained)
  have constructorMember : constructorDependency ∈ projectionParameterDependencies ordered registered levelsWF :=
    cells.constructor_mem registered levelsWF
  have seedPair : ∀ left right : SelectedParameterDependency sourceEnv U,
      left ∈ ledger.dependencies → right ∈ ledger.dependencies →
      richSchedule .expressionReindex
        ((Closure.close (left.root.original.dependencyOrigin left.ordered) []).cost +
          (Closure.close (right.root.original.dependencyOrigin right.ordered) []).cost) < limit := by
    intro left right leftMember rightMember
    exact grouped_projection_seed_parameter_schedule ordered registered levelsWF levelCount parameterCount
      indexCount selected fieldWF field major closed allowed selection.header.ordered seedHeader
      ledger.dependencies bounded [] (by simp) (.equality left leftMember) (.equality right rightMember)
      (Or.inl trivial) initial
  have requestedPair : ∀ left right : ParameterDomain requestedHeader.ordered
      (.left requestedHeader.original) (projectionParameterDependencies ordered registered levelsWF),
      richSchedule .expressionReindex
        ((Closure.close left.origin []).cost + (Closure.close right.origin []).cost) < limit := by
    intro left right
    exact grouped_projection_parameter_schedule ordered registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed allowed [] (by simp) left right initial
  have crossPair : ∀ left : SelectedParameterDependency sourceEnv U,
      left ∈ ledger.dependencies →
      ∀ right : ParameterDomain requestedHeader.ordered (.left requestedHeader.original)
        (projectionParameterDependencies ordered registered levelsWF),
      richSchedule .expressionReindex
        ((Closure.close (left.root.original.dependencyOrigin left.ordered) []).cost +
          (Closure.close right.origin []).cost) < limit := by
    intro left leftMember right
    apply grouped_projection_cross_parameter_schedule ordered registered levelsWF levelCount parameterCount indexCount
      selected fieldWF field major closed allowed selection.header.ordered seedHeader ledger.dependencies
      (Nat.le_trans ledger.weight_le_pairWeight bounded) [] (by simp) (.equality left leftMember)
      [] (by simp) right initial
  have normalizationDomainBound := familyHead.domainLocation.dependency_weight_le packet.origin.baseOrdered
  change (familyHead.domainOriginal.dependencyOrigin packet.origin.baseOrdered).weight ≤
    (packet.instantiated.normalization.dependencyOrigin packet.origin.baseOrdered).weight at normalizationDomainBound
  have constructorDomainBound := ctorHead.weight_le registered levelsWF
  change (ctorHead.domainOriginal.dependencyOrigin
    (selectOriginalHeader ordered packet.origin.constructorPresent levelsWF).ordered).weight ≤
    (requestedHeader.original.dependencyOrigin requestedHeader.ordered).weight at constructorDomainBound
  have familyPair := seedPair normDependency familyDependency normMember familyMember
  have familySingle := seedPair familyDependency familyDependency familyMember familyMember
  let constructorDomain : ParameterDomain requestedHeader.ordered (.left requestedHeader.original)
      (projectionParameterDependencies ordered registered levelsWF) := .equality constructorDependency constructorMember
  let headerDomain : ParameterDomain requestedHeader.ordered (.left requestedHeader.original)
      (projectionParameterDependencies ordered registered levelsWF) := .headerDomain ⟨[], _, _, .ref (.left requestedHeader.original), .here⟩
  have ctorSingle := requestedPair constructorDomain constructorDomain
  have ctorPair := requestedPair constructorDomain headerDomain
  refine {
    familyR := induction.reindex packet.origin.baseOrdered packet.origin.baseOrdered baseBelow baseBelow
      familyHead.domainOriginal (.right cells.familyCell.original) (cells.normalizedDomain familyHead positive) ?_
    familyF := induction.equality packet.origin.baseOrdered baseBelow cells.familyCell.original false ?_
    levels := ?_
    ctorF := induction.equality packet.origin.typesOrdered typesBelow cells.constructorCell.original true ?_
    ctorR := induction.reindex packet.origin.typesOrdered
      (selectOriginalHeader ordered packet.origin.constructorPresent levelsWF).ordered typesBelow ctorBelow
      (.right cells.constructorCell.original) ctorHead.domainOriginal rfl ?_ }
  · change richSchedule .expressionReindex
      ((Closure.close (familyHead.domainOriginal.dependencyOrigin packet.origin.baseOrdered) []).cost +
       (Closure.close (cells.familyCell.original.dependencyOrigin packet.origin.baseOrdered) []).cost) < limit
    dsimp only [normDependency, familyDependency, normRoot, OriginalProjectionParameters.baseDependency,
      FirstParameterCell.root, richSchedule, RichPhase.code, Closure.cost, environmentCost] at familyPair
    dsimp only [richSchedule, RichPhase.code, Closure.cost, environmentCost]
    omega
  · change richSchedule .fundamental (Closure.close (cells.familyCell.original.dependencyOrigin packet.origin.baseOrdered) []).cost < limit
    dsimp only [familyDependency, OriginalProjectionParameters.baseDependency, FirstParameterCell.root,
      richSchedule, RichPhase.code, Closure.cost, environmentCost] at familySingle
    dsimp only [richSchedule, RichPhase.code, Closure.cost, environmentCost]
    omega
  · rcases ledger.displayed with same | changed
    · apply FirstParameterUniverseCalls.same same.symm
      apply induction.reindex packet.origin.baseOrdered packet.origin.typesOrdered baseBelow typesBelow
        (.left cells.familyCell.original) (.left cells.constructorCell.original)
        (congrArg (fun ls => cells.common.instL ls) same.symm)
      have pair := crossPair familyDependency familyMember constructorDomain
      exact pair
    · let universeDependency := packet.baseDependency cells.universeCell.root
      have universeMember : universeDependency ∈ ledger.dependencies :=
        ledger.universe_mem registered levelsWF changed cells.universeCell.root cells.universeCell.retained
      have pair := seedPair familyDependency universeDependency familyMember universeMember
      have single := seedPair universeDependency universeDependency universeMember universeMember
      refine .changed
        (induction.reindex packet.origin.baseOrdered packet.origin.baseOrdered baseBelow baseBelow
          (.left cells.familyCell.original) (.left cells.universeCell.original) rfl pair)
        (induction.equality packet.origin.baseOrdered baseBelow cells.universeCell.original true ?_)
        (induction.reindex packet.origin.baseOrdered packet.origin.typesOrdered baseBelow typesBelow
          (.right cells.universeCell.original) (.left cells.constructorCell.original) rfl
          (crossPair universeDependency universeMember constructorDomain))
      change richSchedule .fundamental (Closure.close (cells.universeCell.original.dependencyOrigin packet.origin.baseOrdered) []).cost < limit
      dsimp only [universeDependency, OriginalProjectionParameters.baseDependency, FirstParameterCell.root,
        richSchedule, RichPhase.code, Closure.cost, environmentCost] at single
      dsimp only [richSchedule, RichPhase.code, Closure.cost, environmentCost]
      omega
  · change richSchedule .fundamental (Closure.close (cells.constructorCell.original.dependencyOrigin packet.origin.typesOrdered) []).cost < limit
    dsimp only [constructorDomain, constructorDependency, ParameterDomain.origin,
      OriginalProjectionParameters.typeDependency, FirstParameterCell.root,
      richSchedule, RichPhase.code, Closure.cost, environmentCost] at ctorSingle
    dsimp only [richSchedule, RichPhase.code, Closure.cost, environmentCost]
    omega
  · change richSchedule .expressionReindex
      ((Closure.close (cells.constructorCell.original.dependencyOrigin packet.origin.typesOrdered) []).cost +
       (Closure.close (ctorHead.domainOriginal.dependencyOrigin
         (selectOriginalHeader ordered packet.origin.constructorPresent levelsWF).ordered) []).cost) < limit
    dsimp only [constructorDomain, constructorDependency, headerDomain, ParameterDomain.origin,
      OriginalProjectionParameters.typeDependency, FirstParameterCell.root, EndpointState.dependencyOrigin,
      EndpointRef.dependencyOrigin, richSchedule, RichPhase.code, Closure.cost, environmentCost] at ctorPair
    dsimp only [richSchedule, RichPhase.code, Closure.cost, environmentCost]
    omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
