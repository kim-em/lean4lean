import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterCaptureStep

/-! The first parameter step uses cells selected from the retained original
declaration traces. It produces the captured constructor slot from the same
owner queries used for the normalized family slot. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure FirstParameterCell
    (trace : OriginalContextEquality sourceEnv U source destination) (A B : VExpr) where
  level : VLevel
  original : Derivation sourceEnv U [] A B (.sort level)
  retained : (⟨[], .nil, A, B, .sort level, original⟩ : ParameterEqualityRoot sourceEnv U) ∈ trace.roots

/-- Telescope contexts are reversed: the first declaration parameter is
the final context cell, whose actual original source context is empty. -/
theorem firstParameterCell
    (trace : OriginalContextEquality sourceEnv U source destination)
    (sourceLast : source.getLast? = some A) (destinationLast : destination.getLast? = some B) :
    Nonempty (FirstParameterCell trace A B) := by
  induction trace with
  | nil => simp at sourceLast
  | @cons source destination left right level tail original ih =>
    cases source with
    | nil =>
      have empty : destination = [] := by
        have lengths := tail.length_eq
        cases destination <;> simp_all
      subst destination
      cases tail
      simp only [List.getLast?_singleton, Option.some.injEq] at sourceLast destinationLast
      subst A B
      exact ⟨⟨level, original, List.mem_cons_self⟩⟩
    | cons first rest =>
      cases destination with
      | nil => have impossible := tail.length_eq; simp at impossible
      | cons next remaining =>
        obtain ⟨selected⟩ := ih (by simpa using sourceLast) (by simpa using destinationLast)
        exact ⟨⟨selected.level, selected.original, List.mem_cons_of_mem _ selected.retained⟩⟩

theorem takeForalls_first
    {expression result : VExpr} {domains : List VExpr}
    (take : expression.takeForalls count = some (domains, result)) (positive : 0 < count) :
    ∃ A B rest, expression = .forallE A B ∧ domains = A :: rest := by
  obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  cases expression <;> simp only [takeForalls] at take
  all_goals try cases take
  case forallE A B =>
    cases tail : B.takeForalls count with
    | none => simp [tail] at take
    | some pair =>
      rcases pair with ⟨rest, residual⟩
      simp only [tail] at take
      obtain ⟨rfl, rfl⟩ := take
      exact ⟨A, B, rest, rfl, rfl⟩

theorem NormalizedFamilyPrefix.firstDomain
    {packet : OriginalProjectionParameters sourceEnv U name info levels}
    (head : NormalizedFamilyPrefix packet) (positive : 0 < info.nparams) :
    ∃ A rest, packet.shape.familyParams = A :: rest ∧ head.domainExpression = A.instL levels := by
  obtain ⟨A, B, rest, shape, params⟩ := takeForalls_first packet.shape.familyTake positive
  refine ⟨A, rest, params, ?_⟩
  have same := head.shape
  rw [shape] at same
  exact (VExpr.forallE.inj same).1.symm

structure FirstProjectionParameterCells
    (packet : OriginalProjectionParameters sourceEnv U name info seedLevels)
    (requestedWF : ∀ level ∈ requestedLevels, level.WF U)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels) where
  common : VExpr
  family : VExpr
  constructor : VExpr
  commonRest : List VExpr
  familyRest : List VExpr
  constructorRest : List VExpr
  common_eq : packet.shape.common = common :: commonRest
  family_eq : packet.shape.familyParams = family :: familyRest
  constructor_eq : packet.shape.ctorParams = constructor :: constructorRest
  familyCell : FirstParameterCell packet.instantiated.family
    (common.instL seedLevels) (family.instL seedLevels)
  universeCell : FirstParameterCell (packet.shape.commonUniverse seedWF requestedWF equivalent)
    (common.instL seedLevels) (common.instL requestedLevels)
  constructorCell : FirstParameterCell (packet.shape.instance requestedWF).constructor
    (common.instL requestedLevels) (constructor.instL requestedLevels)

theorem firstProjectionParameterCells
    (packet : OriginalProjectionParameters sourceEnv U name info seedLevels)
    (requestedWF : ∀ level ∈ requestedLevels, level.WF U)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels)
    (positive : 0 < info.nparams) :
    Nonempty (FirstProjectionParameterCells packet requestedWF seedWF equivalent) := by
  obtain ⟨family, _, familyRest, _, familyEq⟩ := takeForalls_first packet.shape.familyTake positive
  obtain ⟨constructor, _, constructorRest, _, constructorEq⟩ := takeForalls_first packet.shape.ctorTake positive
  have commonExists : ∃ common rest, packet.shape.common = common :: rest := by
    have lengths := packet.instantiated.family.length_eq
    rw [familyEq] at lengths
    cases same : packet.shape.common with
    | nil => simp [same] at lengths
    | cons first rest => exact ⟨first, rest, rfl⟩
  obtain ⟨common, commonRest, commonEq⟩ := commonExists
  obtain ⟨familyCell⟩ := firstParameterCell (A := common.instL seedLevels) (B := family.instL seedLevels) packet.instantiated.family
    (by simp [commonEq]) (by simp [familyEq])
  obtain ⟨universeCell⟩ := firstParameterCell (A := common.instL seedLevels) (B := common.instL requestedLevels) (packet.shape.commonUniverse seedWF requestedWF equivalent)
    (by simp [commonEq]) (by simp [commonEq])
  obtain ⟨constructorCell⟩ := firstParameterCell (A := common.instL requestedLevels) (B := constructor.instL requestedLevels) (packet.shape.instance requestedWF).constructor
    (by simp [commonEq]) (by simp [constructorEq])
  exact ⟨⟨common, family, constructor, commonRest, familyRest, constructorRest,
    commonEq, familyEq, constructorEq, familyCell, universeCell, constructorCell⟩⟩

theorem FirstProjectionParameterCells.normalizedDomain
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    (head : NormalizedFamilyPrefix packet) (positive : 0 < info.nparams) :
    head.domainExpression = cells.family.instL seedLevels := by
  obtain ⟨A, rest, params, domain⟩ := head.firstDomain positive
  rw [cells.family_eq] at params
  cases (List.cons.inj params).1
  exact domain

structure FirstConstructorParameterPrefix
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (ordered : sourceEnv.Ordered)
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent) where
  bodyExpression : VExpr
  shape : packet.origin.constructor.type.instL requestedLevels =
    .forallE (cells.constructor.instL requestedLevels) bodyExpression
  selected : PiPrefix ((Located.here (root := .left
    (selectOriginalHeader ordered packet.origin.constructorPresent requestedWF).original)).castExpression shape)

noncomputable def firstConstructorParameterPrefix
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (ordered : sourceEnv.Ordered)
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    (positive : 0 < info.nparams) : FirstConstructorParameterPrefix ordered cells := by
  have existsBody : ∃ B, packet.origin.constructor.type = .forallE cells.constructor B := by
    obtain ⟨A, B, rest, shape, params⟩ := takeForalls_first packet.shape.ctorTake positive
    rw [cells.constructor_eq] at params
    cases (List.cons.inj params).1
    refine ⟨B, ?_⟩
    have infoType : packet.origin.constructor.type = info.ctorType :=
      (congrArg VProjectionInfo.ctorType packet.origin.info_eq).symm
    exact infoType.trans shape
  let B := Classical.choose existsBody
  have shape : packet.origin.constructor.type.instL requestedLevels =
      .forallE (cells.constructor.instL requestedLevels) (B.instL requestedLevels) := by
    rw [Classical.choose_spec existsBody]
    rfl
  exact ⟨B.instL requestedLevels, shape, piPrefix ((Located.here (root := .left
    (selectOriginalHeader ordered packet.origin.constructorPresent requestedWF).original)).castExpression shape)⟩

noncomputable def FirstConstructorParameterPrefix.domainOriginal
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    (head : FirstConstructorParameterPrefix ordered cells) :
    EndpointRef (selectOriginalHeader ordered packet.origin.constructorPresent requestedWF).source U []
      (cells.constructor.instL requestedLevels) (.sort head.selected.view.domainLevel) :=
  Classical.choose head.selected.view.location.originalDomains.1

theorem FirstConstructorParameterPrefix.domain_eq
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    (head : FirstConstructorParameterPrefix ordered cells) :
    head.selected.view.domain = .ref head.domainOriginal :=
  Classical.choose_spec head.selected.view.location.originalDomains.1

private def castDomain
    (domain : EndpointRef sourceEnv U source A (.sort level)) (same : A = B) :
    EndpointRef sourceEnv U source B (.sort level) := same ▸ domain

private theorem castDomainTransfer
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {destination : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    (same : A = B) :
    RichCodeTransfer env U registry target (.ref (castDomain domain same)) destination
      locals rightLocals σ τ available rightAvailable ↔
    RichCodeTransfer env U registry target (.ref domain) destination
      locals rightLocals σ τ available rightAvailable := by
  cases same
  rfl

/-- Equal universe lists use a literal source reindex directly. Only the
other branch invokes the actual retained universe-comparison proof. -/
inductive FirstParameterUniverseCalls
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst) : Prop where
  | same (levels_eq : seedLevels = requestedLevels)
      (sourceR : RichCodeTransfer env U registry target
        (.ref (.left cells.familyCell.original)) (.ref (.left cells.constructorCell.original))
        [] [] σ σ (fun _ => []) (fun _ => [])) :
      FirstParameterUniverseCalls cells env registry target σ
  | changed
      (seedR : RichCodeTransfer env U registry target
        (.ref (.left cells.familyCell.original)) (.ref (.left cells.universeCell.original))
        [] [] σ σ (fun _ => []) (fun _ => []))
      (universeF : RichCodeTransfer env U registry target
        (.ref (.left cells.universeCell.original)) (.ref (.right cells.universeCell.original))
        [] [] σ σ (fun _ => []) (fun _ => []))
      (requestedR : RichCodeTransfer env U registry target
        (.ref (.right cells.universeCell.original)) (.ref (.left cells.constructorCell.original))
        [] [] σ σ (fun _ => []) (fun _ => [])) :
      FirstParameterUniverseCalls cells env registry target σ

/-- These are exactly the selected original cell endpoints and the two
actual header domains. All first-slot frames are empty, so no unprovided
capture resources are required by this finite local comparison. -/
structure FirstParameterCellCalls
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    (cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent)
    (familyHead : NormalizedFamilyPrefix packet)
    (ctorHead : FirstConstructorParameterPrefix ordered cells)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst) : Prop where
  familyR : RichCodeTransfer env U registry target (.ref familyHead.domainOriginal) (.ref (.right cells.familyCell.original))
    [] [] σ σ (fun _ => []) (fun _ => [])
  familyF : RichCodeTransfer env U registry target (.ref (.right cells.familyCell.original)) (.ref (.left cells.familyCell.original))
    [] [] σ σ (fun _ => []) (fun _ => [])
  levels : FirstParameterUniverseCalls cells env registry target σ
  ctorF : RichCodeTransfer env U registry target (.ref (.left cells.constructorCell.original)) (.ref (.right cells.constructorCell.original))
    [] [] σ σ (fun _ => []) (fun _ => [])
  ctorR : RichCodeTransfer env U registry target (.ref (.right cells.constructorCell.original)) (.ref ctorHead.domainOriginal)
    [] [] σ σ (fun _ => []) (fun _ => [])

theorem FirstParameterCellCalls.transfer
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {ctorHead : FirstConstructorParameterPrefix ordered cells}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (positive : 0 < info.nparams)
    (calls : FirstParameterCellCalls cells familyHead ctorHead env registry target σ) :
    RichCodeTransfer env U registry target (.ref familyHead.domainOriginal) (.ref ctorHead.domainOriginal)
      [] [] σ σ (fun _ => []) (fun _ => []) ∧
    TypeConversion env U target (familyHead.domainExpression.subst σ)
      ((cells.constructor.instL requestedLevels).subst σ) := by
  have same := cells.normalizedDomain familyHead positive
  cases calls.levels with
  | changed seedR universeF requestedR =>
    obtain ⟨transfer, path⟩ := parameterCellsTransfer henv
      (packet.origin.baseBelow.trans below) (packet.origin.typesBelow.trans below) formed
      cells.familyCell.original cells.universeCell.original cells.constructorCell.original
      (castDomain familyHead.domainOriginal same) ctorHead.domainOriginal .nil .nil
      ((castDomainTransfer same).mpr calls.familyR) calls.familyF seedR universeF
      requestedR calls.ctorF calls.ctorR
    exact ⟨(castDomainTransfer same).mp transfer, by simpa only [same] using path⟩
  | same levelsEq sourceR =>
    obtain ⟨first, path⟩ := parameterCellBackward henv (packet.origin.baseBelow.trans below) formed
      cells.familyCell.original (castDomain familyHead.domainOriginal same) (σ := σ) .nil
      ((castDomainTransfer same).mpr calls.familyR) calls.familyF
    constructor
    · intro relevant n profile footprint query resources
      obtain ⟨a⟩ := (castDomainTransfer same).mp first query resources
      obtain ⟨b⟩ := sourceR a.certificate a.resources
      obtain ⟨c⟩ := calls.ctorF b.certificate b.resources
      obtain ⟨d⟩ := calls.ctorR c.certificate c.resources
      exact ⟨{ d with related := a.related.trans henv (b.related.trans henv (c.related.trans henv d.related)) }⟩
    · have last := (cells.constructorCell.original.forget.defeq.mono (packet.origin.typesBelow.trans below)).substDF
        henv (Ctx.SubstEq.wf (show Ctx.SubstEq env U target σ σ [] from .nil)) formed (.nil : Ctx.SubstEq env U target σ σ [])
      have changed : TypeConversion env U target ((cells.common.instL seedLevels).subst σ)
          ((cells.constructor.instL requestedLevels).subst σ) := by
        have expressionEq := congrArg (fun ls => (cells.common.instL ls).subst σ) levelsEq
        rw [expressionEq]
        exact .single last
      simpa only [same] using path.trans changed

/-- The owner keeps its actual inferred-type certificate and query. Only
its declared parameter certificate changes along the selected cells. -/
noncomputable def FirstParameterCellCalls.align
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {ctorHead : FirstConstructorParameterPrefix ordered cells}
    {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
    {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
    {owner : HeaderOwner field major}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (positive : 0 < info.nparams)
    (calls : FirstParameterCellCalls cells familyHead ctorHead env registry target σ)
    (answer : HeaderValueAlignment owner familyHead.domainOriginal env registry target
      ownerLocals [] ownerLeft ownerRight σ ownerAvailable (fun _ => []) input) :
    HeaderValueAlignment owner ctorHead.domainOriginal env registry target
      ownerLocals [] ownerLeft ownerRight σ ownerAvailable (fun _ => []) input := by
  obtain ⟨transfer, path⟩ := calls.transfer henv below formed positive
  let changed := Classical.choice (transfer answer.aligned.certificate answer.aligned.resources)
  exact {
    value := answer.value
    aligned := { changed with related := answer.aligned.related.trans henv changed.related }
    path := answer.path.trans path }

/-- The first constructor slot is produced from the actual family slot's
whole owner queries. Its needs, multiplicity and owner frames are preserved;
the generated source map retains the original nominal argument. -/
theorem FirstParameterCellCalls.captureGroup
    {packet : OriginalProjectionParameters sourceEnv U name info seedLevels}
    {requestedWF : ∀ level ∈ requestedLevels, level.WF U}
    {seedWF : ∀ level ∈ seedLevels, level.WF U}
    {equivalent : List.Forall₂ (· ≈ ·) seedLevels requestedLevels}
    {ordered : sourceEnv.Ordered}
    {cells : FirstProjectionParameterCells packet requestedWF seedWF equivalent}
    {familyHead : NormalizedFamilyPrefix packet}
    {ctorHead : FirstConstructorParameterPrefix ordered cells}
    {base : OriginalCaptureBase env U registry target}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {ownerFrame : RawOriginalRichFrame ownerEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable}
    {field : EndpointRef ownerEnv U ownerSource fieldExpression fieldType}
    {major : EndpointRef ownerEnv U ownerSource majorExpression majorType}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (formed : OnCtx target (env.IsType U))
    (positive : 0 < info.nparams)
    (calls : FirstParameterCellCalls cells familyHead ctorHead env registry target commonLeft)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    (ownerOrdered : ownerEnv.Ordered) (ownerInitial : List Closure)
    (entries : RichGroupedCapture (field := field) (major := major) familyHead.domainOriginal env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight))
    (owners : ∀ entry ∈ entries, Nonempty (OriginalFrameExtension ownerFrame entry.frame.raw)) :
    ∃ changed : RichGroupedCapture (field := field) (major := major) ctorHead.domainOriginal env registry target
      [] commonLeft (fun _ => []) ownerInitial rawCapture (rawCapture.subst ownerLeft) (rawCapture.subst ownerRight),
      changed.needs = entries.needs ∧
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture (.empty common) ctorHead.domainOriginal nominalGraph nominal provenance)
        ((OriginalRichFrame.nil (σ := commonLeft) (τ := commonRight) (locals := []) (available := fun _ => [])).group ctorHead.domainOriginal ownerOrdered ownerInitial changed).raw := by
  obtain ⟨transfer, path⟩ := calls.transfer henv below formed positive
  let changed := realignParameterEntries henv entries transfer path
  refine ⟨changed, realignParameterEntries_needs henv entries transfer path, ?_⟩
  exact realignParameterEntries_generated (ScopedCaptureGenerated.empty common commonLeft commonRight)
    ctorHead.domainOriginal ownerGenerated nominalGraph nominal provenance displayed ownerOrdered ownerInitial
    henv entries transfer path owners

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
