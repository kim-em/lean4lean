import Lean4Lean.Theory.Typing.AnchoredNativeForwardObservation
import Lean4Lean.Theory.Typing.AnchoredNativeForwardTelescope
import Lean4Lean.Theory.Typing.AnchoredNativeClosedRelated
import Lean4Lean.Theory.Typing.AnchoredForwardFromReverse

/-! Concrete forward singleton transfer through the entire original equation.
The open leaf comes from actual capture replay; the semantic comparison uses
the already checked reverse rule and the original left typing child. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData
open AnchoredSource (Footprint Valuation)
open AnchoredSource.Adapted AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem forwardClosedObservation
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ [])
    (fits : PairedFits env U registry [] target locals σ σ available)
    {assigned : VExpr} {structural : Bool}
    (original : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned structural)
    {demand : Profile n} {footprint : Footprint}
    (observed : Obs env U registry target locals σ (rule.lhs.instL levels) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedResult env U registry target locals σ available (rule.rhs.instL levels) demand) := by
  have leaf : NativeEquationForward origin.stage.typing.recursors env U registry
      ((body.domains.map (·.instL levels)).reverse ++ [])
      (body.lhs.instL levels) (body.rhs.instL levels) := by
    intro assigned structural original target locals σ available closed hTarget substitutions fits
      n demand footprint observation resources
    rw [List.append_nil] at substitutions fits
    exact origin.forwardOpenObservation henv hscoped eliminator singleton earlier owner equation
      extracted levelLength levelsWF (signature := signature) lookup notDefinition
      closed hTarget substitutions fits observation resources
  have rebuilt : NativeEquationForward origin.stage.typing.recursors env U registry []
      (wrapLams (body.domains.map (·.instL levels)) (body.lhs.instL levels))
      (wrapLams (body.domains.map (·.instL levels)) (body.rhs.instL levels)) :=
    leaf.underTelescope henv hscoped
      (origin.stage.typing.recursors_le.trans origin.stage.installedBelow)
      (fun H => (earlier H).joint) (body.domains.map (·.instL levels))
  have parts := CaseSchema.EquationBody.extract_sound extracted
  have lhs : wrapLams (body.domains.map (·.instL levels)) (body.lhs.instL levels) =
      rule.lhs.instL levels := by rw [← instL_wrapLams, parts.1]
  have rhs : wrapLams (body.domains.map (·.instL levels)) (body.rhs.instL levels) =
      rule.rhs.instL levels := by rw [← instL_wrapLams, parts.2.1]
  rw [lhs, rhs] at rebuilt
  exact rebuilt original closed hTarget substitutions fits observed resources

theorem forwardTransfer
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {assigned : VExpr} {leftStructural rightStructural : Bool}
    (left : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned leftStructural)
    (right : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.rhs.instL levels) assigned rightStructural) :
    GradedTransfer env U registry target locals σ τ available
      (rule.lhs.instL levels) (rule.rhs.instL levels) assigned := by
  intro n demand footprint observation resources
  obtain ⟨forward⟩ := origin.forwardClosedObservation henv hscoped eliminator singleton earlier
    owner equation extracted levelLength levelsWF (signature := signature) lookup notDefinition
    closed hTarget .nil .nil left observation resources
  have original : GradedTransfer env U registry target locals σ σ available
      (rule.lhs.instL levels) (rule.lhs.instL levels) assigned :=
    ((earlier left.refl).joint target locals σ σ available
    closed hTarget .nil .nil).1
  have reverse : Transfer env U registry target locals σ σ available
      (rule.rhs.instL levels) (rule.lhs.instL levels) assigned :=
    origin.reverseTransfer henv hscoped eliminator singleton earlier owner equation
    extracted levelLength levelsWF (signature := signature) lookup notDefinition
    (σ := σ) (τ := σ) closed hTarget left right
  obtain ⟨result⟩ := forward.forwardComparison henv hscoped hTarget original reverse observation resources
  have scope : (rule.rhs.instL levels).Closed :=
    VExpr.WF.closedN origin.stage.typing.recursorsWF.ordered ⟨_, right.refl.defeq⟩ trivial
  have agree : ∀ i < 0, σ i = τ i := by intro i hi; omega
  have same := subst_congr_closedN scope agree
  exact ⟨{ result with
    observation := result.observation.realizePrefix scope τ agree
    related := by rw [← same]; exact result.related
    rawRelated := by rw [← same]; exact result.rawRelated }⟩

/-- Both equation directions and sort correctness are supplied by the
concrete declaration producers and original header typing children. -/
theorem singletonEquationJoint
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {assigned : VExpr} {leftStructural rightStructural : Bool}
    (left : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned leftStructural)
    (right : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.rhs.instL levels) assigned rightStructural) :
    GradedJoint env U registry [] (rule.lhs.instL levels) (rule.rhs.instL levels) assigned := by
  intro target locals σ τ available closed hTarget substitutions fits
  have reverse : Transfer env U registry target locals σ τ available
      (rule.rhs.instL levels) (rule.lhs.instL levels) assigned :=
    origin.reverseTransfer henv hscoped eliminator singleton earlier owner equation
      extracted levelLength levelsWF (signature := signature) lookup notDefinition closed hTarget left right
  exact ⟨origin.forwardTransfer henv hscoped eliminator singleton earlier owner equation
      extracted levelLength levelsWF (signature := signature) lookup notDefinition closed hTarget left right,
    Transfer.graded reverse,
    ((earlier left.refl).joint target locals σ τ available closed hTarget substitutions fits).2.2.1,
    ((earlier right.refl).joint target locals σ τ available closed hTarget substitutions fits).2.2.1⟩

/-- The final singleton rule recovers both closed endpoint typings from the
actual installed declaration. No endpoint-typing or equation-transfer packet
is supplied separately by its caller. -/
theorem generatedSingletonJoint
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none) :
    GradedJoint env U registry [] (rule.lhs.instL levels) (rule.rhs.instL levels)
      (rule.type.instL levels) := by
  have typed := origin.singletonStrong
    (NativeRecursorData.singletonEquation_of_equation singleton.2.1 owner equation)
  exact origin.singletonEquationJoint henv hscoped eliminator singleton earlier owner equation
    extracted levelLength levelsWF (signature := signature) lookup notDefinition
    (typed.1.instL levelsWF).hasType'.1 (typed.2.instL levelsWF).hasType'.1

end Lean4Lean.VEnv.NativeDeclarationOrigin
