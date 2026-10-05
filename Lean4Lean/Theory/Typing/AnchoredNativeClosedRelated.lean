import Lean4Lean.Theory.Typing.AnchoredNativeEquationTelescope
import Lean4Lean.Theory.Typing.AnchoredNativeOpenRelated

/-! The singleton equation comparison through its entire original telescope.
Both the source reconstruction and semantic leaf are concrete declaration
producers. No open equation comparison is supplied by the caller. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData
open AnchoredSource (Footprint Valuation lowerProfile)
open AnchoredSource.Adapted AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem closedComparison_atType
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
    {leftType rightType : VExpr} {leftStructural rightStructural : Bool}
    (left : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) leftType leftStructural)
    (right : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.rhs.instL levels) rightType rightStructural)
    {demand support : Profile n} {bodyFootprint leftFootprint rightFootprint : Footprint}
    (observed : Obs env U registry target locals σ (rule.rhs.instL levels) demand bodyFootprint)
    (resources : bodyFootprint.Available available)
    (leftCertificate : CodeCert env U registry target locals σ leftType support leftFootprint)
    (rightCertificate : CodeCert env U registry target locals σ rightType support rightFootprint)
    (leftResources : leftFootprint.Available available)
    (rightResources : rightFootprint.Available available)
    (bridge : TypeRelated env U registry target (leftType.subst σ) (rightType.subst σ) support)
    (typed : demand.HasType support) :
    Nonempty (NativeEquationResult env U registry target locals σ available
      (rule.lhs.instL levels) (rule.rhs.instL levels) rightType demand support) := by
  have terminal : NativeEquationComparison origin.stage.typing.recursors env U registry
      (body.domains.map (·.instL levels)).reverse (body.lhs.instL levels) (body.rhs.instL levels) := by
    intro leftType rightType leftStructural rightStructural left right target locals σ available
      closed hTarget substitutions fits n demand support footprint leftFootprint rightFootprint
      observation resources leftCertificate rightCertificate leftResources rightResources bridge typed
    have build : ∀ atoms : List (Atom n), (∀ atom ∈ atoms, atom ∈ demand.atoms) →
        Nonempty (NativeEquationResult env U registry target locals σ available
          (body.lhs.instL levels) (body.rhs.instL levels) rightType (.mk atoms) support) := by
      intro atoms
      induction atoms with
      | nil =>
        intro _
        exact ⟨{
          footprint := []
          observation := .empty
          resources := by intro _ _ h; cases h
          related := by cases n <;> intro _ h <;> cases h }⟩
      | cons atom tail ih =>
        intro included
        obtain ⟨selected⟩ := observation.atom (included atom List.mem_cons_self)
        have selectedResources := selected.atomizes.available_closed resources closed
        have selectedTyped := typed.singleton_of_mem (included atom List.mem_cons_self)
        obtain ⟨headFootprint, ⟨head⟩, headAvailable⟩ := origin.initialObservation henv hscoped
          eliminator singleton earlier owner equation extracted levelLength levelsWF
          (signature := signature) lookup notDefinition closed hTarget substitutions fits left
          selected.observation selectedResources leftCertificate leftResources selectedTyped
        have headRelated := origin.openRelated_atType henv hscoped eliminator singleton earlier
          owner equation extracted levelLength levelsWF (signature := signature) lookup notDefinition
          closed hTarget substitutions fits left selected.observation selectedResources
          leftCertificate leftResources selectedTyped
        obtain ⟨tailResult⟩ := ih (fun atom hm => included atom (List.mem_cons_of_mem _ hm))
        exact ⟨{
          footprint := headFootprint ++ tailResult.footprint
          observation := .union head tailResult.observation
          resources := fun i need hm => (List.mem_append.mp hm).elim
            (headAvailable i need) (tailResult.resources i need)
          related := (Related.convert henv selectedTyped bridge headRelated).union tailResult.related }⟩
    exact build demand.atoms (fun _ h => h)
  have leaf : NativeEquationComparison origin.stage.typing.recursors env U registry
      ((body.domains.map (·.instL levels)).reverse ++ [])
      (body.lhs.instL levels) (body.rhs.instL levels) := by
    rw [List.append_nil]
    exact terminal
  have compared : NativeEquationComparison origin.stage.typing.recursors env U registry []
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
  rw [lhs, rhs] at compared
  exact compared left right closed hTarget substitutions fits observed resources
    leftCertificate rightCertificate leftResources rightResources bridge typed

/-- The original RHS child supplies the type cover; the concrete equation
producer supplies both the reconstructed LHS observer and semantic comparison. -/
theorem closedReverse
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
    {assigned : VExpr} {leftStructural rightStructural : Bool}
    (left : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned leftStructural)
    (right : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.rhs.instL levels) assigned rightStructural)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (rule.rhs.instL levels) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (TransferResult env U registry target locals σ σ available
      (rule.rhs.instL levels) (rule.lhs.instL levels) assigned demand) := by
  obtain ⟨base⟩ := ((earlier right.refl).joint target locals σ σ available closed hTarget
    substitutions fits).1 observation resources
  have code := TypeRelated.lower henv base.bound base.typeCode
  obtain ⟨compared⟩ := origin.closedComparison_atType henv hscoped eliminator singleton earlier
    owner equation extracted levelLength levelsWF (signature := signature) lookup notDefinition
    closed hTarget substitutions fits left right observation resources
    base.requestedCertificate base.requestedCertificate base.typeAvailable base.typeAvailable
    code base.requestedTyped
  exact ⟨{
    rawDemand := demand
    resultFootprint := compared.footprint
    observation := compared.observation
    adapter := .refl _
    resultAvailable := compared.resources
    support := lowerProfile n base.bound base.support
    typeFootprint := base.typeFootprint
    certificate := base.requestedCertificate
    typeAvailable := base.typeAvailable
    typed := base.requestedTyped
    rawTyped := base.requestedTyped
    typeCode := code
    related := compared.related
    rawRelated := (compared.related.symm henv).left_diagonal }⟩

/-- Full reverse transfer, including arbitrary ambient source realizations.
The equation is closed, so changing the output realization retains all actual
source evidence and finite resources. -/
theorem reverseTransfer
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
    Transfer env U registry target locals σ τ available
      (rule.rhs.instL levels) (rule.lhs.instL levels) assigned := by
  intro n demand footprint observation resources
  obtain ⟨result⟩ := origin.closedReverse henv hscoped eliminator singleton earlier owner equation
    extracted levelLength levelsWF (signature := signature) lookup notDefinition closed hTarget
    .nil .nil left right observation resources
  have scope : (rule.lhs.instL levels).Closed :=
    VExpr.WF.closedN origin.stage.typing.recursorsWF.ordered ⟨_, left.refl.defeq⟩ trivial
  have agree : ∀ i < 0, σ i = τ i := by intro i hi; omega
  have same := subst_congr_closedN scope agree
  exact ⟨{ result with
    observation := result.observation.realizePrefix scope τ agree
    related := by rw [← same]; exact result.related
    rawRelated := by rw [← same]; exact result.rawRelated }⟩

end Lean4Lean.VEnv.NativeDeclarationOrigin
