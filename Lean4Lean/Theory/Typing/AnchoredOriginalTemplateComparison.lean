import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! The binary result needed to interpret a shared sparse field template.
Its two actual instantiations need not be syntactically equal. The original
left support and concrete right query are retained independently, and raw
typed equality is present even when the observation profile is empty.

This is the common motive for the local application/projection interpreter,
not a supplied comparison theorem. It imposes no typing judgment on the
uninstantiated template or on every slot of its sparse capture map. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure TemplateComparisonResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression leftType rightType : VExpr}
    (left : EndpointState leftEnv U leftSource leftExpression leftType)
    (right : EndpointState rightEnv U rightSource rightExpression rightType)
    (leftLocals rightLocals : List Nat) (σ τ : Subst)
    (leftAvailable rightAvailable : Valuation) (profile : Profile n) where
  source : RichSupportedValue leftEnv env U registry target left leftLocals σ σ leftAvailable profile
  related : Related env U registry target (leftExpression.subst σ) (rightExpression.subst τ)
    (leftType.subst σ) profile source.support
  raw : env.IsDefEq U target (leftExpression.subst σ) (rightExpression.subst τ) (leftType.subst σ)
  rightQuery : RichGradedResult rightEnv env U registry target right rightLocals τ rightAvailable profile

/-- Code comparison returns the actual right certificate and a raw type
path. The path cannot be inferred from an empty semantic profile. -/
structure TemplateCodeResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression : VExpr} {leftLevel rightLevel : VLevel}
    (left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel))
    (right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel))
    (rightLocals : List Nat) (σ τ : Subst) (rightAvailable : Valuation)
    (relevant : Bool) (profile : Profile n)
    extends RichCodeTransferResult env U registry target left right rightLocals σ τ rightAvailable relevant profile where
  path : TypeConversion env U target (leftExpression.subst σ) (rightExpression.subst τ)

/-- The assigned-type mode of the SAME local term comparison. Its endpoints
are the actual formation nodes retained by the two original terms. In
particular, this is not ordinary same-expression C: the instantiated terms
and their assigned types may both differ syntactically.

The right locals and resources describe the frame selected by reconstruction;
they need not be those of the initial right frame. A caller must retain that
selected frame together with this result. The incoming left certificate and
recursive-call bounds belong to the interpreter's input, not to this result. -/
abbrev TemplateAssignedResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {leftEnv rightEnv : VEnv} {leftSource rightSource : List VExpr}
    {leftExpression rightExpression leftType rightType : VExpr}
    (left : EndpointState leftEnv U leftSource leftExpression leftType)
    (right : EndpointState rightEnv U rightSource rightExpression rightType)
    (rightLocals : List Nat) (σ τ : Subst) (rightAvailable : Valuation)
    (relevant : Bool) (profile : Profile n) :=
  TemplateCodeResult env U registry target left.typeFormation.node right.typeFormation.node
    rightLocals σ τ rightAvailable relevant profile

/-- Extract code at the SAME right original and bound that exact certificate
by the returned query. No new original derivation or type comparison is used. -/
theorem TemplateComparisonResult.code
    {left : EndpointState leftEnv U leftSource leftExpression (.sort leftLevel)}
    {right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    (answer : TemplateComparisonResult env U registry target left right leftLocals rightLocals
      σ τ leftAvailable rightAvailable profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sorted : profile.HasType (.sort relevant)) :
    ∃ code : TemplateCodeResult env U registry target left right rightLocals σ τ rightAvailable relevant profile,
      ∀ policy, code.certificate.headDepth policy ≤ answer.rightQuery.observation.headDepth policy := by
  obtain ⟨footprint, certificate, resources, bound⟩ := answer.rightQuery.code_headDepth henv sorted
  exact ⟨{
    footprint := footprint
    certificate := certificate
    resources := resources
    related := answer.related.code_of_sortable henv hscoped formed sorted
    path := .single (by simpa only [subst_sort] using answer.raw) }, bound⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
