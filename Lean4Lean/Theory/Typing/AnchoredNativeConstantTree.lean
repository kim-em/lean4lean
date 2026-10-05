import Lean4Lean.Theory.Inductive.NativeCommonPrefix
import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Typing.AnchoredNativeFormationPayload
import Lean4Lean.Theory.Typing.NativeRuleRegistration
import Lean4Lean.Theory.Typing.AnchoredSourceFootprint

/-! A finite native constant observation, before adding the corresponding
constructor to the mutual source core. Its only open source contexts are the
fixed registered native and equation telescopes. The outside source footprint
is empty. Crucially, the terminal RHS is observed at BASE-context witnessed
captures, not at private fresh proof variables of the canonical program.

This concrete tree has no semantic interpreter field. Declaration-stage
induction must interpret its actual RHS and certificate descendants. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- Remove the equation's field binders from actual RHS/guard requirements.
Every data binder contributes a demand on its actual native INDEX variable;
proof binders consume only the empty demand. Domain-certificate requirements
are accumulated BEFORE removing the preceding field, so none are hidden.
All profiles and witnesses live in one base target context. -/
inductive NativeCaptureSupport (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (witnesses : List VExpr) : Nat → Footprint → Footprint → Type where
  | prefix (required : Footprint) :
      NativeCaptureSupport env U registry target program witnesses 0 required
        (Footprint.sourceLift (.skipN .refl (program.prefixArgs.length - data.indexOffset)) required)
  | index {templates : NativeIndexTemplates program}
      {naturalAvailable captureAvailable : Valuation} {input packed : Profile n}
      {required outside previousNative : Footprint} {value : VExpr}
      (guard : NativeIndexGuard (env := env) (U := U) (registry := registry) (target := target)
        templates
        (List.range (data.indexOffset + templates.slot))
        (List.range (data.indexOffset + templates.field))
        (nativeCaptureSubst (program.prefixArgs.take (data.indexOffset + templates.slot)))
        (nativeCaptureSubst (witnesses.take (data.indexOffset + templates.field)))
        naturalAvailable captureAvailable input)
      (nativeValue : program.prefixArgs[data.indexOffset + templates.slot]? = some value)
      (copiedValue : witnesses[data.indexOffset + templates.field]? = some value)
      (pack : BinderPack n packed required outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
      (previous : NativeCaptureSupport env U registry target program witnesses templates.field
        (guard.declaredFootprint ++ outside) previousNative) :
      NativeCaptureSupport env U registry target program witnesses (templates.field + 1) required
        (previousNative ++
          Footprint.sourceLift (.skipN .refl
            (program.prefixArgs.length - (data.indexOffset + templates.slot)))
            guard.naturalFootprint ++
          [(program.prefixArgs.length - 1 - (data.indexOffset + templates.slot), ⟨n, input⟩)])
  | proof {field : Nat} {domain witness : VExpr} {required outside native : Footprint}
      (instruction : program.instructions[field]? = some (.proof domain))
      (captured : witnesses[data.indexOffset + field]? = some witness)
      (sourceProof : env.HasType U
        (((program.equationBody.domains.take (data.indexOffset + field)).map
          (·.instL program.levels)).reverse) domain (.sort .zero))
      (domainProof : env.HasType U target
        (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field)))) (.sort .zero))
      (inhabitant : env.HasType U target witness
        (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field)))))
      (pack : BinderPack n (.empty : Profile n) required outside)
      (previous : NativeCaptureSupport env U registry target program witnesses field outside native) :
      NativeCaptureSupport env U registry target program witnesses (field + 1) required native

/-- A terminal after exactly the major argument. There are no trailing
applications here; those use the existing compositional source app rule.
The base witnesses and RHS source observation are genuine finite children.
The generated fresh-proof program is retained separately. -/
structure NativeConstantTerminal (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) (arguments : List VExpr)
    (demand : Profile n) (nativeFootprint : Footprint) where
  program : SaturatedProgram data
  selected : data.saturatedProgram levels arguments = some program
  saturated : arguments.length = data.majorOffset + 1
  noTrailing : program.trailing = []
  prefix_eq : program.prefixArgs = arguments
  witnesses : List VExpr
  witnessLength : witnesses.length = program.equationBody.domains.length
  witnessPrefix : witnesses.take data.indexOffset = arguments.take data.indexOffset
  /-- Field-copy guards alone do not align constructor RESULT indices.
  For `mk : S 0`, an arbitrary `h : S n` does not permit replay at `n`.
  This concrete telescope guard excludes that malformed tree. Its initial
  producer comes from the actual equation LHS tuple, not an arbitrary
  native-head equality or an assumed reduction theorem. -/
  argumentAlignment : Ctx.SubstEq env U target
    (nativeCaptureSubst arguments)
    (nativeCaptureSubst (nativeEquationArguments program witnesses)) signature.domains.reverse
  /-- The anchor tuple is the actual equation tuple. Arbitrary later tuples
  are handled by paired fitting substitutions, rather than a raw guard. -/
  arguments_eq : arguments = nativeEquationArguments program witnesses
  bodyFootprint : Footprint
  body : Obs env U registry target (List.range program.equationBody.domains.length)
    (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL levels) demand bodyFootprint
  captures : NativeCaptureSupport env U registry target program witnesses
    program.instructions.length bodyFootprint nativeFootprint

/-- Prefix identity is computed from the actual canonical generator, not a
caller-supplied reconstruction condition. -/
theorem NativeConstantTerminal.prefixDomains
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (terminal : NativeConstantTerminal env U registry target signature arguments demand footprint) :
    (terminal.program.equationBody.domains.map (·.instL levels)).take data.indexOffset =
      signature.domains.take data.indexOffset :=
  saturatedProgram_commonPrefix terminal.selected signature.typeOrigin signature.telescope

/-- Formal native binders use the exact registered domain. All consumed
local needs are packed, with literal coverage by the declared row input.
Only the selected anchor is installed while building this finite tree. The
original generic-type/body theorem supplies future-argument parametricity. -/
inductive NativeTelescopeTree (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) :
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal (leaf : NativeConstantTerminal env U registry target signature arguments demand footprint) :
      NativeTelescopeTree env U registry target signature arguments demand footprint
  | binder {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n} {domainFootprint bodyFootprint outside : Footprint}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : NativeTelescopeTree env U registry target signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      NativeTelescopeTree env U registry target signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)

/-- The intended new source constructor observes ONLY a bare constant and
has footprint `[]`. It cannot smuggle demands on an enclosing source context.
Registration and the exact chosen head are concrete evidence, not an opaque
adequacy operator. -/
structure NativeConstantObservation (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) (demand : Profile n) where
  data : NativeRecursorData
  lookup : registry.natives name = some data
  notDefinition : registry.definitions name = none
  name_eq : data.name = name
  registered : NativeRecursorRegistered env data
  signature : NativeConstantSignature data levels
  typeSupport : Profile n
  typeRealization : Subst
  typeCertificate : CodeCert env U registry target [] typeRealization
    (signature.type.instL levels) typeSupport []
  typed : demand.HasType typeSupport
  tree : NativeTelescopeTree env U registry target signature [] demand []

end Lean4Lean.AnchoredSource.Adapted
