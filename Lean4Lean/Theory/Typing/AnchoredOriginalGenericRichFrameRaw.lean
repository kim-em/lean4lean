import Lean4Lean.Theory.Typing.AnchoredOriginalRichCaptureActivation

/-! Rich original frames are not restricted to descendants of a closed
header. Ordinary source contexts grow by actual original domain references;
a declaration-capture frame is one concrete base case. -/
namespace Lean4Lean.AnchoredSource

/-- Both finite resource tables remain visible after merging actual frames. -/
def Valuation.append (left right : Valuation) : Valuation :=
  fun index => left index ++ right index

@[simp] theorem Valuation.rename_append (ρ : Lift) (left right : Valuation) :
    (left.append right).rename ρ = (left.rename ρ).append (right.rename ρ) := by
  funext index
  exact List.map_append

end Lean4Lean.AnchoredSource

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

abbrev OriginalRichFrameFamily :=
  (sourceEnv env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) → (target : List VExpr) →
    {source : List VExpr} → ContextDerivation sourceEnv U source →
      List Nat → Subst → Subst → Valuation → Type

mutual
inductive RawOriginalRichFrame : OriginalRichFrameFamily where
  | reserve {context : ContextDerivation sourceEnv U source}
      (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (closures : List Closure) :
      RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available
  | merge {context : ContextDerivation sourceEnv U source}
      (left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable)
      (right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable) :
      RawOriginalRichFrame sourceEnv env U registry target context locals σ τ
        (leftAvailable.append rightAvailable)
  | nil : RawOriginalRichFrame sourceEnv env U registry target .nil locals σ τ available
  | header {header : EndpointRef sourceEnv U [] headerExpression headerType}
      {field : EndpointRef capturedEnv U capturedSource fieldExpression fieldType}
      {major : EndpointRef capturedEnv U capturedSource majorExpression majorType}
      (capturedOrdered : capturedEnv.Ordered) (initial : List Closure)
      (frame : HeaderBinderFrame header field major env registry target context locals σ τ available) :
      RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available
  | bind {context : ContextDerivation sourceEnv U source}
      (tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available)
      (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
        (Locals.push locals) (σ.cons x) (τ.cons y) (available.push needs)

  | capture {context : ContextDerivation sourceEnv U source}
      (tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (domain : EndpointRef sourceEnv U source A (.sort level))
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
      (initialContext : ContextDerivation sourceEnv U rootSource)
      (argument : EndpointState sourceEnv U source a A)
      (argumentLocation : Located root argument)
      (argumentLineage : argumentLocation.contextDerivation initialContext = context)
      (argumentQuery : RichObs sourceEnv env U registry target argument locals σ
        (rawInput : Profile k) argumentFootprint)
      (argumentAvailable : argumentFootprint.Available available)
      (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile n) footprint)
      (resources : footprint.Available available)
      (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst σ) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
        (Locals.push locals) (σ.cons x) (τ.cons y) (available.push needs)

  | group {context : ContextDerivation headerEnv U headerSource}
      {field : EndpointRef capturedEnv U capturedSource fieldExpression fieldType}
      {major : EndpointRef capturedEnv U capturedSource majorExpression majorType}
      (tail : RawOriginalRichFrame headerEnv env U registry target context locals σ τ available)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      (capturedOrdered : capturedEnv.Ordered) (ownerInitial : List Closure)
      (entries : RawRichGroupEntries (field := field) (major := major)
        domain env registry target locals σ available ownerInitial rawCapture leftValue rightValue needs) :
      RawOriginalRichFrame headerEnv env U registry target (.cons context domain) (Locals.push locals)
        (σ.cons leftValue) (τ.cons rightValue) (available.push needs)

inductive RawRichGroupEntry : {sourceEnv headerEnv : VEnv} → {U : Nat} → {source headerSource : List VExpr} →
    {fieldExpression fieldType majorExpression majorType A : VExpr} → {level : VLevel} →
    {field : EndpointRef sourceEnv U source fieldExpression fieldType} →
    {major : EndpointRef sourceEnv U source majorExpression majorType} →
    (domain : EndpointRef headerEnv U headerSource A (.sort level)) →
    (env : VEnv) → (registry : CanonicalHead.Registry) → (target : List VExpr) →
    (headerLocals : List Nat) → (declaredLeft : Subst) → (headerAvailable : Valuation) →
    (ownerInitial : List Closure) → (rawCapture leftValue rightValue : VExpr) → (n : Nat) → Profile n → Type where
  | mk {sourceEnv headerEnv env : VEnv} {U : Nat} {source headerSource target : List VExpr}
      {fieldExpression fieldType majorExpression majorType A : VExpr} {level : VLevel}
      {field : EndpointRef sourceEnv U source fieldExpression fieldType}
      {major : EndpointRef sourceEnv U source majorExpression majorType}
      {domain : EndpointRef headerEnv U headerSource A (.sort level)}
      {registry : CanonicalHead.Registry} {headerLocals : List Nat} {declaredLeft : Subst}
      {headerAvailable : Valuation} {ownerInitial : List Closure} {rawCapture leftValue rightValue : VExpr}
      {n : Nat} {input : Profile n} (owner : HeaderOwner field major)
      (ownerLocals : List Nat)
      (ownerLeft : Subst)
      (ownerRight : Subst)
      (ownerAvailable : Valuation)
      (initialContext : ContextDerivation sourceEnv U source)
      (frame : RawOriginalRichFrame sourceEnv env U registry target
    (owner.context initialContext) ownerLocals ownerLeft ownerRight ownerAvailable)
      (substitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source)
      (depth : Nat)
      (sourcePrefix : List VExpr)
      (source_eq : owner.source = sourcePrefix ++ source)
      (depth_eq : depth = sourcePrefix.length)
      (expression_eq : owner.expression = rawCapture.lift' (.skipN .refl depth))
      (left_eq : owner.expression.subst ownerLeft = leftValue)
      (right_eq : owner.expression.subst ownerRight = rightValue)
      (queryRank : Nat)
      (queryInput : Profile queryRank)
      (queryBound : n ≤ queryRank)
      (queryAdapter : GeneralNormalProfileAdapter env U registry target queryInput
        (raiseProfile queryRank queryBound input))
      (footprint : Footprint)
      (query : RichObs sourceEnv env U registry target owner.node ownerLocals ownerLeft queryInput footprint)
      (queryAvailable : footprint.Available ownerAvailable)
      (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
    ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
      RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input

inductive RawRichGroupEntries : {sourceEnv headerEnv : VEnv} → {U : Nat} → {source headerSource : List VExpr} →
    {fieldExpression fieldType majorExpression majorType A : VExpr} → {level : VLevel} →
    {field : EndpointRef sourceEnv U source fieldExpression fieldType} →
    {major : EndpointRef sourceEnv U source majorExpression majorType} →
    (domain : EndpointRef headerEnv U headerSource A (.sort level)) →
    (env : VEnv) → (registry : CanonicalHead.Registry) → (target : List VExpr) →
    (headerLocals : List Nat) → (declaredLeft : Subst) → (headerAvailable : Valuation) →
    (ownerInitial : List Closure) → (rawCapture leftValue rightValue : VExpr) → List Need → Type where
  | nil : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue []
  | cons {n : Nat} {input : Profile n} (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input)
      (tail : RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs) :
      RawRichGroupEntries (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue (captureNeeds input ++ needs)
end

variable {sourceEnv headerEnv env : VEnv} {U : Nat} {source headerSource target : List VExpr}
variable {fieldExpression fieldType majorExpression majorType A : VExpr} {level : VLevel}
variable {field : EndpointRef sourceEnv U source fieldExpression fieldType}
variable {major : EndpointRef sourceEnv U source majorExpression majorType}
variable {domain : EndpointRef headerEnv U headerSource A (.sort level)}
variable {registry : CanonicalHead.Registry} {headerLocals : List Nat} {declaredLeft : Subst}
variable {headerAvailable : Valuation} {ownerInitial : List Closure} {rawCapture leftValue rightValue : VExpr}
variable {n : Nat} {input : Profile n}

noncomputable def RawRichGroupEntry.owner
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    HeaderOwner field major := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact owner

noncomputable def RawRichGroupEntry.ownerLocals
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    List Nat := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact ownerLocals

noncomputable def RawRichGroupEntry.ownerLeft
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Subst := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact ownerLeft

noncomputable def RawRichGroupEntry.ownerRight
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Subst := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact ownerRight

noncomputable def RawRichGroupEntry.ownerAvailable
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Valuation := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact ownerAvailable

noncomputable def RawRichGroupEntry.initialContext
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    ContextDerivation sourceEnv U source := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact initialContext

noncomputable def RawRichGroupEntry.frame
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    RawOriginalRichFrame sourceEnv env U registry target
    (entry.owner.context entry.initialContext) entry.ownerLocals entry.ownerLeft entry.ownerRight entry.ownerAvailable := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact frame

noncomputable def RawRichGroupEntry.substitutions
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Ctx.SubstEq env U target entry.ownerLeft entry.ownerRight entry.owner.source := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact substitutions

noncomputable def RawRichGroupEntry.depth
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Nat := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact depth

noncomputable def RawRichGroupEntry.sourcePrefix
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    List VExpr := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact sourcePrefix

noncomputable def RawRichGroupEntry.source_eq
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.owner.source = entry.sourcePrefix ++ source := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact source_eq

noncomputable def RawRichGroupEntry.depth_eq
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.depth = entry.sourcePrefix.length := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact depth_eq

noncomputable def RawRichGroupEntry.expression_eq
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.owner.expression = rawCapture.lift' (.skipN .refl entry.depth) := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact expression_eq

noncomputable def RawRichGroupEntry.left_eq
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.owner.expression.subst entry.ownerLeft = leftValue := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact left_eq

noncomputable def RawRichGroupEntry.right_eq
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.owner.expression.subst entry.ownerRight = rightValue := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact right_eq

noncomputable def RawRichGroupEntry.queryRank
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Nat := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact queryRank

noncomputable def RawRichGroupEntry.queryInput
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Profile entry.queryRank := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact queryInput

noncomputable def RawRichGroupEntry.queryBound
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    n ≤ entry.queryRank := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact queryBound

noncomputable def RawRichGroupEntry.queryAdapter
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    GeneralNormalProfileAdapter env U registry target entry.queryInput (raiseProfile entry.queryRank entry.queryBound input) := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact queryAdapter

noncomputable def RawRichGroupEntry.footprint
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    Footprint := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact footprint

noncomputable def RawRichGroupEntry.query
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    RichObs sourceEnv env U registry target entry.owner.node entry.ownerLocals entry.ownerLeft entry.queryInput entry.footprint := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact query

noncomputable def RawRichGroupEntry.queryAvailable
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    entry.footprint.Available entry.ownerAvailable := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact queryAvailable

noncomputable def RawRichGroupEntry.answer
    (entry : RawRichGroupEntry (field := field) (major := major) domain env registry target headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue n input) :
    HeaderValueAlignment entry.owner domain env registry target entry.ownerLocals headerLocals
    entry.ownerLeft entry.ownerRight declaredLeft entry.ownerAvailable headerAvailable input := by
  cases entry with
  | mk owner ownerLocals ownerLeft ownerRight ownerAvailable initialContext frame substitutions depth sourcePrefix source_eq depth_eq expression_eq left_eq right_eq queryRank queryInput queryBound queryAdapter footprint query queryAvailable answer => exact answer


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
