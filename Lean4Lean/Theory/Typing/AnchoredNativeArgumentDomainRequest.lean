import Lean4Lean.Theory.Typing.AnchoredNativeSpineCertificate
import Lean4Lean.Theory.Typing.SourceApplicationFrame

/-! A selected original application's actual argument demand is pulled back
to the registered header as an empty-output Pi row. Empty output is essential:
this request concerns the argument domain, not a fabricated function result. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure NativeArgumentDomainRequest (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (A a : VExpr) (input : Profile n) where
  support : Profile n
  footprint : Footprint
  domain : CodeCert env U registry target locals σ A support footprint
  resources : footprint.Available available
  guard : LambdaGuard env U registry target σ A ⟨A.subst σ, a.subst σ, input⟩ support

namespace NativeArgumentDomainRequest
variable (request : NativeArgumentDomainRequest env U registry target locals σ available A a (input : Profile n))

def key (_request : NativeArgumentDomainRequest env U registry target locals σ available A a (input : Profile n)) : Key n := ⟨A.subst σ, a.subst σ, input⟩

def profile (B : VExpr) : Profile (n + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) request.support [(request.key, .empty)]

noncomputable def certificate (B : VExpr) :
    CodeCert env U registry target locals σ (.forallE A B) (request.profile B) request.footprint := by
  have body : CodeCert env U registry target (Locals.push locals)
      (σ.cons (a.subst σ)) B (.empty : Profile n) [] :=
    .seed .empty (Profile.HasType.empty (Profile.WF.sort true))
  have rows : PiRows env U registry target locals σ A B request.support
      [(request.key, .empty)] [] := by
    exact .cons request.guard body .nil (fun _ h => nomatch h) .nil
  simpa only [profile, List.append_nil] using CodeCert.piLiteral request.domain rows

end NativeArgumentDomainRequest

/-- Only the original argument child is interpreted. Its exact requested
support and source type certificate form the domain request at the same grade. -/
theorem OriginalTypePayload.argumentDomainRequest
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A a : VExpr}
    (original : OriginalTypePayload sourceEnv env U registry source a A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ a input footprint)
    (resources : footprint.Available available) :
    Nonempty (NativeArgumentDomainRequest env U registry target locals σ available A a input) := by
  obtain ⟨value⟩ := (original.2 target locals σ σ available closed hTarget substitutions fits).1
    observation resources
  have raw := (original.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have code := TypeRelated.lower henv value.bound value.typeCode
  have related := value.requestedRelated henv hTarget
  exact ⟨{
    support := lowerProfile n value.bound value.support
    footprint := value.typeFootprint
    domain := value.requestedCertificate
    resources := value.typeAvailable
    guard := ⟨value.requestedTyped, value.requestedCertificate.formed, .refl, code,
      ⟨raw, raw, _, value.requestedTyped, value.requestedCertificate.formed,
        code, related, related⟩⟩ }⟩

/-- Pull the actual selected argument-domain request through every original
application and function conversion back to its literal constant header.
There is no assumed argument typing at a registered domain. -/
theorem HasTypeStrong.argumentDomainSpine
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {f A B a : VExpr} {sf sa : Bool} {name : Name} {levels : List VLevel}
    (function : sourceEnv.HasTypeStrong U source f (.forallE A B) sf)
    (argument : sourceEnv.HasTypeStrong U source a A sa)
    (head : f.getAppFnArgs.1 = .const name levels)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ a input footprint)
    (resources : footprint.Available available) :
    ∃ request : NativeArgumentDomainRequest env U registry target locals σ available A a input,
      Nonempty (NativeSpineCertificate sourceEnv env U registry source target locals σ available
        name levels f (.forallE A B) (request.profile B) request.footprint) := by
  obtain ⟨request⟩ := OriginalTypePayload.argumentDomainRequest henv hle
    ⟨argument.refl, (earlier argument.refl).joint⟩ closed hTarget substitutions fits
    observation resources
  obtain ⟨spine⟩ := HasTypeStrong.spineCertificate henv hscoped hle earlier closed hTarget
    substitutions fits function head (request.certificate B) request.resources
  exact ⟨request, ⟨spine⟩⟩

/-- Select the actual original application frame at a native argument
position and construct its registered-header request. Conversion around the
whole application or any earlier function prefix is handled by original
proof recursion, without a literal registered-domain argument typing premise. -/
theorem HasTypeStrong.selectedArgumentDomainSpine
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {expression assigned : VExpr} {structural : Bool} {name : Name} {levels : List VLevel}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (position : Nat) (bound : position < expression.getAppFnArgs.2.length)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression.getAppFnArgs.2[position] input footprint)
    (resources : footprint.Available available) :
    ∃ frame : VEnv.OriginalApplicationFrame sourceEnv U source expression position,
    ∃ request : NativeArgumentDomainRequest env U registry target locals σ available
        frame.domain frame.argument input,
      Nonempty (NativeSpineCertificate sourceEnv env U registry source target locals σ available
        name levels frame.fn (.forallE frame.domain frame.body)
        (request.profile frame.body) request.footprint) := by
  obtain ⟨frame⟩ := VEnv.HasTypeStrong.applicationFrame original position bound
  have actual : Obs env U registry target locals σ frame.argument input footprint := by
    simpa only [frame.argument_eq bound] using observation
  obtain ⟨request, spine⟩ := HasTypeStrong.argumentDomainSpine henv hscoped hle earlier
    closed hTarget substitutions fits frame.functionTyped frame.argumentTyped
    (frame.head.trans head) actual resources
  exact ⟨frame, request, spine⟩

end Lean4Lean.AnchoredSource.Adapted
