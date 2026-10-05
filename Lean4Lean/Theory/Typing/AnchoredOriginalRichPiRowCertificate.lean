import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredDomainChain

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail

structure RichPiRowCertificate (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (key : Key n) (result : Profile n) where
  domainSupport : Profile n
  domainFootprint : Footprint
  domain : RichCert sourceEnv env U registry target domainNode locals σ true domainSupport domainFootprint
  domainAvailable : domainFootprint.Available available
  inputTyped : key.input.HasType domainSupport
  alignment : DomainChain env U registry target key.input key.domain (A.subst σ)
  anchor : Admitted env U registry target key key.anchor key.anchor
  bodyFootprint : Footprint
  body : RichCert sourceEnv env U registry target bodyNode (Locals.push locals) (σ.cons key.anchor)
    relevant result bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms
  outsideAvailable : outside.Available available

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
