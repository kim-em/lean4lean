import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySeedConsumption

/-! Actual family header metadata is independent of any nominal constant root. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure IndependentFamilyHeader (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) where
  registrationEnv : VEnv
  ordered : registrationEnv.Ordered
  below : registrationEnv ≤ env
  info : VConstant
  origin : ConstantHeaderOrigin registrationEnv name info
  lookup : env.constants name = some info
  notDefinition : registry.definitions name = none
  notNative : registry.natives name = none
  notQuotient : name ≠ ``Quot.lift
  seed : List VLevel
  seedWF : ∀ level ∈ seed, level.WF U
  seedLength : seed.length = info.uvars
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seed levels
  signature : ConstantTelescope (info.type.instL seed)
  typeClosed : info.type.Closed
  rank : Nat
  atom : Atom rank
  typeRealization : Subst
  typeSupport : Profile rank
  typeCertificate : RichCert origin.source env U registry target
    (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport []
  typed : (Profile.singleton atom).HasType typeSupport
  planRealization : Subst
  plan : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
    name seed signature .nil planRealization [] (.singleton atom) []

/-- Consumption starts at the exact retained header, under any actual caller
root. No nominal constant original is manufactured in the header's source. -/
noncomputable def IndependentFamilyHeader.atCaller
    (seed : IndependentFamilyHeader env U registry target name levels)
    (caller : EndpointRef callerEnv U source expression assigned) :
    RichFamilyPlanConsumption caller (seed.origin.familyHeader seed.seedWF).reference
      env registry target locals σ available name seed.seed seed.signature [] seed.atom :=
  .bare seed.plan



end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
