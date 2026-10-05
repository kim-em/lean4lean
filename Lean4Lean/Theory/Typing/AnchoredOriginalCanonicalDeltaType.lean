import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaPacket
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue
import Lean4Lean.Theory.Typing.AnchoredLevels

/-! A closed type-query wrapper for canonical delta return. Its child is the
computed assigned formation of the actual canonical RHS endpoint, precisely
where the RHS fundamental answer returns its certificate. The caller's original
formation is retained independently. No comparison between those two original
proofs is used to construct this packet or its type semantics. This is an
isolated grammar prototype, not an added constructor of `RichCert`. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure CanonicalDeltaTypePacket (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env)
    (expression : VExpr) (relevant : Bool) (profile : Profile n) where
  value : VDefVal
  lookup : registry.definitions value.name = some value
  registered : DefinitionRegistered env value
  seedLevels : List VLevel
  seedWF : ∀ level ∈ seedLevels, level.WF U
  levels : List VLevel
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seedLevels levels
  typeClosed : value.type.Closed
  expressionEq : expression = value.type.instL levels
  realization : Subst
  footprint : Footprint
  certificate : RichCert (strata.select registered.2).origin.source env U registry target
    (EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs
      (strata.select registered.2).origin seedWF))).typeFormation.node
    [] realization relevant profile footprint
  resources : footprint.Available (fun _ => [])

namespace CanonicalDeltaTypePacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {expression : VExpr} {relevant : Bool} {profile : Profile n}

noncomputable def nativeDepth
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile)
    (current : Name → Bool) : Nat :=
  packet.certificate.nativeDepth current + if current packet.value.name then 1 else 0

theorem formed
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) :
    profile.HasType (.sort relevant) := packet.certificate.formed

/-- Interpreting the one actual retained child provides type semantics at
any caller substitution because the displayed original type is closed. -/
theorem related
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile)
    (henv : env.Ordered)
    (child : TypeRelated env U registry target
      ((packet.value.type.instL packet.seedLevels).subst packet.realization)
      ((packet.value.type.instL packet.seedLevels).subst packet.realization) profile)
    (σ τ : Subst) :
    TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  have seed : TypeRelated env U registry target
      (packet.value.type.instL packet.seedLevels) (packet.value.type.instL packet.seedLevels) profile := by
    simpa only [packet.typeClosed.instL.subst_eq (σ := packet.realization) .zero] using child
  have comparison := EqUpToLevels.instL_expr packet.value.type
    packet.seedWF packet.levelsWF packet.equivalent
  simpa only [packet.expressionEq, packet.typeClosed.instL.subst_eq (σ := σ) .zero,
    packet.typeClosed.instL.subst_eq (σ := τ) .zero] using seed.levels henv comparison comparison

end CanonicalDeltaTypePacket

/-- The actual caller formation remains the node of the wrapper, even when
its source environment lacks the canonical packet's other constants. -/
structure CanonicalDeltaTypeAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source expression (.sort level))
    (locals : List Nat) (σ : Subst) (relevant : Bool) (profile : Profile n) where
  packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile

def CanonicalDeltaTypeAt.reindex
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant profile)
    (destination : EndpointState destinationEnv U destinationSource expression (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    CanonicalDeltaTypeAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst relevant profile := ⟨query.packet⟩

/-- Delta return packages the SAME certificate produced by the fixed actual
canonical RHS F call. No canonical-type/caller-formation C or R reply is supplied. -/
noncomputable def CanonicalDeltaPacket.returnType
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
    (locals : List Nat) (σ : Subst) :
    CanonicalDeltaTypeAt sourceEnv env U registry target strata caller locals σ true answer.support :=
  ⟨{ value := packet.value
     lookup := by simpa only [packet.nameEq] using packet.lookup
     registered := packet.registered
     seedLevels := packet.seedLevels
     seedWF := packet.seedWF
     levels := assignedLevels
     levelsWF := assignedWF
     equivalent := seedAssigned
     typeClosed := packet.typeClosed
     expressionEq := rfl
     realization := packet.bodyRealization
     footprint := answer.footprint
     certificate := answer.certificate
     resources := answer.resources }⟩

theorem CanonicalDeltaPacket.returnType_related
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (henv : env.Ordered)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
    (locals : List Nat) (σ τ : Subst) :
    TypeRelated env U registry target
      ((packet.value.type.instL assignedLevels).subst σ) ((packet.value.type.instL assignedLevels).subst τ)
      answer.support :=
  (packet.returnType answer assignedWF seedAssigned caller locals σ).packet.related henv answer.typeCode σ τ

/-- The returned wrapper spends precisely the same head as its incoming
value packet. This equation concerns the actual retained F certificate. -/
theorem CanonicalDeltaPacket.returnType_depth
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (answer : RichSupportedValue packet.selected.origin.source env U registry target
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs packet.selected.origin packet.seedWF)))
      [] packet.bodyRealization packet.bodyRealization (fun _ => []) profile)
    (assignedWF : ∀ level ∈ assignedLevels, level.WF U)
    (seedAssigned : List.Forall₂ (· ≈ ·) packet.seedLevels assignedLevels)
    (caller : EndpointState sourceEnv U source (packet.value.type.instL assignedLevels) (.sort level))
    (locals : List Nat) (σ : Subst) (current : Name → Bool) :
    (packet.returnType answer assignedWF seedAssigned caller locals σ).packet.nativeDepth current =
      answer.certificate.nativeDepth current + if current name then 1 else 0 := by
  simp only [returnType, CanonicalDeltaTypePacket.nativeDepth, packet.nameEq]

end Lean4Lean.AnchoredSource.Adapted
