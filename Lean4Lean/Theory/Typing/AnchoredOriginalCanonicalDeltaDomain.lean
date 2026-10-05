import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaType
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix
import Lean4Lean.Theory.Typing.EquationControls
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule

/-! A finite domain elimination of a charged canonical type query. The whole
Pi packet stays in the recipe: stripping its named head would expose lower
controls that were masked during canonical opening. Interpretation opens the
actual canonical formation once and then extracts its literal target domain.
It never calls F on a larger caller-side Pi proof. This remains an isolated
grammar candidate, not a constructor of `RichCert`. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDeltaTypePacket
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {expression : VExpr} {relevant : Bool} {profile : Profile n}

noncomputable def chargeDepth
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) : Nat → Nat :=
  headDepth (strata.select packet.registered.2).ordinal
    (fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control)

noncomputable def codeNode
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) :=
  (EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs
    (strata.select packet.registered.2).origin packet.seedWF))).typeFormation.node

noncomputable def codeSchedule
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile) : Nat :=
  richSchedule .fundamental
    (Closure.close (packet.codeNode.dependencyOrigin (strata.select packet.registered.2).origin.ordered) []).cost

/-- The lower original F clause is specialized to the retained certificate's
actual canonical formation and empty frame. Its applicability is guarded by
both source cutoff and the computed alternating-order decrease. -/
def CodeBelow
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile)
    (parentKey : EquationControlMeasure.Key strata.rules.length) : Prop :=
  ∀ {footprint : Footprint}
    (query : RichObs (strata.select packet.registered.2).origin.source env U registry target
      packet.codeNode [] packet.realization profile footprint),
    footprint.Available (fun _ => []) → ∀ fuel : Nat → Nat,
    WithinAbove ((strata.select packet.registered.2).ordinal - 1) fuel
      (fun control => query.stratifiedDepth (strata.headOrdinal registry) control) →
    strata.SourceCutoff (strata.select packet.registered.2).origin.source
      ((strata.select packet.registered.2).ordinal - 1) →
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length
        ((strata.select packet.registered.2).ordinal - 1) fuel
        (strata.select packet.registered.2).origin.ordered.constantCount packet.codeSchedule) parentKey →
    Nonempty (RichComputationalValue (strata.select packet.registered.2).origin.source
      env U registry target packet.codeNode [] packet.realization packet.realization
      (fun _ => []) profile)

/-- Fuse opening with interpretation of the actual whole certificate. There
is no F call on the caller endpoint, so a later domain/body elimination cannot
accidentally replace its strict head-fuel decrease by a larger caller proof. -/
theorem interpret
    (packet : CanonicalDeltaTypePacket env U registry target strata expression relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel packet.chargeDepth)
    (lower : packet.CodeBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (σ τ : Subst) :
    TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  let selected := strata.select packet.registered.2
  let children := fun control => packet.certificate.stratifiedDepth (strata.headOrdinal registry) control
  have decrease := openingDecrease selected.ordinal_pos selected.ordinal_le cutoffBound bounded
    constants callerSchedule selected.origin.ordered.constantCount packet.codeSchedule
  obtain ⟨answer⟩ := lower (.code packet.certificate) packet.resources children (by
    intro control _
    simp only [RichObs.stratifiedDepth, RichObs.headDepth]
    exact Nat.le_refl _) selected.sourceCutoff decrease
  exact packet.related henv
    (answer.related.code_of_sortable henv hscoped formed packet.formed) σ τ

end CanonicalDeltaTypePacket

structure CanonicalDeltaDomainRecipe (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env) (domain : VExpr) (support : Profile n) where
  body : VExpr
  relevant : Bool
  prototypeDomain : VExpr
  prototypeBody : VExpr
  rows : List (Key n × Profile n)
  parent : CanonicalDeltaTypePacket env U registry target strata (.forallE domain body)
    relevant (.pi prototypeDomain prototypeBody support rows)

namespace CanonicalDeltaDomainRecipe
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {domain : VExpr} {support : Profile n}

noncomputable def depth (recipe : CanonicalDeltaDomainRecipe env U registry target strata domain support) : Nat → Nat :=
  recipe.parent.chargeDepth

theorem formed (recipe : CanonicalDeltaDomainRecipe env U registry target strata domain support) :
    support.HasType (.sort true) :=
  (Profile.WF.pi_iff.mp recipe.parent.formed.1).1

theorem related (recipe : CanonicalDeltaDomainRecipe env U registry target strata domain support)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (child : TypeRelated env U registry target
      ((recipe.parent.value.type.instL recipe.parent.seedLevels).subst recipe.parent.realization)
      ((recipe.parent.value.type.instL recipe.parent.seedLevels).subst recipe.parent.realization)
      (.pi recipe.prototypeDomain recipe.prototypeBody support recipe.rows))
    (σ τ : Subst) :
    TypeRelated env U registry target (domain.subst σ) (domain.subst τ) support := by
  exact TypeRelated.literalPiDomain henv hscoped formed
    (by simpa only [subst] using recipe.parent.related henv child σ τ)

/-- The domain interpreter keeps the charged whole packet and performs the
actual canonical formation call before pure literal-Pi elimination. -/
theorem interpret (recipe : CanonicalDeltaDomainRecipe env U registry target strata domain support)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat) (bounded : WithinAbove cutoff fuel recipe.depth)
    (lower : recipe.parent.CodeBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (σ τ : Subst) :
    TypeRelated env U registry target (domain.subst σ) (domain.subst τ) support := by
  exact TypeRelated.literalPiDomain henv hscoped formed (by
    simpa only [subst] using recipe.parent.interpret henv hscoped formed cutoff cutoffBound
      fuel constants callerSchedule bounded lower σ τ)

end CanonicalDeltaDomainRecipe

/-- The actual destination domain node is independent of the stored closed
parent packet. Expression R can copy the recipe without inventing a destination
Pi parent or changing the original canonical certificate. -/
structure CanonicalDeltaDomainAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source domain (.sort level))
    (locals : List Nat) (σ : Subst) (support : Profile n) where
  recipe : CanonicalDeltaDomainRecipe env U registry target strata domain support

def CanonicalDeltaDomainAt.reindex
    {node : EndpointState sourceEnv U source domain (.sort level)}
    (query : CanonicalDeltaDomainAt sourceEnv env U registry target strata node locals σ support)
    (destination : EndpointState destinationEnv U destinationSource domain (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    CanonicalDeltaDomainAt destinationEnv env U registry target strata destination
      destinationLocals destinationSubst support := ⟨query.recipe⟩

@[simp] theorem CanonicalDeltaDomainAt.reindex_depth
    {node : EndpointState sourceEnv U source domain (.sort level)}
    (query : CanonicalDeltaDomainAt sourceEnv env U registry target strata node locals σ support)
    (destination : EndpointState destinationEnv U destinationSource domain (.sort destinationLevel))
    (destinationLocals : List Nat) (destinationSubst : Subst) :
    (query.reindex destination destinationLocals destinationSubst).recipe.depth = query.recipe.depth := rfl

/-- The source extraction starts at its actual original Pi route. Its output
retains the whole charged parent, including the complete requested row table. -/
def CanonicalDeltaTypeAt.piDomain
    {node : EndpointState sourceEnv U source (.forallE A B) (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant
      (.pi prototypeDomain prototypeBody (support : Profile n) rows))
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (_route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body)) :
    CanonicalDeltaDomainAt sourceEnv env U registry target strata domain locals σ support :=
  ⟨⟨B, relevant, prototypeDomain, prototypeBody, rows, query.packet⟩⟩

@[simp] theorem CanonicalDeltaTypeAt.piDomain_depth
    {node : EndpointState sourceEnv U source (.forallE A B) (.sort level)}
    (query : CanonicalDeltaTypeAt sourceEnv env U registry target strata node locals σ relevant
      (.pi prototypeDomain prototypeBody (support : Profile n) rows))
    (hu : u.WF U) (hv : v.WF U)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domain body)) :
    (query.piDomain hu hv domain body route).recipe.depth = query.packet.chargeDepth := rfl

end Lean4Lean.AnchoredSource.Adapted
