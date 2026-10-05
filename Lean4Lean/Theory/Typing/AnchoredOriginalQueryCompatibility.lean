import Lean4Lean.Theory.Typing.AnchoredOriginalEndpointFactor
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFits

/-! Exact source context frames for original endpoint queries. Every binder
formation reached through computed exposure is an actual original reference.
Consequently a location extends the supplied original context spine without
reifying a synthetic endpoint's soundness proof. This is context provenance,
not a hereditary typed-observer interpretation theorem. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

private def IsReference (node : EndpointState env U Γ expression type) : Prop :=
  ∃ reference, node = .ref reference

/-- References remain lazy; exposing one separately reestablishes this
invariant from its actual original derivation. -/
def EndpointState.OriginalDomains : EndpointState env U Γ expression type → Prop
  | .ref _ | .sort _ => True
  | .bvar _ _ formation => formation.OriginalDomains
  | .app _ _ domain codomain fn arg result =>
      IsReference domain ∧ domain.OriginalDomains ∧ codomain.OriginalDomains ∧
        fn.OriginalDomains ∧ arg.OriginalDomains ∧ result.OriginalDomains
  | .lam _ _ domain codomain body =>
      IsReference domain ∧ domain.OriginalDomains ∧ codomain.OriginalDomains ∧ body.OriginalDomains
  | .pi _ _ domain body =>
      IsReference domain ∧ domain.OriginalDomains ∧ body.OriginalDomains
  | .proj _ _ _ _ _ _ _ field _ _ _ => field.OriginalDomains
  | .convert _ term => term.OriginalDomains

@[simp] theorem EndpointState.originalDomains_cast
    (expressionEq : expression = expression') (typeEq : type = type')
    (node : EndpointState env U Γ expression type) :
    (node.cast expressionEq typeEq).OriginalDomains ↔ node.OriginalDomains := by
  cases expressionEq
  cases typeEq
  rfl

theorem Derivation.expose_originalDomains (original : Derivation env U Γ left right type) :
    original.expose.1.OriginalDomains ∧ original.expose.2.OriginalDomains := by
  induction original with
  | symm original ih => exact ih.symm
  | trans first second ihFirst ihSecond => exact ⟨ihFirst.1, ihSecond.2⟩
  | beta _ _ _ _ _ _ _ instantiated _ _ _ _ _ ih =>
    exact ⟨⟨⟨_, rfl⟩, trivial, trivial, ⟨⟨_, rfl⟩, trivial, trivial, trivial⟩, trivial, trivial⟩, ih.1⟩
  | eta hu hv domain codomain liftedCodomain term liftedTerm liftedDomain _ _ _ ih _ _ =>
    refine ⟨⟨⟨_, rfl⟩, trivial, trivial, ?_⟩, ih.1⟩
    change (EndpointState.cast rfl (inst_liftN_bvar _ 0) _).OriginalDomains
    rw [EndpointState.originalDomains_cast]
    exact ⟨⟨_, rfl⟩, trivial, trivial, trivial, trivial, by
      rw [EndpointState.originalDomains_cast]; trivial⟩
  | proofIrrel _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra _ _ _ _ _ _ _ left right _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | elimIota _ _ _ _ _ _ _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | projIota _ projection _ field ihProjection ihField => exact ⟨ihProjection.1, ihField.1⟩
  | structEta _ _ _ major constructor ihMajor ihConstructor => exact ⟨ihConstructor.1, ihMajor.1⟩
  | unitLike _ _ _ _ left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | _ => simp [Derivation.expose, EndpointState.OriginalDomains, IsReference]

theorem EndpointRef.expose_originalDomains (reference : EndpointRef env U Γ expression type) :
    reference.expose.OriginalDomains := by
  cases reference with
  | left original => exact original.expose_originalDomains.1
  | right original => exact original.expose_originalDomains.2

theorem Derivation.typeFormation_OriginalDomains
    (original : Derivation env U Γ left right type) :
    original.typeFormation.node.OriginalDomains := by
  induction original <;> simp_all [Derivation.typeFormation, EndpointState.OriginalDomains, IsReference]

theorem EndpointRef.typeFormation_OriginalDomains
    (reference : EndpointRef env U Γ expression type) :
    reference.typeFormation.node.OriginalDomains := by
  cases reference with
  | left original => exact original.typeFormation_OriginalDomains
  | right original => exact original.typeFormation_OriginalDomains

theorem EndpointConversion.targetFormation_OriginalDomains
    (plan : EndpointConversion env U Γ A B) :
    plan.targetFormation.node.OriginalDomains := by
  cases plan <;> simp [EndpointConversion.targetFormation, EndpointState.OriginalDomains, IsReference]

theorem EndpointState.typeFormation_OriginalDomains
    (node : EndpointState env U Γ expression type) (original : node.OriginalDomains) :
    node.typeFormation.node.OriginalDomains := by
  cases node with
  | ref reference => exact reference.typeFormation_OriginalDomains
  | convert plan term => exact plan.targetFormation_OriginalDomains
  | _ => simp_all [EndpointState.typeFormation, EndpointState.OriginalDomains]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

theorem Located.originalDomains (location : Located root node) : node.OriginalDomains := by
  induction location with
  | here => trivial
  | expose => exact EndpointRef.expose_originalDomains _
  | convertTerm _ ih => exact ih
  | appPiFormation _ ih => exact ⟨ih.1, ih.2.1, ih.2.2.1⟩
  | appDomain _ ih => exact ih.2.1
  | appCodomain _ ih => exact ih.2.2.1
  | appFunction _ ih => exact ih.2.2.2.1
  | appArgument _ ih => exact ih.2.2.2.2.1
  | appResult _ ih => exact ih.2.2.2.2.2
  | lamDomain _ ih | piDomain _ ih => exact ih.2.1
  | lamCodomain _ ih => exact ih.2.2.1
  | lamBody _ ih => exact ih.2.2.2
  | piBody _ ih => exact ih.2.2
  | projField _ ih => exact ih
  | projMajor _ _ => trivial
  | assignedFormation _ ih => exact EndpointState.typeFormation_OriginalDomains _ ih

/-- Extend the supplied exact context spine only at actual binder edges.
No context proof is reconstructed from a raw typing judgment. -/
noncomputable def Located.contextDerivation
    {root : EndpointRef env U source expression type}
    {node : EndpointState env U context selectedExpression selectedType}
    (location : Located root node) (initial : ContextDerivation env U source) :
    ContextDerivation env U context := by
  induction location with
  | here => exact initial
  | expose _ ih | convertTerm _ ih | appDomain _ ih | appResult _ ih | appFunction _ ih | appArgument _ ih | lamDomain _ ih | piDomain _ ih | projField _ ih | projMajor _ ih | assignedFormation _ ih | appPiFormation _ ih => exact ih
  | appCodomain parent ih | lamCodomain parent ih | lamBody parent ih | piBody parent ih =>
    exact .cons ih (Classical.choose parent.originalDomains.1)

/-- The reconstructed context captures exactly the environment already paid
for by the location's original closure bound. -/
theorem Located.contextDerivation_closures
    {root : EndpointRef env U source expression type}
    {node : EndpointState env U context selectedExpression selectedType}
    (location : Located root node) (initial : ContextDerivation env U source) :
    (location.contextDerivation initial).closures = location.environment initial.closures := by
  induction location with
  | here => rfl
  | expose _ ih | convertTerm _ ih | appDomain _ ih | appResult _ ih | appFunction _ ih | appArgument _ ih | lamDomain _ ih | piDomain _ ih | projField _ ih | projMajor _ ih | assignedFormation _ ih | appPiFormation _ ih => exact ih
  | appCodomain parent ih | lamCodomain parent ih | lamBody parent ih | piBody parent ih =>
    have equal := Classical.choose_spec parent.originalDomains.1
    have originEq := congrArg EndpointState.origin equal
    simp only [EndpointState.origin] at originEq
    change Closure.close (Classical.choose parent.originalDomains.1).origin
      (parent.contextDerivation initial).closures :: (parent.contextDerivation initial).closures =
      Closure.close _ (parent.environment initial.closures) :: parent.environment initial.closures
    rw [ih, originEq]

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv

/-- A literal suffix of the finite original formation spine. -/
inductive ContextDerivation.Suffix (tail : ContextDerivation env U source) :
    {context : List VExpr} → ContextDerivation env U context → Type where
  | refl : Suffix tail tail
  | cons (previous : Suffix tail context) : Suffix tail (.cons context domain)

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv OriginalClosureMeasure

theorem Located.contextDerivation_suffix
    {root : EndpointRef env U source expression type}
    {node : EndpointState env U context selectedExpression selectedType}
    (location : Located root node) (initial : ContextDerivation env U source) :
    Nonempty (ContextDerivation.Suffix initial (location.contextDerivation initial)) := by
  induction location with
  | here => exact ⟨.refl⟩
  | expose _ ih | convertTerm _ ih | appDomain _ ih | appResult _ ih | appFunction _ ih | appArgument _ ih | lamDomain _ ih | piDomain _ ih | projField _ ih | projMajor _ ih | assignedFormation _ ih | appPiFormation _ ih => exact ih
  | appCodomain _ ih | lamCodomain _ ih | lamBody _ ih | piBody _ ih =>
    exact ⟨.cons (Classical.choice ih)⟩

/-- At an actual variable occurrence, selecting the original context tail
produces the concrete type-coherence call and its strict local schedule.
The occurrence formation may be a synthetic endpoint state; it is not
reified as a newly manufactured original derivation. -/
theorem Located.lookup_reindex_schedule
    {root : EndpointRef env U source rootExpression rootType}
    (initial : ContextDerivation env U source)
    {lookup : Lookup context index assigned} {levelWF : level.WF U}
    {formation : EndpointState env U context assigned (.sort level)}
    (location : Located root (.bvar lookup levelWF formation)) :
    ∃ entry : ContextDerivation.LookupOrigin (location.contextDerivation initial) index assigned,
      schedule .coherence
        ((Closure.close formation.origin (location.contextDerivation initial).closures).cost +
          (Closure.close entry.formation.origin entry.tail.closures).cost) <
        schedule .fundamental
          (Closure.close (EndpointState.bvar lookup levelWF formation).origin
            (location.environment initial.closures)).cost := by
  obtain ⟨entry⟩ := (location.contextDerivation initial).lookupOrigin lookup
  refine ⟨entry, ?_⟩
  have bound := lookup_type_reindex formation.origin
    (.close entry.formation.origin entry.tail.closures)
    (location.contextDerivation initial).closures entry.cost_le
  have strict := schedule_strict bound Phase.coherence Phase.fundamental
  simpa only [EndpointState.origin, location.contextDerivation_closures initial] using strict

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure

/-- Current certificates have no embedded source-typing index. Replace only
formation provenance along the same literal source context; preserve every
certificate, finite demand and semantic argument field. This operation makes
no claim about reindexing a future hereditary typed certificate grammar. -/
def TailFits.reorigin
    (fits : TailFits sourceEnv env U registry target source locals left right available)
    (desired : ContextDerivation sourceEnv U source) :
    TailFits sourceEnv env U registry target source locals left right available :=
  match fits, desired with
  | .nil, .nil => .nil
  | .push tail _ domain resources typed arguments needs bounded covered, .cons rest originalDomain =>
      .push (tail.reorigin rest) originalDomain domain resources typed arguments needs bounded covered

theorem TailFits.reorigin_contextDerivation
    (fits : TailFits sourceEnv env U registry target source locals left right available)
    (desired : ContextDerivation sourceEnv U source) :
    (fits.reorigin desired).contextDerivation = desired := by
  induction fits with
  | nil => cases desired; rfl
  | push tail originalDomain domain resources typed arguments needs bounded covered ih =>
    cases desired with
    | cons rest formation =>
      change ContextDerivation.cons ((tail.reorigin rest).contextDerivation) formation = _
      rw [ih rest]

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
