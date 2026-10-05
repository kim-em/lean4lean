import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRichComparison

/-! A finite rich-tail pilot. A binder's original formation and the captured
value's original assigned-type formation are different witnesses. Neither
is replaced by the other, and no rich certificate is erased to core syntax.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The exact finite part of a rich computational F answer needed to enter
a binder. The certificate may itself contain projected types or native Pi
queries; its occurrence is the captured value's computed type formation. -/
structure RichBinderValue
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {value A : VExpr}
    (owner : EndpointState sourceEnv U source value A)
    (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (input : Profile n) where
  support : Profile n
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target owner.typeFormation.node
    locals σ true support footprint
  resources : footprint.Available available
  typed : input.HasType support
  related : Related env U registry target (value.subst σ) (value.subst τ)
    (A.subst σ) input support

inductive RichTailFits (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : {source : List VExpr} → ContextDerivation sourceEnv U source →
      List Nat → Subst → Subst → Valuation → Type where
  | nil : RichTailFits sourceEnv env U registry target .nil locals σ τ available
  | push {n : Nat} {input : Profile n}
      {context : ContextDerivation sourceEnv U source}
      (tail : RichTailFits sourceEnv env U registry target context locals σ τ available)
      (originalDomain : EndpointRef sourceEnv U source A (.sort level))
      (owner : EndpointState sourceEnv U source value A)
      (provenance : EndpointProvenance context owner)
      (answer : RichBinderValue sourceEnv env U registry target owner locals σ τ available input)
      (needs : List Need)
      (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      RichTailFits sourceEnv env U registry target (.cons context originalDomain) (Locals.push locals)
        (σ.cons (value.subst σ)) (τ.cons (value.subst τ)) (available.push needs)

/-- The environment charges the actual captured value AND the separate
binder formation. It is not reconstructed from raw context equality. -/
def RichTailFits.environment
    {source : List VExpr} {context : ContextDerivation sourceEnv U source}
    (tail : RichTailFits sourceEnv env U registry target context locals σ τ available) : List Closure :=
  match tail with
  | .nil => []
  | .push tail domain owner .. =>
      .bundle (.close owner.origin tail.environment) (.close domain.origin tail.environment) :: tail.environment

/-- A rich projected argument is accepted without changing its own source
assigned-type certificate. This constructor also accepts a native Pi code
whose domain/body certificates contain further projections. -/
def RichTailFits.pushValue
    {source : List VExpr} {context : ContextDerivation sourceEnv U source}
    (tail : RichTailFits sourceEnv env U registry target context locals σ τ available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (owner : EndpointState sourceEnv U source value A)
    (provenance : EndpointProvenance context owner)
    (answer : RichBinderValue sourceEnv env U registry target owner locals σ τ available (input : Profile n))
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    RichTailFits sourceEnv env U registry target (.cons context domain) (Locals.push locals)
      (σ.cons (value.subst σ)) (τ.cons (value.subst τ)) (available.push needs) :=
  .push tail domain owner provenance answer needs bounded covered

/-- Reindexing is an explicit smaller original-pair obligation. The source
certificate remains indexed by its owner until that obligation returns an
actual certificate at the binder's original formation. -/
theorem RichBinderValue.reindexDomain
    {owner : EndpointState sourceEnv U source value A}
    (answer : RichBinderValue sourceEnv env U registry target owner locals σ τ available input)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (transfer : RichCodeTransfer env U registry target owner.typeFormation.node (.ref domain)
      locals locals σ σ available available) :
    Nonempty (RichCodeTransferResult env U registry target owner.typeFormation.node (.ref domain)
      locals σ σ available true answer.support) :=
  transfer answer.certificate answer.resources

/-- The variable's captured slot pays for this reindex pair, including an
arbitrarily rich projected assigned-type query. Query size is irrelevant. -/
theorem RichTailFits.head_reindex_schedule
    {source : List VExpr} {context : ContextDerivation sourceEnv U source}
    (tail : RichTailFits sourceEnv env U registry target context locals σ τ available)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (owner : EndpointState sourceEnv U source value A)
    (variableOrigin : Origin) :
    schedule .coherence
      ((Closure.close owner.typeFormation.node.origin tail.environment).cost +
       (Closure.close domain.origin tail.environment).cost) <
    schedule .fundamental
      (Closure.close variableOrigin
        (.bundle (.close owner.origin tail.environment) (.close domain.origin tail.environment) ::
          tail.environment)).cost := by
  apply schedule_strict
  have bounded := Nat.add_le_add_right (owner.typeFormation_cost_le tail.environment)
    (Closure.close domain.origin tail.environment).cost
  exact Nat.lt_of_le_of_lt bounded
    (variable_lookup variableOrigin (List.mem_cons_self :
      Closure.bundle (.close owner.origin tail.environment) (.close domain.origin tail.environment) ∈
        _ :: tail.environment))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
