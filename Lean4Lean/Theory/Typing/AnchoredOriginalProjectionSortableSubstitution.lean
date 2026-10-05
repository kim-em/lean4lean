import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableProducer
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixApplication

/-! The exact reconstruction boundary for the endpoint-indexed proposal.
These are finite data and explicit proof goals, not supplied semantic clauses.
In particular no result here claims that a residual source template inherits
an original typing from the instantiated expression's raw typing.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

/-- A replacement retains its actual original argument state and its finite
adapted query. It does not acquire the declaration binder's assigned type. -/
structure RichGradedResult
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  footprint : Footprint
  observation : RichObs sourceEnv env U registry target node locals σ raw footprint
  adapter : GeneralNormalProfileAdapter env U registry target raw (raiseProfile rank bound requested)
  resources : footprint.Available available
  live : Profile.Live env U registry target raw

/-- The pack has finitely many requested local needs. Each replacement is
a concrete source query at the same actual argument occurrence. -/
inductive RichArgumentSupply
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation) : List Need → Type where
  | nil : RichArgumentSupply sourceEnv env U registry target node locals σ available []
  | cons (value : RichGradedResult sourceEnv env U registry target node locals σ available need.profile)
      (tail : RichArgumentSupply sourceEnv env U registry target node locals σ available needs) :
      RichArgumentSupply sourceEnv env U registry target node locals σ available (need :: needs)

/-- A whole cut keeps its pre-reflection query at the actual input location.
Its projection field certificate is not silently reflected or relabelled. -/
inductive WholeRichCut
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : CutOriginAt root boundary argument baseDepth)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (realization : Subst) :
    {n : Nat} → Profile n → Footprint → Type where
  | observed (query : RichObs sourceEnv env U registry target origin.view locals realization demand footprint) :
      WholeRichCut (env := env) origin registry target locals realization demand footprint
  | sortable (query : RichCert sourceEnv env U registry target origin.view locals realization relevant demand footprint) :
      WholeRichCut (env := env) origin registry target locals realization demand footprint

/-- A retained whole cut charged to the actual result child of one source
application. The tail realization equality is syntactic source substitution;
the payload remains at its original, possibly larger, source context. -/
structure ApplicationCut
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst) where
  boundary : List VExpr
  origin : CutOriginAt root boundary argument 0
  locals : List Nat
  realization : Subst
  tail : Subst.lift_l (.skipN .refl origin.depth) realization = σ
  need : Need
  footprint : Footprint
  query : WholeRichCut (env := env) origin registry target locals realization need.profile footprint
  bounded : ∀ initial, (Closure.close origin.view.origin (origin.location.environment initial)).cost ≤
    (Closure.close view.result.origin (view.location.environment initial)).cost

/-- The real application reserve covers reindexing a retained cut against
the actual argument. This statement is independent of which query grammar
the cut retains, so the old location proof survives the extension. -/
theorem ApplicationCut.argument_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (cut : ApplicationCut (env := env) view registry target σ) (initial : List Closure) :
    schedule .coherence ((Closure.close cut.origin.view.origin
      (cut.origin.location.environment initial)).cost +
      (Closure.close view.argument.origin (view.location.environment initial)).cost) <
    schedule .fundamental (Closure.close root.origin initial).cost := by
  exact schedule_strict (Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (cut.bounded initial) _)
      (view.result_argument_cost_lt initial)) (start.cost_le initial)) _ _

/-- The required source result is tied to the application's actual result
formation child, rather than a typing synthesized for `B[a]`. -/
structure RichInstantiationResult
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (profile : Profile n) where
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target view.result locals σ relevant profile footprint
  resources : footprint.Available available

/-- Open structural/typed reconstruction obligation for the new grammar.
It states the complete one-binder substitution needed by application replay,
with arbitrary Boolean code rows, native Pi domains, finite graded argument
queries and all external resources. No theorem assumes this proposition.

Whole cuts have the strict schedule proved above. A proof must additionally
reindex every retained projection's field metadata from the original body
occurrence to the actual result occurrence; endpoint indices cannot be cast
using only equality of the displayed expressions. -/
def AppView.RichSubstitutionContract
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (registry : CanonicalHead.Registry) (target : List VExpr) : Prop :=
  ∀ (locals : List Nat) (σ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    ∀ {relevant : Bool} {n : Nat} {profile packed : Profile n} {bodyFootprint outside : Footprint},
      RichCert sourceEnv env U registry target view.codomain (Locals.push locals)
        (σ.cons (argument.subst σ)) relevant profile bodyFootprint →
      BinderPack n packed bodyFootprint outside → outside.Available available →
      RichArgumentSupply sourceEnv env U registry target view.argument locals σ available
        (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) →
      Nonempty (RichInstantiationResult (env := env) view registry target locals σ available relevant profile)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
