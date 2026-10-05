import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! Computational type-support certificates cannot query a Prop-valued
family descriptor. Sortable observations provide a distinct formation query;
its result can be produced by an actual original F transfer. No general
cross-typing transfer theorem is assumed here. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- This restriction applies to every certificate wrapper, not just seeds. -/
theorem CodeCert.family_relevant
    {family : FamilyData (Profile n)}
    (certificate : CodeCert env U registry target locals σ expression
      (Profile.singleton (n := n + 1) (.family family)) footprint) : family.relevant = true := by
  have typed := certificate.formed
  obtain ⟨atom, member, related⟩ := typed.2.2 _ (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  exact related

theorem CodeCert.noProofFamily
    {family : FamilyData (Profile n)} (irrelevant : family.relevant = false) :
    ¬ Nonempty (CodeCert env U registry target locals σ expression
      (Profile.singleton (n := n + 1) (.family family)) footprint) := by
  rintro ⟨certificate⟩
  have impossible := irrelevant.symm.trans certificate.family_relevant
  cases impossible

/-- A seed-only Bool generalization cannot carry a false-family result
through application: the old Pi-row grammar rejects that body outright. -/
theorem PiRows.noProofFamilyRow
    {family : FamilyData (Profile n)} {key : Key (n + 1)} {ambient : Profile (n + 1)}
    (irrelevant : family.relevant = false) :
    ¬ Nonempty (PiRows env U registry target locals σ A B ambient
      [(key, Profile.singleton (.family family))] footprint) := by
  rintro ⟨rows⟩
  cases rows with
  | cons guard body pack covered tail => exact CodeCert.noProofFamily irrelevant ⟨body⟩

/-- An ordinary sortable observation keeps its actual result observer and
adapter; its type relation does not impose the stronger sort-true condition
required by computational CodeCert. -/
structure SortableQueryResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right : VExpr) (requested : Profile n) where
  result : GradedResult env U registry target locals τ available right requested
  related : TypeRelated env U registry target (left.subst σ) (right.subst τ) requested

/-- The strengthened formation-query output is already available from a
fixed actual original F call, for either relevance flag. Producing it across
two unrelated original assigned types remains a C induction obligation. -/
theorem Obs.transferSortable
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (observation : Obs env U registry target locals σ left profile footprint)
    (sortable : profile.HasType (.sort relevant))
    (resources : footprint.Available available)
    (transfer : GradedTransfer env U registry target locals σ τ available left right assigned) :
    Nonempty (SortableQueryResult env U registry target locals σ τ available left right profile) := by
  obtain ⟨answer⟩ := transfer observation resources
  exact ⟨{
    result := {
      rank := answer.rank, bound := answer.bound, raw := answer.rawDemand
      footprint := answer.resultFootprint, observation := answer.observation
      adapter := answer.adapter, resources := answer.resultAvailable
      live := answer.rawRelated.live henv hscoped formed }
    related := (answer.requestedRelated henv formed).code_of_sortable henv hscoped formed sortable }⟩

end Lean4Lean.AnchoredSource.Adapted
