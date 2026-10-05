import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredRecordIntroduction

/-! The empty record source packet consumes only the original assigned type
certificate. In particular, observing a zero-field record requires no source
variable resource and no synthesized projection typing induction hypothesis. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure EmptyRecordObservation (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (assigned : VExpr) (family : FamilyData (Profile n)) where
  relevant : family.relevant = true
  info : VProjectionInfo
  lookup : registry.projections family.name = some info
  inert : CanonicalDataHead.HeadInert registry info.ctorName
  footprint : Footprint
  certificate : CodeCert env U registry target locals realization assigned
    (Profile.singleton (n := n + 1) (.family family)) footprint

noncomputable def EmptyRecordObservation.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (route : FutureInsertion env U target future ρ)
    {locals : List Nat} {σ : Subst} {assigned : VExpr} {family : FamilyData (Profile n)}
    (node : EmptyRecordObservation env U registry target locals σ assigned family) :
    EmptyRecordObservation env U registry future locals (σ.lift_r ρ) assigned
      (family.rename ρ) where
  relevant := node.relevant
  info := node.info
  lookup := node.lookup
  inert := node.inert
  footprint := Footprint.rename ρ node.footprint
  certificate := by
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.rename] using
      node.certificate.future henv route

/-- The only semantic induction hypothesis is the original formation child
for the assigned type. The term endpoints supply their existing raw typing
evidence; no computational observation of either endpoint is requested. -/
theorem EmptyRecordObservation.transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right assigned : VExpr} {level : VLevel}
    {family : FamilyData (Profile n)}
    (node : EmptyRecordObservation env U registry target locals σ assigned family)
    (original : env.IsDefEq U source left right assigned)
    (originalType : GradedJoint env U registry source assigned assigned (.sort level))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (resources : node.footprint.Available available) :
    ∃ next : EmptyRecordObservation env U registry target locals τ assigned family,
      next.footprint.Available available ∧
      Related env U registry target (left.subst σ) (right.subst τ) (assigned.subst σ)
        (Profile.singleton (n := n + 1) (.record ⟨family, node.relevant, []⟩))
        (.singleton (.family family)) := by
  obtain ⟨result⟩ := node.certificate.transfer_graded henv hscoped formed closed
    (originalType target locals σ τ available closed formed substitutions fits).1 resources
  let next : EmptyRecordObservation env U registry target locals τ assigned family := {
    relevant := node.relevant
    info := node.info
    lookup := node.lookup
    inert := node.inert
    footprint := result.footprint
    certificate := result.certificate }
  refine ⟨next, result.available, ?_⟩
  have raw := original.substDF henv substitutions.wf formed substitutions
  have code := result.related.left_diagonal
  exact Related.record henv hscoped
    (Profile.HasType.emptyRecord node.relevant node.certificate.formed.wf_value) code
    (RankedData.emptyRecord henv node.relevant node.lookup node.inert
      raw.hasType.1 raw.hasType.2 (code.familyRelation (List.mem_singleton_self _)))

end Lean4Lean.AnchoredSource.Adapted
