import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionRecursiveSubstitution

/-! Query-local resources for a captured endpoint. The head valuation is
exactly the finite local needs of this query, with singleton closure. Its
replacement observations are produced by F at the actual original argument.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalRecordSource
set_option backward.isDefEq.respectTransparency false

def captureNeeds (required : Footprint) : List Need :=
  required.localNeeds ++ required.localNeeds.flatMap Need.singletons

structure CapturedQueryFrame
    (display : CapturedEndpointDisplay sourceEnv U Γ e A)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (common : Subst) (locals : List Nat) (available : Valuation)
    (required outside : Footprint) where
  captureRank : Nat
  packed : Profile captureRank
  pack : BinderPack captureRank packed required outside
  replacements : RichArgumentSupply sourceEnv env U registry target (.ref display.argument)
    locals (display.baseSubst common) available (captureNeeds required)
  outsideAvailable : outside.Available available
  fitted : SortableTailPairedFits env registry target (.cons display.context display.domain)
    (Locals.push locals) (display.sourceSubst common) (display.sourceSubst common)
    (available.push (captureNeeds required))
  substitutions : Ctx.SubstEq env U target (display.sourceSubst common)
    (display.sourceSubst common) (display.domainExpression :: display.source)
  closed : (available.push (captureNeeds required)).AtomClosed
  resources : required.Available (available.push (captureNeeds required))

def CapturedQueryFrame.footprint
    (frame : CapturedQueryFrame display env registry target common locals available required outside) : Footprint :=
  outside ++ frame.replacements.footprint

theorem CapturedQueryFrame.available {available : Valuation}
    (frame : CapturedQueryFrame display env registry target common locals available required outside) :
    frame.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.outsideAvailable i need)
    (frame.replacements.available i need)

/-- The original argument is the sole computational call. The query's
finite binder pack determines every admitted local need. No valuation fitted
to all future queries or erased rich replacement is assumed. -/
theorem CapturedEndpointDisplay.fitQuery
    (display : CapturedEndpointDisplay sourceEnv U Γ e A)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (argumentF : StateHereditaryFundamental env registry display.context (.ref display.argument))
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target (display.baseSubst common)
      (display.baseSubst common) display.source)
    (tails : SortableTailPairedFits env registry target display.context locals
      (display.baseSubst common) (display.baseSubst common) available)
    {input packed : Profile captureRank}
    (pack : BinderPack captureRank packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
    (outsideResources : outside.Available available)
    (argumentQuery : SortableObs env U registry target locals (display.baseSubst common)
      display.argumentExpression input argumentFootprint)
    (argumentResources : argumentFootprint.Available available) :
    Nonempty (CapturedQueryFrame display env registry target common locals available required outside) := by
  obtain ⟨answer⟩ := argumentF target locals _ _ available closed formed substitutions tails
    argumentQuery argumentResources
  have arguments := answer.requestedRelated henv formed
  have bounded : ∀ need ∈ captureNeeds required, need.rank ≤ captureRank :=
    fun need member => (pack.atomized_localNeeds need member).1
  have included : ∀ need ∈ captureNeeds required, ∀ atom ∈ (need.atGrade captureRank).atoms,
      atom ∈ input.atoms :=
    fun need member atom present => covered atom ((pack.atomized_localNeeds need member).2 atom present)
  let fitted := tails.pushCertificates display.domain answer.requestedCertificate answer.requestedCertificate
    answer.typeAvailable answer.typeAvailable answer.requestedTyped answer.requestedTyped
    arguments arguments (captureNeeds required) bounded included
  have rawArgument := (display.argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  have instantiated : Ctx.SubstEq env U target (display.sourceSubst common)
      (display.sourceSubst common) (display.domainExpression :: display.source) :=
    .cons substitutions (display.domain.sound.defeq.mono below) rawArgument
  exact ⟨{
    captureRank := captureRank
    packed := packed
    pack := pack
    replacements := RichArgumentSupply.ofCore answer.toSortableGradedResult (captureNeeds required) bounded included
    outsideAvailable := outsideResources
    fitted := fitted
    substitutions := instantiated
    closed := Valuation.push_atomized_closed closed required.localNeeds
    resources := pack.available_atomized_localNeeds outsideResources }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
