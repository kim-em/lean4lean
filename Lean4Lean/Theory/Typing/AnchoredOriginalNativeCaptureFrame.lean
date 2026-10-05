import Lean4Lean.Theory.Typing.AnchoredOriginalRichOccurrenceTraversal
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichLookupDepth
import Lean4Lean.Theory.Typing.AnchoredNativeWitnessedReplay

/-! Concrete native index/proof capture steps at the actual equation lambda
body. The index relation is obtained by lookup in the retained argument frame,
then transported by the stored native domain chain. Neither step invokes a
fundamental theorem or assumes a completed equation-body frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def OriginalRichOccurrenceFrame.nativeIndex
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: source) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceBelow : sourceEnv ≤ env)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target
      locals captures rightCaptures available ordered initialEnvironment)
    {argumentContext : ContextDerivation argumentEnv U argumentSource}
    (argumentFrame : OriginalRichFrame argumentEnv env U registry target argumentContext
      argumentLocals arguments rightArguments argumentAvailable)
    (argumentSubstitutions : Ctx.SubstEq env U target arguments rightArguments argumentSource)
    (lookup : Lookup argumentSource position natural)
    (needed : (⟨n, input⟩ : Need) ∈ argumentAvailable position)
    (domainCode : CodeCert env U registry target locals captures A support footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (alignment : DomainChain env U registry target input
      (natural.subst arguments) (A.subst captures))
    (declaredCode : TypeRelated env U registry target
      (A.subst captures) (A.subst captures) support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    OriginalRichOccurrenceFrame (.lamBody location) initialContext env registry target
      (Locals.push locals) (captures.cons (arguments position))
      (rightCaptures.cons (rightArguments position)) (available.push needs)
      ordered initialEnvironment := by
  let entry := Classical.choose (argumentFrame.lookup_allDepth henv formed needed lookup)
  exact occurrence.lamBody sourceBelow
    (.legacy (.ofCode domainCode domainCode.formed)) resources typed
    (alignment.related henv typed declaredCode entry.related)
    (alignment.path.cast (argumentSubstitutions.lookup lookup)) needs bounded covered

/-- Proof slots require no semantic code opening: their stored pack excludes
all demand atoms. The actual domain reference still comes from the equation
lambda, and its dependency is charged by `lamBody`. -/
noncomputable def OriginalRichOccurrenceFrame.nativeProof
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: source) expression B}
    {hu : u.WF U} {hv : v.WF U}
    {location : Located root (.lam hu hv domain codomain body)}
    (sourceBelow : sourceEnv ≤ env)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target
      locals captures rightCaptures available ordered initialEnvironment)
    (inhabitant : env.HasType U target witness (A.subst captures))
    (needs : List Need) (n : Nat) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (empty : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, False) :
    OriginalRichOccurrenceFrame (.lamBody location) initialContext env registry target
      (Locals.push locals) (captures.cons witness) (rightCaptures.cons witness)
      (available.push needs) ordered initialEnvironment := by
  have certificate : CodeCert env U registry target locals captures A
      (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
  have related : Related env U registry target witness witness (A.subst captures)
      (Profile.empty (n := n)) .empty := by
    apply Related.of_singletons
    intro atom member
    cases member
  exact occurrence.lamBody sourceBelow
    (.legacy (.ofCode certificate certificate.formed)) (fun _ _ h => nomatch h)
    (.empty .empty) related inhabitant needs bounded
    (fun need member atom atomMember => (empty need member atom atomMember).elim)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
