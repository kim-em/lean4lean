import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredSortableApplicationCode
import Lean4Lean.Theory.Typing.AnchoredAtomActionCode
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionCertificate

/-! Finite header replay for physical application origins. Each seed retains
its actual function/argument requests and output action. Charged-code leaves
are retained separately by application-origin extraction and require their
actual interpreter; they are not fabricated into physical requests.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false


def RichAppOrigin.functionNeed
    (origin : RichAppOrigin root env registry target source locals σ f a) : Need :=
  ⟨origin.rank + 1, Profile.fn origin.key origin.output⟩

def RichAppOrigin.argumentNeed
    (origin : RichAppOrigin root env registry target source locals σ f a) : Need :=
  ⟨origin.rank, origin.rawInput⟩

/-- A finite row retains two whole ORIGINAL rich child queries, together
with the actual path from their frozen output to the requested atom. -/
inductive RichApplicationSeeds
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (f a : VExpr)
    (originalFootprint : Footprint) : List (Atom n) → Type where
  | nil : RichApplicationSeeds root env registry target source locals σ f a originalFootprint []
  | cons (origin : RichAppOrigin root env registry target source locals σ f a)
      (path : GeneralOutputPath env U registry target origin.output atom)
      (included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) originalFootprint)
      (rest : RichApplicationSeeds root env registry target source locals σ f a originalFootprint atoms) :
      RichApplicationSeeds root env registry target source locals σ f a originalFootprint (atom :: atoms)

/- A general rich application query may now contain a charged recipe
from an independent original source. `RichCert.applicationOrigin` returns
that explicit alternative. It cannot be converted into physical function/
argument seeds without interpreting the recipe; the old unconditional
`RichCert.applicationSeeds` convenience had no consumers and is retired. -/

def RichApplicationSeeds.required
    (seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms)
    (functionIndex argumentIndex : Nat) : Footprint :=
  match seeds with
  | .nil => []
  | .cons origin _ _ rest =>
      [(functionIndex, origin.functionNeed), (argumentIndex, origin.argumentNeed)] ++
        rest.required functionIndex argumentIndex

/-- Every extracted child still uses available ORIGINAL resources. -/
theorem RichAppOrigin.originalResources
    {footprint : Footprint}
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint)
    (resources : footprint.Available available) :
    origin.functionFootprint.Available available ∧ origin.argumentFootprint.Available available :=
  ⟨fun index need member => resources index need (included (List.mem_append_left _ member)),
    fun index need member => resources index need (included (List.mem_append_right _ member))⟩

/-- Replay one actual origin. The function lookup may have any assigned type;
the sortable result is extracted from its actual semantic application row. -/
theorem RichAppOrigin.headerReplay
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef currentEnv U current fieldExpression fieldType}
    {major : EndpointRef currentEnv U current majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source ownerLocals σ f a)
    (path : GeneralOutputPath env U registry target origin.output atom)
    (sorted : (Profile.singleton atom).HasType (.sort relevant))
    (tail : HeaderBinderFrame header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource (.app (.bvar functionIndex) (.bvar argumentIndex)) (.sort level))
    (functionNeed : origin.functionNeed ∈ available functionIndex)
    (functionLookup : Lookup headerSource functionIndex functionType)
    (argumentNeed : origin.argumentNeed ∈ available argumentIndex)
    (functionEq : f.subst σ = left functionIndex)
    (argumentEq : a.subst σ = left argumentIndex) :
    ∃ required, Nonempty (RichCert headerEnv env U registry target (.ref domain) locals left
      relevant (.singleton atom) required) ∧ required.Available available ∧
      TypeRelated env U registry target ((VExpr.app f a).subst σ)
        ((VExpr.app (.bvar functionIndex) (.bvar argumentIndex)).subst left) (.singleton atom) := by
  obtain ⟨flag, inputSorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv path sorted
  obtain ⟨entry⟩ := tail.lookup henv formed functionNeed functionLookup
  have admitted : Admitted env U registry target origin.key (left argumentIndex) (left argumentIndex) :=
    argumentEq ▸ origin.admitted
  have code := Related.applicationCode henv hscoped formed inputSorted entry.related.left_diagonal admitted
  let input : SortableCert env U registry target locals left
      (.app (.bvar functionIndex) (.bvar argumentIndex)) flag (.singleton origin.output)
      [(functionIndex, origin.functionNeed), (argumentIndex, origin.argumentNeed)] :=
    .observe (.app (.legacy (.var locals left functionIndex _))
      (.legacy (.var locals left argumentIndex _)) origin.arguments admitted) inputSorted
  have inputResources : Footprint.Available
      [(functionIndex, origin.functionNeed), (argumentIndex, origin.argumentNeed)] available := by
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact functionNeed
    · cases List.mem_singleton.mp member; exact argumentNeed
  exact ⟨_, ⟨.legacy (action.applyCertificate input)⟩, action.available inputResources, by
    simpa only [subst, functionEq, argumentEq] using action.codeMap henv hscoped code⟩

private theorem typeSubset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom member => typed atom (subset atom member)
  | succ n => exact ⟨fun atom member => typed.1 atom (subset atom member), typed.2.1,
      fun atom member => typed.2.2 atom (subset atom member)⟩

/-- The whole original profile is rebuilt from its finite extracted seeds.
All source output certificates are produced here; only the computed capture
footprint must already be available in the actual header tail. -/
theorem RichApplicationSeeds.headerReplay
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef currentEnv U current fieldExpression fieldType}
    {major : EndpointRef currentEnv U current majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (seeds : RichApplicationSeeds root env registry target source ownerLocals σ f a footprint atoms)
    (sorted : (Profile.mk atoms).HasType (.sort relevant))
    (tail : HeaderBinderFrame header field major env registry target context locals left right available)
    (domain : EndpointRef headerEnv U headerSource (.app (.bvar functionIndex) (.bvar argumentIndex)) (.sort level))
    (resources : (seeds.required functionIndex argumentIndex).Available available)
    (functionLookup : Lookup headerSource functionIndex functionType)
    (functionEq : f.subst σ = left functionIndex)
    (argumentEq : a.subst σ = left argumentIndex) :
    ∃ required, Nonempty (RichCert headerEnv env U registry target (.ref domain) locals left
      relevant (.mk atoms) required) ∧ required.Available available ∧
      TypeRelated env U registry target ((VExpr.app f a).subst σ)
        ((VExpr.app (.bvar functionIndex) (.bvar argumentIndex)).subst left) (.mk atoms) := by
  induction seeds with
  | nil =>
    exact ⟨[], ⟨.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)))⟩,
      (by intro _ _ member; cases member), by
        apply TypeRelated.of_singletons
        intro atom member; cases member⟩
  | cons origin path included rest ih =>
    obtain ⟨headFootprint, ⟨headCode⟩, headResources, headRelated⟩ := origin.headerReplay henv hscoped formed
      path (sorted.singleton_of_mem (List.mem_cons_self)) tail domain
      (resources _ _ (by simp [required])) functionLookup
      (resources _ _ (by simp [required])) functionEq argumentEq
    obtain ⟨tailFootprint, ⟨tailCode⟩, tailResources, tailRelated⟩ := ih
      (typeSubset (fun _ h => List.mem_cons_of_mem _ h) sorted)
      (fun index need member => resources index need (List.mem_append_right _ member))
    refine ⟨headFootprint ++ tailFootprint, ⟨.union headCode tailCode⟩, ?_, ?_⟩
    · intro index need member
      exact (List.mem_append.mp member).elim (headResources index need) (tailResources index need)
    · apply TypeRelated.of_singletons
      intro atom member
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact headRelated
      · exact tailRelated.singleton member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
