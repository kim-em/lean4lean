import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipePiRowExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

inductive WorldPiLeaf (env : VEnv) {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) : {n : Nat} → Atom n → Type where
  | native (origin : WorldPiAtomOrigins env controls frontier U registry target locals σ available domainNode bodyNode atom) :
      WorldPiLeaf env controls frontier U registry target locals σ available domainNode bodyNode atom
  | recipe
      (code : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.singleton atom) footprint)
      (annotation : WorldCodeRecipeProvenance strata code)
      (resources : footprint.Available available)
      (sponsored : Sponsored frontier annotation.worlds)
      (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
        (fun control => code.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))) :
      WorldPiLeaf env controls frontier U registry target locals σ available domainNode bodyNode atom

structure WorldPiDeferredOrigin (env : VEnv) {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (atom : Atom n) where
  rank : Nat
  original : Atom rank
  leaf : WorldPiLeaf env controls frontier U registry target locals σ available domainNode bodyNode original
  path : GeneralOutputPath env U registry target original atom

def WorldPiDeferredOrigins (env : VEnv) {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource) (frontier : List (World strata.rules.length))
    (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    {sourceEnv : VEnv} {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domainNode : EndpointState sourceEnv U source A (.sort u))
    (bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)) (profile : Profile n) : Prop :=
  ∀ atom ∈ profile.atoms,
    Nonempty (WorldPiDeferredOrigin env controls frontier U registry target locals σ available domainNode bodyNode atom)

theorem WorldPiDeferredOrigins.code
    (change : SortableCodeAction env U registry target relevant p next q)
    (typed : p.HasType (.sort relevant))
    (origins : WorldPiDeferredOrigins env controls frontier U registry target locals σ available domainNode bodyNode p) :
    WorldPiDeferredOrigins env controls frontier U registry target locals σ available domainNode bodyNode q := by
  intro atom member
  obtain ⟨old, present, ⟨step⟩⟩ := change.atom member
  obtain ⟨origin⟩ := origins old present
  exact ⟨{ origin with path := .code origin.path step (typed.singleton_of_mem present) }⟩


 theorem WorldPiDeferredOrigin.resolve
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource} {frontier : List (World strata.rules.length)}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (reanchorRow : ∀ {relevant : Bool} {n : Nat} {key : Key n} {result : Profile n} {anchor : VExpr},
      (row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result) →
      row.Controlled controls frontier → Admitted env U registry target key anchor anchor →
      ∃ next : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode
        (reanchorKey key anchor) result, Nonempty (next.Controlled controls frontier))
    (origin : WorldPiDeferredOrigin env controls frontier U registry target locals σ available domainNode bodyNode (n := n + 1)
      (.pi prototypeDomain prototypeBody (support : Profile n) rows))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      (.forallE C D) (Profile.pi prototypeDomain prototypeBody support rows))
    (sorted : (Profile.pi prototypeDomain prototypeBody support rows).HasType (.sort relevant))
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant domainNode bodyNode key result,
      Nonempty (row.Controlled controls frontier) := by
  obtain ⟨flag, inputSorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv origin.path sorted
  cases origin.leaf with
  | native native =>
    have origins : WorldPiProfileOrigins env controls frontier U registry target locals σ available domainNode bodyNode
        (.singleton origin.original) := by
      intro atom member
      cases List.mem_singleton.mp member
      exact native
    have next := WorldPiProfileOrigins.codeActionWith henv hscoped formed closed reanchorRow action origins
    obtain ⟨oldFlag, row, ⟨ready⟩⟩ := next _ (List.mem_singleton_self _) key result selected
    have typed := (Profile.HasType.pi_iff.mp sorted).2 key result selected
    exact ⟨row.atFlag typed, ⟨ready.atFlag typed⟩⟩
  | recipe code annotation resources sponsored within =>
    let next := RichCodeRecipe.action action (RichCodeRecipe.action (.retag inputSorted) code)
    let nextAnnotation := WorldCodeRecipeProvenance.action action
      (WorldCodeRecipeProvenance.action (.retag inputSorted) annotation)
    exact next.requestedRowControlled nextAnnotation sponsored
      (by simpa only [next, RichCodeRecipe.headDepth] using within)
      henv hscoped formed whole selected admitted resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
