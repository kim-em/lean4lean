import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyPlanReplay

/-! The actual original family producer also supplies formation queries for
proposition families. Its source observer is constructed by the complete
header and original-argument replay, with the flag retained literally. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem OriginalSeededSpine.sortableFamilyCertificate
    {sourceEnv headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.Fundamentals env registry)
    {source target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : env.constants name = some info)
    {signature : ConstantTelescope (info.type.instL levels)}
    (typeClosed : info.type.Closed)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {expression assigned : VExpr} {profile : Profile n} {footprint required : Footprint}
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint)
    (rows : OriginalFamilyCodeRows header env registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) (info.type.instL levels) signature.domains spine.familyKeys)
    (resultSort : signature.result = .sort resultLevel)
    (relevance : Relevant resultLevel relevant)
    (N : Nat) (bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N) :
    ∃ footprint, Nonempty (SortableCert env U registry target locals seed expression relevant
      (n := N + 1) (.singleton (.family ⟨name, levels, relevant,
        FamilyKey.uniform N spine.familyKeys bounded⟩)) footprint) ∧ footprint.Available available := by
  obtain ⟨footprint, ⟨observation⟩, resources⟩ := spine.familyObservation henv hscoped below calls
    hTarget lookup typeClosed levelsWF length notDefinition notNative notQuotient
    rows resultSort relevance N bounded
  obtain ⟨captures⟩ := rows.captures henv N bounded
  exact ⟨footprint, ⟨.seed observation (captures.familyTyped relevant)⟩, resources⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
