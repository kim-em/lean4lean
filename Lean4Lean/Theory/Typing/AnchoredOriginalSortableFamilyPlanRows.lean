import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyDeclaredPrefix
import Lean4Lean.Theory.Typing.AnchoredSortableFamilyPlanResult

/-! Close the finite rich family row ledger into an actual source family
plan using only the original declared-domain children at their exact tails. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem SortablePiRowCertificate.familyPlanBinderOriginal
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    {arguments : List VExpr} {available : Valuation} {A B : VExpr}
    {key : Key n} {result : Profile n} {output : Atom m}
    (row : SortablePiRowCertificate env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available true A B key result)
    (context : ContextDerivation headerEnv U source)
    (original : EndpointRef headerEnv U source A (.sort level))
    (domainIH : StateSortableFundamental env registry context (.ref original))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) source)
    (fits : SortableTailFits headerEnv env U registry target source (List.range arguments.length)
      (nativeCaptureSubst arguments) (nativeCaptureSubst arguments) available)
    (origin : signature.domains[arguments.length]? = some A)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (child : SortableFamilyPlanResult env U registry target name levels signature (arguments ++ [key.anchor])
      (Valuation.push (row.seedNeeds extra) available) B output) :
    Nonempty (SortableFamilyPlanResult env U registry target name levels signature arguments available
      (.forallE A B) (n := max n m + 1) (.fn (raiseKey (max n m) (Nat.le_max_left _ _) key)
        (raiseAtom (max n m) (Nat.le_max_right _ _) output))) := by
  obtain ⟨domain⟩ := domainIH target (List.range arguments.length) _ _ available closed hTarget substitutions
    (SortableTailPairedFits.diagonal context fits) row.domain row.domainAvailable
  have guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) A
      (domainKey key (A.subst (nativeCaptureSubst arguments))) row.domainSupport :=
    ⟨row.inputTyped, row.domain.formed, .refl, domain.related, row.alignment.admission henv row.anchor⟩
  let raised := child.raise (Nat.le_max_right n m)
  have domainCode := row.domain.raise (Nat.le_max_left n m)
  have raisedGuard := guard.raise henv (Nat.le_max_left n m)
  have coverage := row.seedCoverageRaised extra bounded covered (Nat.le_max_left n m)
  obtain ⟨packed, outside, pack, included, outsideAvailable⟩ :=
    Footprint.pack_available raised.resources
      (fun need member => (coverage need member).1) (fun need member => (coverage need member).2)
  obtain ⟨typePacked, typeOutside, typePack, typeIncluded, typeOutsideAvailable⟩ :=
    Footprint.pack_available raised.typeResources
      (fun need member => (coverage need member).1) (fun need member => (coverage need member).2)
  let actualKey := raiseKey (max n m) (Nat.le_max_left n m)
    (domainKey key (A.subst (nativeCaptureSubst arguments)))
  have code : SortableCert env U registry target (Locals.push (List.range arguments.length))
      ((nativeCaptureSubst arguments).cons key.anchor) B true raised.support raised.typeFootprint := by
    simpa only [List.length_append, List.length_singleton, List.range_succ_eq_map,
      Locals.push, nativeCaptureSubst_append] using raised.certificate
  let assembled : SortableFamilyPlanResult env U registry target name levels signature arguments available
      (.forallE A B) (n := max n m + 1) (.fn actualKey (raiseAtom (max n m) (Nat.le_max_right n m) output)) := {
    footprint := row.domainFootprint ++ outside
    plan := .binder origin domainCode raisedGuard raised.plan pack included
    resources := fun i need member => (List.mem_append.mp member).elim
      (row.domainAvailable i need) (outsideAvailable i need)
    support := .pi (A.subst (nativeCaptureSubst arguments))
      (B.subst (nativeCaptureSubst arguments).lift)
      (raiseProfile (max n m) (Nat.le_max_left n m) row.domainSupport)
      [(actualKey, raised.support)]
    typeFootprint := row.domainFootprint ++ typeOutside
    certificate := by
      apply SortableCert.piLiteral domainCode
      simpa only [List.append_nil] using
        SortableRows.cons raisedGuard code typePack typeIncluded SortableRows.nil
    typeResources := fun i need member => (List.mem_append.mp member).elim
      (row.domainAvailable i need) (typeOutsideAvailable i need)
    typed := by
      apply Profile.HasType.fn _ (List.mem_singleton_self _) raised.typed
      refine Profile.WF.pi_iff.mpr ⟨domainCode.formed, ?_⟩
      intro k r member
      cases List.mem_singleton.mp member
      exact ⟨raisedGuard.inputTyped, raised.typed.wf_type⟩ }
  have chain := row.alignment.raise henv (Nat.le_max_left n m)
  have forward := chain.view key.anchor (raiseAtom (max n m) (Nat.le_max_right n m) output)
  exact ⟨assembled.view (forward.inverse henv)⟩

theorem OriginalSortableFamilyCodeRows.closePlan
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.SortableFundamentals env registry)
    {source target : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : OriginalSortableFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (localNames : locals = List.range arguments.length)
    (realization : seed = nativeCaptureSubst arguments)
    (remaining : domains = signature.domains.drop arguments.length)
    (residual : expression = wrapForalls domains signature.result)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : SortableTailFits headerEnv env U registry target source locals seed seed available)
    {atom : Atom m}
    (terminal : SortableFamilyPlanResult env U registry target name levels signature
      (arguments ++ keys.map (·.key.anchor)) rows.terminalValuation signature.result atom) :
    Nonempty (SortableFamilyPlanResult env U registry target name levels signature arguments available
      expression (FamilyKey.replayAtom keys atom)) := by
  induction rows generalizing arguments with
  | nil resources =>
    simp only [wrapForalls] at residual
    have finish := Nonempty.intro terminal
    simpa only [List.map_nil, List.append_nil, OriginalSortableFamilyCodeRows.terminalValuation,
      FamilyKey.replayAtom, residual, List.foldr_nil] using finish
  | @cons source A level locals seed available B n key result domains keys
      original location row support admission extra bounded covered inputPresent tail ih =>
    subst locals seed
    have origin : signature.domains[arguments.length]? = some A := by
      have head : (signature.domains.drop arguments.length)[0]? = some A := by
        rw [← remaining]
        rfl
      simpa only [List.getElem?_drop, Nat.add_zero] using head
    have nextRemaining : domains = signature.domains.drop (arguments ++ [key.anchor]).length := by
      simp only [List.length_append, List.length_singleton, List.drop_add_one_eq_tail_drop,
        ← remaining, List.tail_cons]
    have nextResidual : B = wrapForalls domains signature.result :=
      (VExpr.forallE.inj residual).2
    obtain ⟨raw, ⟨localFits⟩⟩ := row.pushSeedOriginal henv hscoped below
      (location.contextDerivation .nil) original (calls location) closed hTarget
      substitutions fits extra bounded covered
    have nextLocals : Locals.push (List.range arguments.length) =
        List.range (arguments ++ [key.anchor]).length := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have nextSeed : (nativeCaptureSubst arguments).cons key.anchor =
        nativeCaptureSubst (arguments ++ [key.anchor]) := (nativeCaptureSubst_append arguments key.anchor).symm
    have terminal' : SortableFamilyPlanResult env U registry target name levels signature
        ((arguments ++ [key.anchor]) ++ keys.map (·.key.anchor)) tail.terminalValuation
        signature.result atom := by
      simpa only [List.map_cons, List.append_assoc, List.singleton_append,
        OriginalSortableFamilyCodeRows.terminalValuation] using terminal
    obtain ⟨child⟩ := ih nextLocals nextSeed nextRemaining nextResidual
      (row.seedClosed extra closed) raw localFits.forward terminal'
    exact row.familyPlanBinderOriginal henv hscoped below (location.contextDerivation .nil)
      original (calls location) closed hTarget substitutions fits
      origin extra bounded covered child

/-- The initial empty source context closes every actual plan and code
leaf. The resulting bare-family demand replays the same frozen row keys. -/
theorem OriginalSortableFamilyCodeRows.barePlan
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.SortableFundamentals env registry)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {keys : List FamilyKey} {required : Footprint}
    (rows : OriginalSortableFamilyCodeRows header env registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys)
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    Nonempty (SortableFamilyPlanResult env U registry target name levels signature [] (fun _ => []) declaredType
      (FamilyKey.replayAtom (n := N + 1) keys (.family ⟨name, levels, relevant, FamilyKey.uniform N keys bounded⟩))) := by
  obtain ⟨captures⟩ := rows.captures henv N bounded
  have localNames := rows.terminalLocals_eq 0 rfl
  have captures' : FamilyCaptures env U registry target signature.domains.reverse
      (List.range (keys.map (·.key.anchor)).length)
      (nativeCaptureSubst (keys.map (·.key.anchor)))
      (constantCaptureVariables (keys.map (·.key.anchor)).length)
      (FamilyKey.uniform N keys bounded) (FamilyKey.captureFootprint keys) := by
    simpa only [List.append_nil, familySubst_native, List.nil_append, List.length_map,
      localNames, Nat.zero_add] using captures
  let terminal := SortableFamilyPlanResult.terminal (name := name) (levels := levels)
    (by simpa only [List.length_map] using rows.length) resultSort relevance captures' rows.captureAvailable
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  exact rows.closePlan henv hscoped below calls rfl rfl (by simp) signature.type_eq
    emptyClosed hTarget .nil .nil terminal


end Lean4Lean.AnchoredSource.Adapted
