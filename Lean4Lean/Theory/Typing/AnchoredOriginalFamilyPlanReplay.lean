import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanReplay

/-! Bare family plans and the original finite argument spine share one
frozen key sequence. Replay creates ordinary source application observers
without an unrestricted original-typing supplier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive OriginalFamilyReplayPath (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {m : Nat} → Atom m → {M : Nat} → Atom M → Type where
  | constant {atom : Atom m} :
      OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned atom atom
  | application {atom : Atom m} {root : Atom M}
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) (frame.familyReplayDemand atom) root) :
      OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) atom root
  | conversion {atom : Atom m} {root : Atom M}
      (edge : EndpointConversion sourceEnv U source A B)
      (term : OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        expression A atom root) :
      OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        expression B atom root

/-- This bound is computed by one finite pass over retained applications.
No pass rebuilds the original frozen key sequence. -/
def OriginalSeededSpine.familyReplayRank
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (outputRank : Nat) : Nat :=
  match spine with
  | .constant .. => outputRank
  | .application frame function => function.familyReplayRank (frame.familyReplayRank outputRank + 1)
  | .conversion _ _ _ term => term.familyReplayRank outputRank

structure OriginalFamilyReplayRoot
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (atom : Atom m) where
  demand : Atom (spine.familyReplayRank m)
  path : OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available name levels
    expression assigned atom demand

noncomputable def OriginalSeededSpine.familyReplay
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (atom : Atom m) : OriginalFamilyReplayRoot spine atom := by
  induction spine generalizing m with
  | constant replay => exact ⟨atom, .constant⟩
  | application frame function ih =>
    let previous := ih (frame.familyReplayDemand atom)
    exact ⟨previous.demand, .application frame previous.path⟩
  | conversion edge certificate transfer term ih =>
    let previous := ih atom
    exact ⟨previous.demand, .conversion edge previous.path⟩

/-- Once the finite bare-family plan is installed, this checked replay
constructs the saturated source observer through the existing application
grammar. Source footprints stay exactly the retained original leaves. -/
theorem OriginalFamilyReplayPath.observe
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression assigned : VExpr}
    {atom : Atom m} {root : Atom M}
    (path : OriginalFamilyReplayPath sourceEnv env U registry source target locals σ available
      name levels expression assigned atom root)
    {headFootprint : Footprint}
    (head : Obs env U registry target locals σ (.const name levels) (.singleton root) headFootprint)
    (headResources : headFootprint.Available available) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ expression (.singleton atom) footprint) ∧
      footprint.Available available := by
  induction path with
  | constant => exact ⟨headFootprint, ⟨head⟩, headResources⟩
  | @application m atom M root A B a n result before f frame function ih =>
    obtain ⟨footprint, ⟨fn⟩, resources⟩ := ih head
    have argument := frame.argumentObservation.raise (Nat.le_max_left frame.collected.rank m)
    have anchor := (frame.familyReplayGuard henv m).anchor
    have application := Obs.app fn argument (.refl _) anchor
    refine ⟨footprint ++ (frame.seed.footprint ++ frame.collected.argumentFootprint), ⟨?_⟩,
      fun i need member => (List.mem_append.mp member).elim
        (resources i need) (frame.argumentResources i need)⟩
    apply Obs.lower (Nat.le_max_right frame.collected.rank m)
    simpa only [raiseProfile_singleton, SeededApplicationCodeInput.familyReplayOutput,
      SeededApplicationCodeInput.familyReplayRank] using application
  | conversion _ _ ih => exact ih head
theorem OriginalSeededSpine.familyReplay_fold
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint) (atom : Atom m) :
    (⟨spine.familyReplayRank m, (spine.familyReplay atom).demand⟩ : Sigma Atom) =
      spine.familyKeys.foldr FamilyKey.replayStep ⟨m, atom⟩ := by
  induction spine generalizing m with
  | constant => rfl
  | application frame function ih =>
    change (⟨_, (function.familyReplay (frame.familyReplayDemand atom)).demand⟩ : Sigma Atom) = _
    rw [ih]
    simp only [OriginalSeededSpine.familyKeys, List.foldr_append,
      List.foldr_cons, List.foldr_nil]
    rfl
  | conversion edge certificate transfer term ih => exact ih atom

theorem OriginalSeededSpine.familyReplay_keys
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint) (atom : Atom m) :
    (⟨spine.familyReplayRank m, (spine.familyReplay atom).demand⟩ : Sigma Atom) =
      ⟨FamilyKey.replayRank spine.familyKeys m, FamilyKey.replayAtom spine.familyKeys atom⟩ := by
  rw [spine.familyReplay_fold atom, FamilyKey.replay_fold]

theorem OriginalSeededSpine.familyObservation
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
    ∃ footprint, Nonempty (Obs env U registry target locals seed expression
      (n := N + 1) (.singleton (.family ⟨name, levels, relevant,
        FamilyKey.uniform N spine.familyKeys bounded⟩)) footprint) ∧ footprint.Available available := by
  let atom : Atom (N + 1) := .family ⟨name, levels, relevant,
    FamilyKey.uniform N spine.familyKeys bounded⟩
  obtain ⟨plan⟩ := rows.barePlan henv hscoped below calls hTarget resultSort relevance N bounded
  obtain ⟨head⟩ := plan.bareObservation (locals := locals) (seed := seed) lookup
    notDefinition notNative notQuotient levelsWF length typeClosed
  have equal := spine.familyReplay_keys atom
  have replayHead := Obs.castAtomPair equal.symm head
  exact (spine.familyReplay atom).path.observe henv replayHead (fun _ _ member => nomatch member)


/-- The reconstructed observer is a type certificate at the same frozen
family descriptor; its well-formedness comes from the actual terminal
captures and their fixed input/support admissions. -/
theorem OriginalSeededSpine.familyCertificate
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
    (relevance : Relevant resultLevel true)
    (N : Nat) (bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N) :
    ∃ footprint, Nonempty (CodeCert env U registry target locals seed expression
      (n := N + 1) (.singleton (.family ⟨name, levels, true,
        FamilyKey.uniform N spine.familyKeys bounded⟩)) footprint) ∧ footprint.Available available := by
  obtain ⟨footprint, ⟨observation⟩, resources⟩ := spine.familyObservation henv hscoped below calls
    hTarget lookup typeClosed levelsWF length notDefinition notNative notQuotient
    rows resultSort relevance N bounded
  obtain ⟨captures⟩ := rows.captures henv N bounded
  exact ⟨footprint, ⟨.seed observation (captures.familyTyped true)⟩, resources⟩

/-- Start with a finite original argument ledger, follow only the computed
spine's smaller source calls, then replay the actual earlier declaration.
The retained declaration output exposes the exact final seed resources to
the later projection-field consumer. -/
theorem OriginalConstantSpine.seededFamilyCertificate
    {sourceEnv headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {rootSource source target : List VExpr} {rootExpression rootType expression assigned : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {name : Name} {levels : List VLevel}
    (spine : OriginalConstantSpine root name levels start)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (sourceCalls : spine.Fundamentals env registry initial)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {info : VConstant} (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (typeClosed : info.type.Closed)
    (header : OriginalFamilyHeader headerEnv U (info.type.instL levels))
    (headerCalls : header.Fundamentals env registry)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel)
    (relevance : Relevant resultLevel true)
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    {required : Footprint} (coverage : NativeSpineSeedCoverage seeds required)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ produced : OriginalSeededSpine sourceEnv env U registry source target locals σ available
        name levels expression assigned profile footprint,
      produced.seeds = seeds ∧
      ∃ declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
          expression.getAppFnArgs.2 assigned profile required produced.familyKeys,
        NativeObservedValuation env U registry target locals σ available
          expression.getAppFnArgs.2 declared.valuation ∧
        ∃ (bounded : ∀ key ∈ produced.familyKeys, key.rank ≤ FamilyKey.bound produced.familyKeys),
          ∃ outputFootprint,
          Nonempty (CodeCert env U registry target locals σ expression
            (n := FamilyKey.bound produced.familyKeys + 1)
            (.singleton (.family ⟨name, levels, true,
              FamilyKey.uniform (FamilyKey.bound produced.familyKeys) produced.familyKeys bounded⟩)) outputFootprint) ∧
          outputFootprint.Available available := by
  obtain ⟨produced, same⟩ := spine.prepare henv hscoped sourceBelow initial sourceCalls closed hTarget
    substitutions fits seeds certificate resources
  have covered : NativeSpineSeedCoverage produced.seeds required := by rw [same]; exact coverage
  obtain ⟨declared, observed⟩ := produced.familyDeclared henv hscoped headerBelow closed hTarget lookup
    signature typeClosed.instL header headerCalls covered (Nat.le_of_eq saturated)
  obtain ⟨rows, _, _⟩ := declared.anyRows saturated
  let bounded : ∀ key ∈ produced.familyKeys, key.rank ≤ FamilyKey.bound produced.familyKeys :=
    fun _ member => Nat.le_of_lt (FamilyKey.lt_bound member)
  exact ⟨produced, same, declared, observed, bounded,
    produced.familyCertificate henv hscoped headerBelow headerCalls hTarget
      (sourceBelow.constants lookup) typeClosed levelsWF length notDefinition notNative notQuotient
      rows resultSort relevance _ bounded⟩

/-- The actual source family observer also retains proposition-family tags.
Only the final intrinsic certificate interface distinguishes the flag. -/
theorem OriginalConstantSpine.seededFamilyObservation
    {sourceEnv headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {rootSource source target : List VExpr} {rootExpression rootType expression assigned : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {name : Name} {levels : List VLevel}
    (spine : OriginalConstantSpine root name levels start)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (sourceCalls : spine.Fundamentals env registry initial)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {info : VConstant} (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (typeClosed : info.type.Closed)
    (header : OriginalFamilyHeader headerEnv U (info.type.instL levels))
    (headerCalls : header.Fundamentals env registry)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel)
    (relevance : Relevant resultLevel relevant)
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    {required : Footprint} (coverage : NativeSpineSeedCoverage seeds required)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ produced : OriginalSeededSpine sourceEnv env U registry source target locals σ available
        name levels expression assigned profile footprint,
      produced.seeds = seeds ∧
      ∃ declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
          expression.getAppFnArgs.2 assigned profile required produced.familyKeys,
        NativeObservedValuation env U registry target locals σ available
          expression.getAppFnArgs.2 declared.valuation ∧
        ∃ (bounded : ∀ key ∈ produced.familyKeys, key.rank ≤ FamilyKey.bound produced.familyKeys),
          ∃ outputFootprint,
          Nonempty (Obs env U registry target locals σ expression
            (n := FamilyKey.bound produced.familyKeys + 1)
            (.singleton (.family ⟨name, levels, relevant,
              FamilyKey.uniform (FamilyKey.bound produced.familyKeys) produced.familyKeys bounded⟩)) outputFootprint) ∧
          outputFootprint.Available available := by
  obtain ⟨produced, same⟩ := spine.prepare henv hscoped sourceBelow initial sourceCalls closed hTarget
    substitutions fits seeds certificate resources
  have covered : NativeSpineSeedCoverage produced.seeds required := by rw [same]; exact coverage
  obtain ⟨declared, observed⟩ := produced.familyDeclared henv hscoped headerBelow closed hTarget lookup
    signature typeClosed.instL header headerCalls covered (Nat.le_of_eq saturated)
  obtain ⟨rows, _, _⟩ := declared.anyRows saturated
  let bounded : ∀ key ∈ produced.familyKeys, key.rank ≤ FamilyKey.bound produced.familyKeys :=
    fun _ member => Nat.le_of_lt (FamilyKey.lt_bound member)
  exact ⟨produced, same, declared, observed, bounded,
    produced.familyObservation henv hscoped headerBelow headerCalls hTarget
      (sourceBelow.constants lookup) typeClosed levelsWF length notDefinition notNative notQuotient
      rows resultSort relevance _ bounded⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
