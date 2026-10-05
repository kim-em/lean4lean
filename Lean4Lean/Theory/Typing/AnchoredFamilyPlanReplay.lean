import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows
import Lean4Lean.Theory.Typing.AnchoredFamilyReplay

/-! The finite bare-family plan and the original application replay use one
frozen key sequence. Their grade computations agree as dependent atom
packets, so the bare constant is installed in the actual Obs grammar and
every original application is replayed through Obs.app. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeSeededSpineCertificate.familyReplay_fold
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint) (atom : Atom m) :
    (⟨spine.familyReplayRank m, (spine.familyReplay atom).demand⟩ : Sigma Atom) =
      spine.familyKeys.foldr FamilyKey.replayStep ⟨m, atom⟩ := by
  induction spine generalizing m with
  | constant => rfl
  | application frame function ih =>
    change (⟨_, (function.familyReplay (frame.familyReplayDemand atom)).demand⟩ : Sigma Atom) = _
    rw [ih]
    simp only [NativeSeededSpineCertificate.familyKeys, List.foldr_append,
      List.foldr_cons, List.foldr_nil]
    rfl
  | conversion edge certificate transfer term ih => exact ih atom

theorem NativeSeededSpineCertificate.familyReplay_keys
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint) (atom : Atom m) :
    (⟨spine.familyReplayRank m, (spine.familyReplay atom).demand⟩ : Sigma Atom) =
      ⟨FamilyKey.replayRank spine.familyKeys m, FamilyKey.replayAtom spine.familyKeys atom⟩ := by
  rw [spine.familyReplay_fold atom, FamilyKey.replay_fold]

noncomputable def Obs.castAtomPair
    {a : Atom n} {b : Atom m}
    (equal : (⟨n, a⟩ : Sigma Atom) = ⟨m, b⟩)
    (observation : Obs env U registry target locals seed expression (.singleton a) footprint) :
    Obs env U registry target locals seed expression (.singleton b) footprint := by
  cases equal
  exact observation

/-- Install the bare declaration plan and replay the original application
spine. Both the source type code and the observer are concrete finite syntax;
their only source leaves are retained original argument observations. -/
theorem NativeSeededSpineCertificate.familyObservation
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
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
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals seed available
      name levels expression assigned profile footprint)
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) (info.type.instL levels) signature.domains spine.familyKeys)
    (resultSort : signature.result = .sort resultLevel)
    (relevance : Relevant resultLevel relevant)
    (N : Nat) (bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N) :
    ∃ footprint, Nonempty (Obs env U registry target locals seed expression
      (n := N + 1) (.singleton (.family ⟨name, levels, relevant,
        FamilyKey.uniform N spine.familyKeys bounded⟩)) footprint) ∧ footprint.Available available := by
  let atom : Atom (N + 1) := .family ⟨name, levels, relevant,
    FamilyKey.uniform N spine.familyKeys bounded⟩
  obtain ⟨plan⟩ := rows.barePlan henv hscoped hle hTarget resultSort relevance N bounded
  obtain ⟨head⟩ := plan.bareObservation (locals := locals) (seed := seed) lookup
    notDefinition notNative notQuotient levelsWF length typeClosed
  have equal := spine.familyReplay_keys atom
  have replayHead := Obs.castAtomPair equal.symm head
  exact (spine.familyReplay atom).path.observe henv replayHead (fun _ _ member => nomatch member)

/-- End-to-end source production starts at the original Strong application
tree and its finite argument ledger. Declared rows recover source domains,
the terminal observes their actual variables, and ordinary application
nodes reconnect that closed plan to the original source expression. -/
theorem HasTypeStrong.seededFamilyObservation
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : PairedFits env U registry source target locals seed seed available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels)
      (info.type.instL levels) (.sort headerLevel))
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    {expression : VExpr} {structural : Bool} {level : VLevel}
    (original : sourceEnv.HasTypeStrong U source expression (.sort level) structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel)
    (relevance : Relevant resultLevel relevant)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {profile : Profile n} {footprint required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals seed available expression.getAppFnArgs.2 required)
    (certificate : CodeCert env U registry target locals seed (.sort level) profile footprint)
    (resources : footprint.Available available) :
    ∃ (keys : List FamilyKey) (bounded : ∀ key ∈ keys, key.rank ≤ FamilyKey.bound keys),
      ∃ footprint, Nonempty (Obs env U registry target locals seed expression
        (n := FamilyKey.bound keys + 1) (.singleton (.family ⟨name, levels, relevant,
          FamilyKey.uniform (FamilyKey.bound keys) keys bounded⟩)) footprint) ∧
        footprint.Available available := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head n
  obtain ⟨spine, same, children⟩ := HasTypeStrong.seededFamilySpine henv hscoped hle earlier
    closed hTarget substitutions fits original head seeds certificate resources
  have payload := earlier formation
  have coverage' : NativeSpineSeedCoverage spine.seeds required := by rw [same]; exact coverage
  obtain ⟨declared⟩ := spine.familyDeclared henv hscoped hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation
    coverage' (Nat.le_of_eq saturated)
  obtain ⟨rows, _, _⟩ := declared.rows saturated resultSort
  let bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ FamilyKey.bound spine.familyKeys :=
    fun _ member => Nat.le_of_lt (FamilyKey.lt_bound member)
  obtain ⟨u, rawType⟩ := hsource.constWF lookup
  have typeClosed : info.type.Closed := VExpr.WF.closedN hsource ⟨_, rawType⟩ trivial
  exact ⟨spine.familyKeys, bounded, spine.familyObservation henv hscoped hle hTarget
    (hle.constants lookup) typeClosed levelsWF length notDefinition notNative notQuotient
    rows resultSort relevance _ bounded⟩

end Lean4Lean.AnchoredSource.Adapted
