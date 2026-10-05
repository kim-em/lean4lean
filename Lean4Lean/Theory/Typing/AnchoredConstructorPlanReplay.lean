import Lean4Lean.Theory.Typing.AnchoredConstructorPlanRows
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanReplay
import Lean4Lean.Theory.Typing.AnchoredSourceFamilyPadding

/-! Constructor production starts with the original application's requested
family type certificate. The actual declared prefix retains that same code
at the literal constructor result; only its finite request ranks are raised.
The resulting bare plan is reconnected by ordinary source applications. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem NativeSeededSpineCertificate.constructorObservation
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
    {family : FamilyData (Profile p)} {expression assigned : VExpr} {footprint required : Footprint}
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals seed available
      name levels expression assigned (Profile.singleton (n := p + 1) (.family family)) footprint)
    (declared : FamilySeededDeclaredPrefix sourceEnv env U registry target locals seed available
      signature expression.getAppFnArgs.2 assigned
      (Profile.singleton (n := p + 1) (.family family)) required spine.familyKeys)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
    (relevant : family.relevant = true)
    (N : Nat) (familyBound : p ≤ N) (bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N) :
    ∃ footprint, Nonempty (Obs env U registry target locals seed expression
      (n := N + 1) (.singleton (.ctor ⟨name, levels, FamilyKey.uniform N spine.familyKeys bounded,
        family.raise N familyBound, relevant⟩)) footprint) ∧ footprint.Available available := by
  obtain ⟨rows, _, ledgerEq⟩ := declared.anyRows saturated
  have resultCode : CodeCert env U registry target (List.range spine.familyKeys.length)
      (nativeCaptureSubst (spine.familyKeys.map (·.key.anchor))) signature.result
      (Profile.singleton (n := p + 1) (.family family)) declared.footprint := by
    have originalCode := declared.certificate
    simp only [saturated, List.drop_length, wrapForalls] at originalCode
    have seedEq := declared.seed_eq
    simp only [familySubst_native, List.nil_append] at seedEq
    rw [← seedEq] at originalCode
    simpa only [rows.length, saturated, List.foldr_nil] using originalCode
  have resultResources : declared.footprint.Available rows.terminalValuation := by
    rw [ledgerEq]
    exact declared.resources
  let atom : Atom (N + 1) := .ctor ⟨name, levels, FamilyKey.uniform N spine.familyKeys bounded,
    family.raise N familyBound, relevant⟩
  obtain ⟨plan⟩ := rows.bareConstructorPlan (name := name) (levels := levels)
    (family := family.raise N familyBound)
    henv hscoped hle hTarget resultShape relevant bounded
    (resultCode.raiseFamily N familyBound) resultResources
  obtain ⟨head⟩ := plan.bareObservation (locals := locals) (seed := seed) lookup
    notDefinition notNative notQuotient levelsWF length typeClosed
  have equal := spine.familyReplay_keys atom
  have replayHead := Obs.castAtomPair equal.symm head
  exact (spine.familyReplay atom).path.observe henv replayHead (fun _ _ member => nomatch member)

/-- Every constructor capture comes from an original application child.
The family result certificate is the original requested type code transported
through the retained declaration rows, including all source conversions. -/
theorem HasTypeStrong.seededConstructorObservation
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
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    {family : FamilyData (Profile p)} {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
    (relevant : family.relevant = true)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    {footprint required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals seed available expression.getAppFnArgs.2 required)
    (certificate : CodeCert env U registry target locals seed assigned
      (Profile.singleton (n := p + 1) (.family family)) footprint)
    (resources : footprint.Available available) :
    ∃ (keys : List FamilyKey) (N : Nat) (familyBound : p ≤ N)
      (bounded : ∀ key ∈ keys, key.rank ≤ N),
      ∃ footprint, Nonempty (Obs env U registry target locals seed expression
        (n := N + 1) (.singleton (.ctor ⟨name, levels, FamilyKey.uniform N keys bounded,
          family.raise N familyBound, relevant⟩)) footprint) ∧ footprint.Available available := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head (p + 1)
  obtain ⟨spine, same⟩ := HasTypeStrong.seededSpineCertificate henv hscoped hle earlier
    closed hTarget substitutions fits original head seeds certificate resources
  have payload := earlier formation
  have coverage' : NativeSpineSeedCoverage spine.seeds required := by rw [same]; exact coverage
  obtain ⟨declared⟩ := spine.familyDeclared henv hscoped hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation
    coverage' (Nat.le_of_eq saturated)
  let N := max p (FamilyKey.bound spine.familyKeys)
  have familyBound : p ≤ N := Nat.le_max_left _ _
  have bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N :=
    fun _ member => Nat.le_trans (Nat.le_of_lt (FamilyKey.lt_bound member)) (Nat.le_max_right _ _)
  obtain ⟨u, rawType⟩ := hsource.constWF lookup
  have typeClosed : info.type.Closed := VExpr.WF.closedN hsource ⟨_, rawType⟩ trivial
  exact ⟨spine.familyKeys, N, familyBound, bounded,
    spine.constructorObservation henv hscoped hle hTarget (hle.constants lookup) typeClosed
      levelsWF length notDefinition notNative notQuotient declared saturated resultShape relevant
      N familyBound bounded⟩

end Lean4Lean.AnchoredSource.Adapted
