import Lean4Lean.Theory.Typing.AnchoredFamilyIntroduction
import Lean4Lean.Theory.Typing.AnchoredFamilySourceObservation

/-! The actual source family spine produces the rank-parametric family
clause. Its finite descriptor uses precisely the retained application keys,
raised to one common lower rank. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- Exact finite descriptor output for the eventual source family atom.
Every lower argument admission is produced from the retained original child;
the family terminal traces and future transport are constructed here. -/
theorem FamilySpinePayload.code
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression : VExpr} {level : VLevel}
    {profile : Profile n} {footprint : Footprint}
    {spine : NativeSeededSpineCertificate sourceEnv env U registry.toRegistry source target locals σ available
      name levels expression (.sort level) profile footprint}
    (payload : FamilySpinePayload sourceEnv env U registry.toRegistry source target locals σ available name levels spine)
    (original : sourceEnv.HasTypeStrong U source expression (.sort level) structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry.toRegistry source target locals σ τ available)
    (definitions : registry.definitions name = none)
    (natives : registry.natives name = none) (quotient : name ≠ ``Quot.lift)
    (flag : Relevant level relevant)
    (N : Nat) (bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ N) :
    RankedData.FamilyRelation env U registry (relations env U registry.toRegistry N) target
      (expression.subst σ) (expression.subst τ)
      ⟨name, levels, relevant, FamilyKey.uniform N spine.familyKeys bounded⟩ := by
  have arguments := payload.arguments henv hle closed hTarget substitutions fits
  have raw := (original.refl.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have sourceEq : expression = mkApps (.const name levels) expression.getAppFnArgs.2 := by
    rw [← head]
    exact (VExpr.mkApps_getAppFnArgs_eq expression).symm
  have leftEq : expression.subst σ =
      mkApps (.const name levels) (expression.getAppFnArgs.2.map (·.subst σ)) := by
    simpa only [subst_mkApps, subst] using congrArg (·.subst σ) sourceEq
  have rightEq : expression.subst τ =
      mkApps (.const name levels) (expression.getAppFnArgs.2.map (·.subst τ)) := by
    simpa only [subst_mkApps, subst] using congrArg (·.subst τ) sourceEq
  rw [leftEq, rightEq]
  rw [leftEq, rightEq] at raw
  exact RankedData.literalFamilyCode henv hscoped definitions natives quotient raw flag
    (arguments.uniform henv N bounded)

/-- End-to-end family production from the actual original Strong spine.
The declared rows and family code share precisely the same finite keys and
frozen seed. All requested later field footprints survive in the exact
terminal ledger returned alongside the binary family relation. -/
theorem HasTypeStrong.seededFamilyCode
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry.toRegistry H)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry.toRegistry source target locals σ τ available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels)
      (info.type.instL levels) (.sort headerLevel))
    {expression : VExpr} {structural : Bool} {level : VLevel}
    (original : sourceEnv.HasTypeStrong U source expression (.sort level) structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (saturated : expression.getAppFnArgs.2.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel)
    (definitions : registry.definitions name = none)
    (natives : registry.natives name = none) (quotient : name ≠ ``Quot.lift)
    (flag : Relevant level relevant)
    {profile : Profile n} {footprint required : Footprint}
    (ledger : NativeArgumentLedger env U registry.toRegistry target locals σ available
      expression.getAppFnArgs.2 required)
    (certificate : CodeCert env U registry.toRegistry target locals σ (.sort level) profile footprint)
    (resources : footprint.Available available) :
    ∃ (keys : List FamilyKey) (bounded : ∀ key ∈ keys, key.rank ≤ FamilyKey.bound keys),
      ∃ declared : FamilySeededDeclaredPrefix sourceEnv env U registry.toRegistry target locals σ available
          signature expression.getAppFnArgs.2 (.sort level) profile required keys,
        RankedData.FamilyRelation env U registry (relations env U registry.toRegistry (FamilyKey.bound keys)) target
          (expression.subst σ) (expression.subst τ)
          ⟨name, levels, relevant, FamilyKey.uniform (FamilyKey.bound keys) keys bounded⟩ ∧
        ∃ rows : FamilySeededCodeRows sourceEnv env U registry.toRegistry target required [] []
            (nativeCaptureSubst []) (fun _ => []) (info.type.instL levels) signature.domains keys,
          rows.terminalLocals = List.range expression.getAppFnArgs.2.length ∧
          rows.terminalValuation = declared.valuation ∧
          familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) =
            nativeCaptureSubst (expression.getAppFnArgs.2.map (·.subst σ)) := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head n
  obtain ⟨spine, same, arguments⟩ := HasTypeStrong.seededFamilySpine henv hscoped.base hle earlier
    closed hTarget substitutions.left fits.left original head seeds certificate resources
  have payload := earlier formation
  have coverage' : NativeSpineSeedCoverage spine.seeds required := by rw [same]; exact coverage
  obtain ⟨declared⟩ := spine.familyDeclared henv hscoped.base hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation
    coverage' (Nat.le_of_eq saturated)
  let bounded : ∀ key ∈ spine.familyKeys, key.rank ≤ FamilyKey.bound spine.familyKeys :=
    fun _ member => Nat.le_of_lt (FamilyKey.lt_bound member)
  refine ⟨spine.familyKeys, bounded, declared,
    arguments.code henv hscoped hle original head closed hTarget substitutions fits
      definitions natives quotient flag _ bounded, ?_⟩
  obtain ⟨rows, terminalLocals, terminalValuation⟩ := declared.rows saturated resultSort
  exact ⟨rows, terminalLocals, terminalValuation, declared.seed_eq⟩

end Lean4Lean.AnchoredSource.Adapted
