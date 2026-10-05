import Lean4Lean.Theory.Typing.AnchoredBoundedSupportedReplay
import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredTerminalProtected
import Lean4Lean.Theory.Typing.NativeTerminalSoundness

/-! The protected native result support and raw equation opening use only
same-fuel predecessor interpretations and the original bounded children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem NativeSupportedReplay.witnessedBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (rawArguments : Ctx.SubstEq env U target arguments arguments argumentSource)
    (argumentFits : Staged.PairedFits current fuel env U registry argumentSource target argumentLocals
      arguments arguments argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (replayBound : replay.nativeDepth current ≤ fuel) :
    Ctx.SubstEq env U target captures captures declared ∧
    Staged.PairedFits current fuel env U registry declared target locals captures captures available := by
  induction replay with
  | nil => exact ⟨.nil, by constructor <;> constructor <;> intro _ _ h <;> cases h⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have raw := rawArguments
    have fits := argumentFits
    rw [source] at raw fits
    exact ⟨Ctx.SubstEq.nativePrefix raw, fits.nativePrefix (List.range declared.length)⟩
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativeSupportedReplay.nativeDepth] using replayBound)
    obtain ⟨raw, fits⟩ := ih bounds.1
    have formed := formation.defeq.mono hle |>.hasType.1
    obtain ⟨entry, _⟩ := argumentFits.forward.entry position ⟨n, input⟩ needed natural lookup
    have pair := alignment.related henv typed declaredCode entry.related
    exact ⟨.cons raw formed (alignment.path.cast (rawArguments.lookup lookup)),
      fits.pushCertificates henv hTarget domainCode domainCode bounds.2 bounds.2 resources resources
        typed typed pair pair localNeeds bounded covered⟩
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      localNeeds n bounded empty ih =>
    obtain ⟨raw, fits⟩ := ih (by simpa only [NativeSupportedReplay.nativeDepth] using replayBound)
    let certificate : CodeCert env U registry target locals captures domain
        (Profile.empty (n := n)) [] := .seed .empty (.empty (.sort true))
    have related : Related env U registry target witness witness (domain.subst captures)
        (Profile.empty (n := n)) .empty := by
      apply Related.of_singletons
      intro atom member
      cases member
    exact ⟨.cons raw formation inhabitant,
      fits.pushCertificates henv hTarget certificate certificate
        (by simp only [certificate, CodeCert.nativeDepth, Obs.nativeDepth]; omega)
        (by simp only [certificate, CodeCert.nativeDepth, Obs.nativeDepth]; omega)
        (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        (.empty .empty) (.empty .empty) related related localNeeds bounded
        (fun need member atom atomMember => (empty need member atom atomMember).elim)⟩

theorem NativeSupportedReplay.declaredTerminalPairProtectedBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : Staged.PairedFits current fuel env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    {domains : List VExpr} {plan : CapturePlan domains.reverse} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable domains.reverse plan captures locals available)
    (replayBound : replay.nativeDepth current ≤ fuel)
    (closed : available.AtomClosed)
    {rhs result : VExpr}
    (original : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ result : DeclaredTerminalProtectedResult env U registry target locals captures
      (plan.captures (nativeCaptureSubst newValues)) available rhs result demand
      (plan.added (nativeCaptureSubst newValues)) plan.count, result.certificate.nativeDepth current ≤ fuel := by
  obtain ⟨raw, fits⟩ := replay.witnessedBounded henv hle hTarget rawArguments.left argumentFits.left replayBound
  obtain ⟨base⟩ := Staged.HasTypeStrong.declaredRhs (source := []) henv hscoped hsource hle earlier
    trivial original formation closed hTarget
    (by simpa only [List.append_nil] using raw)
    (by simpa only [List.append_nil] using fits) body bodyBound resources
  obtain ⟨insertion, ⟨terminal⟩⟩ := replay.declaredTerminalPairBounded henv hscoped hsource hle earlier
    hTarget newValues newLength rawArguments argumentFits replayBound closed original formation body bodyBound resources
  have typed := base.opened.requestedTyped
  have code := TypeRelated.lower henv base.opened.bound base.opened.typeCode
  have witnessed := lowerProfile.related base.opened.bound henv hTarget base.related
  have related := lowerProfile.related terminal.opened.bound henv (insertion.targetWF henv)
    terminal.related
  have raised (expression : VExpr) : expression.subst (raisedSubst captures plan.count) =
      (expression.subst captures).lift' (.skipN .refl plan.count) := by
    have substitution : captures.lift_r (.skipN .refl plan.count) =
        raisedSubst captures plan.count := by
      funext i
      exact lift'_consN_skipN (k := 0)
    rw [← substitution, ← lift'_subst]
  simp only [raised] at related
  exact ⟨{
    support := lowerProfile n base.opened.bound base.opened.support
    footprint := base.opened.typeFootprint
    certificate := base.opened.requestedCertificate
    resources := base.opened.typeAvailable
    typed := typed
    typeCode := code
    witnessed := witnessed
    insertion := insertion
    related := related.retag henv (Profile.rename_hasType_iff.mpr typed)
      (code.future henv insertion.toFuture) }, by
      simpa only [GradedTransferResult.requestedCertificate, CodeCert.nativeDepth_lower] using base.opened.certificateBound⟩

theorem native_openEquation_originalBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {domains : List VExpr} {lhs rhs result : VExpr}
    (left : sourceEnv.HasTypeStrong U [] (wrapLams domains lhs) (wrapForalls domains result) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs) (wrapForalls domains result) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    (equation : env.IsDefEq U [] (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains result)) :
    env.IsDefEq U domains.reverse lhs rhs result := by
  have context := (HasType.native_open henv (by trivial) (left.refl.defeq.mono hle)).1
  obtain ⟨_, _, _, _, leftTyped⟩ := Staged.HasTypeStrong.openDeclaredBody henv hscoped hle earlier left formation context
  obtain ⟨_, _, _, _, rightTyped⟩ := Staged.HasTypeStrong.openDeclaredBody henv hscoped hle earlier right formation context
  exact native_openEquation henv (by simpa only [List.append_nil] using context)
    (by simpa only [List.append_nil] using leftTyped)
    (by simpa only [List.append_nil] using rightTyped) equation


theorem SaturatedProgram.openEquation_originalBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {data : NativeRecursorData} {program : SaturatedProgram data} {arguments : List VExpr}
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level)) :
    env.IsDefEq U (program.equationBody.domains.map (·.instL program.levels)).reverse
      (program.equationBody.lhs.instL program.levels) (program.equationBody.rhs.instL program.levels)
      (program.equationBody.type.instL program.levels) := by
  have spec := saturatedProgram_spec selected
  have selection := spec.2.2.2.2.2.2.2.2.1
  have parts := CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1
  have equation : env.IsDefEq U [] (program.equation.lhs.instL program.levels)
      (program.equation.rhs.instL program.levels) (program.equation.type.instL program.levels) :=
    .extra (registered.singletonEquation selection) levelsWF
      (spec.2.1.trans (singletonEquation_uvars selection).symm)
  rw [← parts.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at left
  rw [← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at right
  rw [← parts.2.2, instL_wrapForalls] at formation
  rw [← parts.1, ← parts.2.1, ← parts.2.2, instL_wrapLams, instL_wrapLams,
    instL_wrapForalls] at equation
  exact native_openEquation_originalBounded henv hscoped hle earlier left right formation equation


end Lean4Lean.AnchoredSource.Adapted
