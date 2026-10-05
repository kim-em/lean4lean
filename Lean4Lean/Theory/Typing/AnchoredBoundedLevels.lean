import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels
import Lean4Lean.Theory.Typing.AnchoredNativeDepth

/-! Scoped universe transport preserves the exact current-native depth of
actual source observations, certificates and Pi rows. This keeps the source
certificate returned by native constant transfer within its stage fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private anchorLevels binderWF lambdaGuardLevels piGuardLevels relevantLevels
  from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr}

mutual
/-- Change only source universe syntax, retaining each finite native tree and
all fixed raw target keys. The second equality is the realized guard equality. -/
theorem Obs.levelsDepth
    (current : Name → Bool) (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {expression expression' : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    (sourceEq : EqUpToLevels U expression expression')
    (realizedEq : EqUpToLevels U (expression.subst σ) (expression'.subst σ))
    (formed : (expression.subst σ).WF env U target) :
    ∃ output : Obs env U registry target locals σ expression' demand footprint,
      output.nativeDepth current = observation.nativeDepth current := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨.delta lookup nameEq registered seedWF seedLength rightWF (levelsTrans equivalent equal)
        bodyClosed typeClosed typeCertificate typed body, by simp only [Obs.nativeDepth]⟩
  | .native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨.native lookup notDefinition nameEq registered seedWF rightWF (levelsTrans equivalent equal)
        signature typeClosed typeCertificate typed tree, by simp only [Obs.nativeDepth]⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength rightWF
        (levelsTrans equivalent equal) signature typeClosed typeCertificate typed tree,
        by simp only [Obs.nativeDepth]⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨.constructor lookup noDefinition noNative noQuotient seedWF seedLength rightWF
        (levelsTrans equivalent equal) signature typeClosed typeCertificate typed tree,
        by simp only [Obs.nativeDepth]⟩
  | .var locals σ i demand => cases sourceEq; exact ⟨.var locals σ i demand, by simp only [Obs.nativeDepth, *]⟩
  | .empty => exact ⟨.empty, by simp only [Obs.nativeDepth, *]⟩
  | .sort relevant =>
    cases sourceEq with
    | sort _ _ equal =>
      exact ⟨.sort (relevantLevels relevant equal), by simp only [Obs.nativeDepth, *]⟩
  | .app fn arg arguments admitted =>
    cases sourceEq with
    | app sourceFn sourceArg =>
      cases realizedEq with
      | app realizedFn realizedArg =>
        obtain ⟨A, B, typedFn, typedArg⟩ := formed.app_inv henv hTarget
        obtain ⟨fn', fnDepth⟩ := fn.levelsDepth current henv hTarget sourceFn realizedFn ⟨_, typedFn⟩
        obtain ⟨arg', argDepth⟩ := arg.levelsDepth current henv hTarget sourceArg realizedArg ⟨_, typedArg⟩
        exact ⟨.app fn' arg' arguments (admitted.levels henv hTarget realizedArg realizedArg), by simp only [Obs.nativeDepth, *]⟩
  | .lam domain guard body normal covered =>
    cases sourceEq with
    | lam sourceDomain sourceBody =>
      cases realizedEq with
      | lam realizedDomain realizedBody =>
        obtain ⟨hA, hBody⟩ := formed.lam_inv henv hTarget
        obtain ⟨domain', domainDepth⟩ := domain.levelsDepth current henv hTarget sourceDomain realizedDomain
          ⟨_, hA.choose_spec⟩
        have anchor := guard.path.cast guard.anchor.1.hasType.1
        have bodyEq := EqUpToLevels.instN (k := 0) (anchorLevels henv hTarget guard.anchor) realizedBody
        have bodyWF := binderWF henv hBody anchor
        simp only [inst_lift_cons] at bodyEq bodyWF
        obtain ⟨body', bodyDepth⟩ := body.levelsDepth current henv hTarget sourceBody bodyEq bodyWF
        exact ⟨.lam domain' (lambdaGuardLevels henv hTarget guard hA realizedDomain)
          body' normal covered, by simp only [Obs.nativeDepth, *]⟩
  | .pi domain guard bodies =>
    cases sourceEq with
    | forallE sourceDomain sourceBody =>
      cases realizedEq with
      | forallE realizedDomain realizedBody =>
        obtain ⟨T, hPi⟩ := formed
        obtain ⟨hA, hB⟩ := HasType.forallE_inv henv hPi
        obtain ⟨domain', domainDepth⟩ := domain.levelsDepth current henv hTarget sourceDomain realizedDomain ⟨_, hA.choose_spec⟩
        obtain ⟨bodies', bodiesDepth⟩ := bodies.levelsDepth current henv hTarget sourceDomain sourceBody
          realizedDomain realizedBody hA hB
        exact ⟨.pi domain' (piGuardLevels henv hTarget guard hA hB realizedDomain realizedBody) bodies', by simp only [Obs.nativeDepth, *]⟩
  | .union left right =>
    obtain ⟨left', leftDepth⟩ := left.levelsDepth current henv hTarget sourceEq realizedEq formed
    obtain ⟨right', rightDepth⟩ := right.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.union left' right', by simp only [Obs.nativeDepth, *]⟩
  | .view source transformation =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.view source' transformation, by simp only [Obs.nativeDepth, *]⟩
  | .pad source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.pad source', by simp only [Obs.nativeDepth, *]⟩
  | .unpad source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.unpad source', by simp only [Obs.nativeDepth, *]⟩
  | .rowShift source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.rowShift source', by simp only [Obs.nativeDepth, *]⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.levelsDepth
    (current : Name → Bool) (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {expression expression' : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (sourceEq : EqUpToLevels U expression expression')
    (realizedEq : EqUpToLevels U (expression.subst σ) (expression'.subst σ))
    (formed : (expression.subst σ).WF env U target) :
    ∃ output : CodeCert env U registry target locals σ expression' profile footprint,
      output.nativeDepth current = certificate.nativeDepth current := by
  match certificate with
  | .seed observation typed =>
    obtain ⟨observation', observationDepth⟩ := observation.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.seed observation' typed, by simp only [CodeCert.nativeDepth, *]⟩
  | .union left right =>
    obtain ⟨left', leftDepth⟩ := left.levelsDepth current henv hTarget sourceEq realizedEq formed
    obtain ⟨right', rightDepth⟩ := right.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.union left' right', by simp only [CodeCert.nativeDepth, *]⟩
  | .pad source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.pad source', by simp only [CodeCert.nativeDepth, *]⟩
  | .familyPad source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.familyPad source', by simp only [CodeCert.nativeDepth, *]⟩
  | .unpad source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.unpad source', by simp only [CodeCert.nativeDepth, *]⟩
  | .down source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.down source', by simp only [CodeCert.nativeDepth, *]⟩
  | .map transformation source =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.map transformation source', by simp only [CodeCert.nativeDepth, *]⟩
  | .select source member =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.select source' member, by simp only [CodeCert.nativeDepth, *]⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨source', sourceDepth⟩ := source.levelsDepth current henv hTarget sourceEq realizedEq formed
    exact ⟨.focusMinimal source' minimal focusedBound, by simp only [CodeCert.nativeDepth, *]⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

theorem PiRows.levelsDepth
    (current : Name → Bool) (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {A A' B B' : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry target locals σ A B ambient rows footprint)
    (sourceDomain : EqUpToLevels U A A') (sourceBody : EqUpToLevels U B B')
    (realizedDomain : EqUpToLevels U (A.subst σ) (A'.subst σ))
    (realizedBody : EqUpToLevels U (B.subst σ.lift) (B'.subst σ.lift))
    (hA : env.IsType U target (A.subst σ))
    (hB : env.IsType U (A.subst σ :: target) (B.subst σ.lift)) :
    ∃ output : PiRows env U registry target locals σ A' B' ambient rows footprint,
      output.nativeDepth current = bodies.nativeDepth current := by
  match bodies with
  | .nil => exact ⟨.nil, by simp only [PiRows.nativeDepth, *]⟩
  | .cons guard body normal covered tail =>
    have anchor := guard.path.cast guard.anchor.1.hasType.1
    have bodyEq := EqUpToLevels.instN (k := 0) (anchorLevels henv hTarget guard.anchor) realizedBody
    have bodyWF := binderWF henv ⟨_, hB.choose_spec⟩ anchor
    simp only [inst_lift_cons] at bodyEq bodyWF
    obtain ⟨body', bodyDepth⟩ := body.levelsDepth current henv hTarget sourceBody bodyEq bodyWF
    obtain ⟨tail', tailDepth⟩ := tail.levelsDepth current henv hTarget sourceDomain sourceBody realizedDomain realizedBody hA hB
    exact ⟨.cons (lambdaGuardLevels henv hTarget guard hA realizedDomain) body' normal covered tail', by simp only [PiRows.nativeDepth, *]⟩
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega
end

theorem CodeCert.instLevelsDepth
    (current : Name → Bool) (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {type : VExpr}
    {seed levels : List VLevel} {profile : Profile n} {footprint : Footprint}
    (closed : type.Closed)
    (seedWF : ∀ level ∈ seed, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seed levels)
    (certificate : CodeCert env U registry target locals σ (type.instL seed) profile footprint)
    (formed : env.IsType U target (type.instL seed)) :
    ∃ output : CodeCert env U registry target locals σ (type.instL levels) profile footprint,
      output.nativeDepth current = certificate.nativeDepth current := by
  have seedClosed : (type.instL seed).subst σ = type.instL seed := closed.instL.subst_eq .zero
  have levelsClosed : (type.instL levels).subst σ = type.instL levels := closed.instL.subst_eq .zero
  have equal := EqUpToLevels.instL_expr type seedWF levelsWF equivalent
  apply certificate.levelsDepth current henv hTarget equal
  · simpa only [seedClosed, levelsClosed] using equal
  · simpa only [seedClosed] using (show (type.instL seed).WF env U target from
      ⟨_, formed.choose_spec⟩)

end Lean4Lean.AnchoredSource.Adapted
