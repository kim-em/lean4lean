import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
import Lean4Lean.Theory.Typing.AnchoredLevels

/-! Universe packet changes preserve finite source demands. Raw typing is
used only to reconstruct guards at the level-equivalent source syntax; the
semantic guard transport uses the already proved fixed-profile relation laws.
There is no equality-fundamental induction hypothesis in this construction. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem Admitted.levels {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {key : Key n} {left right left' right' : VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (leftEq : EqUpToLevels U left left') (rightEq : EqUpToLevels U right right')
    (admitted : Admitted env U registry target key left right) :
    Admitted env U registry target key left' right' := by
  obtain ⟨anchorPath, path, support, typed, formed, code, anchor, related⟩ := admitted
  have reflexiveAnchor := (EqUpToLevels.refl (CtxStrong.strong henv hTarget).levelWF
    (anchorPath.strong henv hTarget)).1
  exact ⟨anchorPath.eqUpToLevels henv hTarget leftEq,
    ((path.symm.eqUpToLevels henv hTarget leftEq).symm.eqUpToLevels henv hTarget rightEq),
    support, typed, formed, code, Related.levels henv reflexiveAnchor leftEq anchor,
    Related.levels henv leftEq rightEq related⟩

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr}

private theorem anchorLevels (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {key : Key n} (admitted : Admitted env U registry target key key.anchor key.anchor) :
    EqUpToLevels U key.anchor key.anchor :=
  (EqUpToLevels.refl (CtxStrong.strong henv hTarget).levelWF
    (admitted.1.strong henv hTarget)).1

private theorem binderWF (henv : env.Ordered) {A e anchor : VExpr}
    (formed : e.WF env U (A :: target)) (typed : env.HasType U target anchor A) :
    (e.inst anchor).WF env U target := by
  obtain ⟨B, body⟩ := formed
  exact ⟨_, HasType.instN henv .zero body typed⟩

private theorem lambdaGuardLevels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {σ : Subst} {A A' : VExpr} {key : Key n} {support : Profile n}
    (guard : LambdaGuard env U registry target σ A key support)
    (formed : env.IsType U target (A.subst σ))
    (equal : EqUpToLevels U (A.subst σ) (A'.subst σ)) :
    LambdaGuard env U registry target σ A' key support := by
  obtain ⟨u, hA⟩ := formed
  obtain ⟨v, domainTyped⟩ := guard.anchor.1.isType henv hTarget
  have reflexiveDomain := (EqUpToLevels.refl (CtxStrong.strong henv hTarget).levelWF
    (domainTyped.strong henv hTarget)).1
  exact ⟨guard.inputTyped, guard.formed,
    guard.path.trans (.single (hA.eqUpToLevels henv hTarget equal)),
    guard.domains.levels henv reflexiveDomain equal, guard.anchor⟩

private theorem piGuardLevels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {σ : Subst} {A A' B B' prototypeDomain prototypeBody : VExpr}
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
    (domain : env.IsType U target (A.subst σ))
    (body : env.IsType U (A.subst σ :: target) (B.subst σ.lift))
    (domainEq : EqUpToLevels U (A.subst σ) (A'.subst σ))
    (bodyEq : EqUpToLevels U (B.subst σ.lift) (B'.subst σ.lift)) :
    PiGuard env U target σ A' B' prototypeDomain prototypeBody := by
  obtain ⟨u, hA⟩ := domain
  obtain ⟨v, hB⟩ := body
  have domains := hA.eqUpToLevels henv hTarget domainEq
  have bodyContext : OnCtx (A.subst σ :: target) (env.IsType U) := ⟨hTarget, _, hA⟩
  have bodies := hB.eqUpToLevels henv bodyContext bodyEq
  exact ⟨(TypeConversion.single domains).symm.trans guard.domainPath,
    ((TypeConversion.single bodies).symm.trans guard.bodyPath).defeqDFC henv
      (.succ (.refl hTarget) domains)⟩

private theorem relevantLevels {level level' : VLevel} {flag : Bool}
    (relevant : Relevant level flag) (equal : level ≈ level') : Relevant level' flag := by
  cases flag with
  | false => exact equal.symm.trans relevant
  | true => exact fun zero => relevant (equal.trans zero)

mutual
/-- Change only source universe syntax, retaining each finite native tree and
all fixed raw target keys. The second equality is the realized guard equality. -/
theorem Obs.levels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {expression expression' : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression demand footprint)
    (sourceEq : EqUpToLevels U expression expression')
    (realizedEq : EqUpToLevels U (expression.subst σ) (expression'.subst σ))
    (formed : (expression.subst σ).WF env U target) :
    Nonempty (Obs env U registry target locals σ expression' demand footprint) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨(Obs.delta lookup nameEq registered seedWF seedLength levelsWF equivalent
        bodyClosed typeClosed typeCertificate typed body).constLevels rightWF equal⟩
  | .native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨(Obs.native lookup notDefinition nameEq registered seedWF levelsWF equivalent
        signature typeClosed typeCertificate typed tree).constLevels rightWF equal⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨(Obs.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree).constLevels rightWF equal⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases sourceEq with
    | const _ rightWF equal =>
      exact ⟨(Obs.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree).constLevels rightWF equal⟩
  | .var locals σ i demand => cases sourceEq; exact ⟨.var locals σ i demand⟩
  | .empty => exact ⟨.empty⟩
  | .sort relevant =>
    cases sourceEq with
    | sort _ _ equal =>
      exact ⟨.sort (relevantLevels relevant equal)⟩
  | .app fn arg arguments admitted =>
    cases sourceEq with
    | app sourceFn sourceArg =>
      cases realizedEq with
      | app realizedFn realizedArg =>
        obtain ⟨A, B, typedFn, typedArg⟩ := formed.app_inv henv hTarget
        obtain ⟨fn'⟩ := fn.levels henv hTarget sourceFn realizedFn ⟨_, typedFn⟩
        obtain ⟨arg'⟩ := arg.levels henv hTarget sourceArg realizedArg ⟨_, typedArg⟩
        exact ⟨.app fn' arg' arguments (admitted.levels henv hTarget realizedArg realizedArg)⟩
  | .lam domain guard body normal covered =>
    cases sourceEq with
    | lam sourceDomain sourceBody =>
      cases realizedEq with
      | lam realizedDomain realizedBody =>
        obtain ⟨hA, hBody⟩ := formed.lam_inv henv hTarget
        obtain ⟨domain'⟩ := domain.levels henv hTarget sourceDomain realizedDomain
          ⟨_, hA.choose_spec⟩
        have anchor := guard.path.cast guard.anchor.1.hasType.1
        have bodyEq := EqUpToLevels.instN (k := 0) (anchorLevels henv hTarget guard.anchor) realizedBody
        have bodyWF := binderWF henv hBody anchor
        simp only [inst_lift_cons] at bodyEq bodyWF
        obtain ⟨body'⟩ := body.levels henv hTarget sourceBody bodyEq bodyWF
        exact ⟨.lam domain' (lambdaGuardLevels henv hTarget guard hA realizedDomain)
          body' normal covered⟩
  | .pi domain guard bodies =>
    cases sourceEq with
    | forallE sourceDomain sourceBody =>
      cases realizedEq with
      | forallE realizedDomain realizedBody =>
        obtain ⟨T, hPi⟩ := formed
        obtain ⟨hA, hB⟩ := HasType.forallE_inv henv hPi
        obtain ⟨domain'⟩ := domain.levels henv hTarget sourceDomain realizedDomain ⟨_, hA.choose_spec⟩
        obtain ⟨bodies'⟩ := bodies.levels henv hTarget sourceDomain sourceBody
          realizedDomain realizedBody hA hB
        exact ⟨.pi domain' (piGuardLevels henv hTarget guard hA hB realizedDomain realizedBody) bodies'⟩
  | .union left right =>
    obtain ⟨left'⟩ := left.levels henv hTarget sourceEq realizedEq formed
    obtain ⟨right'⟩ := right.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.union left' right'⟩
  | .view source transformation =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.view source' transformation⟩
  | .pad source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.pad source'⟩
  | .unpad source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.unpad source'⟩
  | .rowShift source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.rowShift source'⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.levels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {expression expression' : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (sourceEq : EqUpToLevels U expression expression')
    (realizedEq : EqUpToLevels U (expression.subst σ) (expression'.subst σ))
    (formed : (expression.subst σ).WF env U target) :
    Nonempty (CodeCert env U registry target locals σ expression' profile footprint) := by
  match certificate with
  | .seed observation typed =>
    obtain ⟨observation'⟩ := observation.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.seed observation' typed⟩
  | .union left right =>
    obtain ⟨left'⟩ := left.levels henv hTarget sourceEq realizedEq formed
    obtain ⟨right'⟩ := right.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.union left' right'⟩
  | .pad source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.pad source'⟩
  | .familyPad source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.familyPad source'⟩
  | .unpad source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.unpad source'⟩
  | .down source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.down source'⟩
  | .map transformation source =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.map transformation source'⟩
  | .select source member =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.select source' member⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨source'⟩ := source.levels henv hTarget sourceEq realizedEq formed
    exact ⟨.focusMinimal source' minimal bound⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

theorem PiRows.levels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {A A' B B' : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry target locals σ A B ambient rows footprint)
    (sourceDomain : EqUpToLevels U A A') (sourceBody : EqUpToLevels U B B')
    (realizedDomain : EqUpToLevels U (A.subst σ) (A'.subst σ))
    (realizedBody : EqUpToLevels U (B.subst σ.lift) (B'.subst σ.lift))
    (hA : env.IsType U target (A.subst σ))
    (hB : env.IsType U (A.subst σ :: target) (B.subst σ.lift)) :
    Nonempty (PiRows env U registry target locals σ A' B' ambient rows footprint) := by
  match bodies with
  | .nil => exact ⟨.nil⟩
  | .cons guard body normal covered tail =>
    have anchor := guard.path.cast guard.anchor.1.hasType.1
    have bodyEq := EqUpToLevels.instN (k := 0) (anchorLevels henv hTarget guard.anchor) realizedBody
    have bodyWF := binderWF henv ⟨_, hB.choose_spec⟩ anchor
    simp only [inst_lift_cons] at bodyEq bodyWF
    obtain ⟨body'⟩ := body.levels henv hTarget sourceBody bodyEq bodyWF
    obtain ⟨tail'⟩ := tail.levels henv hTarget sourceDomain sourceBody realizedDomain realizedBody hA hB
    exact ⟨.cons (lambdaGuardLevels henv hTarget guard hA realizedDomain) body' normal covered tail'⟩
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega
end


/-- The declared-header consumer: one representative packet certificate
becomes a certificate of the actual scoped packet with unchanged footprint.
Its raw formation can be obtained from the original constDF type child by
raw level congruence; no semantic induction on that derived typing occurs. -/
theorem CodeCert.instLevels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {type : VExpr}
    {seed levels : List VLevel} {profile : Profile n} {footprint : Footprint}
    (closed : type.Closed)
    (seedWF : ∀ level ∈ seed, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seed levels)
    (certificate : CodeCert env U registry target locals σ (type.instL seed) profile footprint)
    (formed : env.IsType U target (type.instL seed)) :
    Nonempty (CodeCert env U registry target locals σ (type.instL levels) profile footprint) := by
  have seedClosed : (type.instL seed).subst σ = type.instL seed := closed.instL.subst_eq .zero
  have levelsClosed : (type.instL levels).subst σ = type.instL levels := closed.instL.subst_eq .zero
  have equal := EqUpToLevels.instL_expr type seedWF levelsWF equivalent
  apply certificate.levels henv hTarget equal
  · simpa only [seedClosed, levelsClosed] using equal
  · simpa only [seedClosed] using (show (type.instL seed).WF env U target from
      ⟨_, formed.choose_spec⟩)

end Lean4Lean.AnchoredSource.Adapted
