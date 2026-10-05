import Lean4Lean.Theory.Typing.AnchoredOriginalTailPrefix

/-! Constant replay calls only the original ambient header equality and
conversion children, each with its exact captured source formation context. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def ConstantCall.contextDerivation
    {context : List VExpr} {left right type : VExpr}
    {reference : EndpointRef sourceEnv U source expression assigned}
    {original : Derivation sourceEnv U context left right type}
    (call : ConstantCall reference original) (initial : ContextDerivation sourceEnv U source) :
    ContextDerivation sourceEnv U context := by
  cases call <;> exact initial

theorem ConstantCall.contextDerivation_closures
    {context : List VExpr} {left right type : VExpr}
    {reference : EndpointRef sourceEnv U source expression assigned}
    {original : Derivation sourceEnv U context left right type}
    (call : ConstantCall reference original) (initial : ContextDerivation sourceEnv U source) :
    (call.contextDerivation initial).closures = initial.closures := by
  cases call <;> rfl

def ConstantPrefixCall.contextDerivation
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    {packet : ConstantPrefix first}
    {original : Derivation sourceEnv U context left right type}
    (call : ConstantPrefixCall packet original) (initial : ContextDerivation sourceEnv U source) :
    ContextDerivation sourceEnv U context :=
  match call with
  | .conversion call => call.contextDerivation initial
  | .ambient call => call.contextDerivation initial

theorem ConstantPrefixCall.contextDerivation_closures
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    {packet : ConstantPrefix first}
    (call : ConstantPrefixCall packet original) (initial : ContextDerivation sourceEnv U source) :
    (call.contextDerivation initial).closures = call.environment initial.closures := by
  cases call with
  | conversion call => exact call.contextDerivation_closures initial
  | ambient call => exact call.contextDerivation_closures initial

def ConstantCall.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConstantCall reference original),
    DerivationFundamental env registry (call.contextDerivation initial) original

def ConstantPrefixCall.Fundamentals (env : VEnv) (registry : CanonicalHead.Registry)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first) (initial : ContextDerivation sourceEnv U source) : Prop :=
  ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
    (call : ConstantPrefixCall packet original),
    DerivationFundamental env registry (call.contextDerivation initial) original

theorem EndpointRef.replayConstantOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel} {assigned : VExpr}
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels)
    (primitive : reference.Primitive) (calls : ConstantCall.Fundamentals env registry reference initial)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      have joint := (calls .left).left henv hscoped
      obtain ⟨answer⟩ := certificate.transfer_graded henv hscoped hTarget closed
        (joint target locals σ σ available closed hTarget substitutions (TailPairedFits.diagonal initial fits)).1 resources
      exact ⟨⟨_, by assumption, answer, .refl⟩⟩
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl lookup levelsWF otherLevelsWF levelCount levelEquality levelWF headerClosed ambient =>
      have joint := calls .right
      obtain ⟨answer⟩ := certificate.transfer_graded henv hscoped hTarget closed
        (joint target locals σ σ available closed hTarget substitutions (TailPairedFits.diagonal initial fits)).1 resources
      exact ⟨⟨_, by assumption, answer, .single ((ambient.forget.defeq.mono below).substDF henv
        substitutions.wf hTarget substitutions)⟩⟩

private theorem PrefixRoute.replayHeaderOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Fundamentals env registry route initial)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty
        (ConstantReplayResult sourceEnv env U registry target locals σ available name levels natural profile))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backward, _⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (TailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed backward resources
    obtain ⟨result⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    obtain ⟨rawLevel, _, equal⟩ := plan.sound
    have path := TypeConversion.single ((equal.symm.defeq.mono below).substDF henv
      substitutions.wf hTarget substitutions)
    exact ⟨{ result with
      transfer := { result.transfer with related := changed.related.trans henv result.transfer.related }
      targetPath := path.trans result.targetPath }⟩

/-- Complete backward transport from an actual syntactic constant endpoint
to its displayed declaration header. All semantic calls are the packet's
finite, strictly smaller original children. -/
theorem ConstantPrefix.replayOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {name : Name} {levels : List VLevel}
    {first : EndpointState sourceEnv U source (.const name levels) assigned}
    (packet : ConstantPrefix first)
    (calls : ConstantPrefixCall.Fundamentals env registry packet initial)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (ConstantReplayResult sourceEnv env U registry target locals σ available
      name levels assigned profile) := by
  exact packet.route.replayHeaderOriginal henv hscoped below initial closed hTarget substitutions fits
    (fun call => calls (.conversion call))
    (fun current present => EndpointRef.replayConstantOriginal henv hscoped below initial closed hTarget
      substitutions fits packet.reference rfl packet.primitive (fun call => calls (.ambient call)) current present)
    certificate resources

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
