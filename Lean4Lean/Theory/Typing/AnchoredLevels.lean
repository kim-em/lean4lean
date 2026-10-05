import Lean4Lean.Theory.Typing.AnchoredExposureLevels
import Lean4Lean.Theory.Typing.AnchoredConversion
import Lean4Lean.Theory.Typing.AnchoredDataLevels

/-! Fixed-profile endpoint congruence for scoped universe changes. The proof
recurses on observation rank; canonical trace congruence is the only new head
producer, and every generated domain guard is transported by raw typing. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private def CodeLevels {env : VEnv} {U : Nat} (lower : Relations n) : Prop :=
  ∀ {Γ left right left' right' profile}, EqUpToLevels U left left' →
    EqUpToLevels U right right' → lower.code Γ left right profile →
      lower.code Γ left' right' profile

private def TermLevels {env : VEnv} {U : Nat} (lower : Relations n) : Prop :=
  ∀ {Γ left right left' right' type value support}, EqUpToLevels U left left' →
    EqUpToLevels U right right' → lower.term Γ left right type value support →
      lower.term Γ left' right' type value support

private theorem reflexiveLevels (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.HasType U Γ e A) : EqUpToLevels U e e :=
  (EqUpToLevels.refl (CtxStrong.strong henv hΓ).levelWF (h.strong henv hΓ)).1

private theorem path_leftType (h : TypeConversion env U Γ A B)
    (hb : env.IsType U Γ B) : env.IsType U Γ A := by
  induction h with
  | refl => exact hb
  | tail _ edge ih => exact ih ⟨_, edge.hasType.1⟩

private theorem path_rightType (h : TypeConversion env U Γ A B)
    (ha : env.IsType U Γ A) : env.IsType U Γ B := by
  cases h with
  | refl => exact ha
  | tail _ edge => exact ⟨_, edge.hasType.2⟩

private theorem sort_levels (henv : env.Ordered)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : SortRelated env U registry Γ left right relevant) :
    SortRelated env U registry Γ left' right' relevant := by
  obtain ⟨Δ, ρ, u, v, ⟨leftExposure⟩, ⟨rightExposure⟩, levels, flag⟩ := related
  obtain ⟨leftHead, ⟨leftNew⟩, leftEq⟩ := leftExposure.levels henv leftLevels
  obtain ⟨rightHead, ⟨rightNew⟩, rightEq⟩ := rightExposure.levels henv rightLevels
  cases leftEq with | sort _ _ leftEq =>
    cases rightEq with | sort _ _ rightEq =>
      refine ⟨Δ, ρ, _, _, ⟨leftNew⟩, ⟨rightNew⟩,
        leftEq.symm.trans (levels.trans rightEq), ?_⟩
      cases relevant with
      | false => exact leftEq.symm.trans flag
      | true => exact fun hz => flag (leftEq.trans hz)

private theorem pi_levels
    (henv : env.Ordered) (code : CodeLevels (env := env) (U := U) lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (display : PiWitness env U registry lower Γ left right A B domain rows) :
    Nonempty (PiWitness env U registry lower Γ left' right' A B domain rows) := by
  obtain ⟨leftHead, ⟨leftNew⟩, leftEq⟩ := display.leftExposure.levels henv leftLevels
  obtain ⟨rightHead, ⟨rightNew⟩, rightEq⟩ := display.rightExposure.levels henv rightLevels
  cases leftEq with | @forallE leftA leftA' leftB leftB' leftDomainEq leftBodyEq =>
    cases rightEq with | @forallE rightA rightA' rightB rightB' rightDomainEq rightBodyEq =>
      have hctx := display.leftExposure.targetWF henv
      obtain ⟨u, hA⟩ := display.leftDomainType
      obtain ⟨u', hA'⟩ := display.rightDomainType
      have leftDomain := hA.eqUpToLevels henv hctx leftDomainEq
      have rightDomain := hA'.eqUpToLevels henv hctx rightDomainEq
      have leftCtx : IsDefEqCtx env U [] (display.leftDomain :: display.context)
          (leftA' :: display.context) := .succ (.refl hctx) leftDomain
      have rightCtx : IsDefEqCtx env U [] (display.rightDomain :: display.context)
          (rightA' :: display.context) := .succ (.refl hctx) rightDomain
      obtain ⟨v, hB⟩ := display.leftBodyType
      obtain ⟨v', hB'⟩ := display.rightBodyType
      have hLeftWF : OnCtx (display.leftDomain :: display.context) (env.IsType U) := ⟨hctx, u, hA⟩
      have hRightWF : OnCtx (display.rightDomain :: display.context) (env.IsType U) := ⟨hctx, u', hA'⟩
      have leftBody := hB.eqUpToLevels henv hLeftWF leftBodyEq
      have rightBody := hB'.eqUpToLevels henv hRightWF rightBodyEq
      obtain ⟨w, hRightAtLeft⟩ := path_rightType display.bodies ⟨v, hB⟩
      have rightAtLeft := hRightAtLeft.eqUpToLevels henv hLeftWF rightBodyEq
      refine ⟨{
        context := display.context
        map := display.map
        leftDomain := leftA'
        rightDomain := rightA'
        leftBody := leftB'
        rightBody := rightB'
        leftExposure := leftNew
        rightExposure := rightNew
        leftDomainType := ⟨u, leftDomain.hasType.2⟩
        rightDomainType := ⟨u', rightDomain.hasType.2⟩
        leftBodyType := ⟨v, leftBody.hasType.2.defeqDFC henv leftCtx⟩
        rightBodyType := ⟨v', rightBody.hasType.2.defeqDFC henv rightCtx⟩
        domains := (TypeConversion.single leftDomain.symm).trans
          (display.domains.trans (.single rightDomain))
        bodies := ((TypeConversion.single leftBody.symm).trans
          (display.bodies.trans (.single rightAtLeft))).defeqDFC henv leftCtx
        prototypeDomainPath := (TypeConversion.single leftDomain.symm).trans
          display.prototypeDomainPath
        prototypeBodyPath := ((TypeConversion.single leftBody.symm).trans
          display.prototypeBodyPath).defeqDFC henv leftCtx
        domainRelated := code leftDomainEq rightDomainEq display.domainRelated
        rowDomains := ?_
        rowBodies := ?_ }⟩
      · intro key result member
        obtain ⟨support, typed, formed, smaller, path, related⟩ := display.rowDomains key result member
        obtain ⟨k, hk⟩ := path_leftType path ⟨u, hA⟩
        exact ⟨support, typed, formed, smaller, path.trans (.single leftDomain),
          code (reflexiveLevels henv hctx hk) leftDomainEq related⟩
      · intro key result member Δ ρ future x y admitted
        have hx := reflexiveLevels henv (future.targetWF henv) admitted.2.1.hasType.1
        have hy := reflexiveLevels henv (future.targetWF henv) admitted.2.1.hasType.2
        obtain ⟨first, second, cross⟩ := display.rowBodies key result member Δ ρ future x y admitted
        exact ⟨code (.instN hx (leftBodyEq.lift' ρ.cons))
            (.instN hy (leftBodyEq.lift' ρ.cons)) first,
          code (.instN hx (rightBodyEq.lift' ρ.cons))
            (.instN hy (rightBodyEq.lift' ρ.cons)) second,
          code (.instN hx (leftBodyEq.lift' ρ.cons))
            (.instN hx (rightBodyEq.lift' ρ.cons)) cross⟩

private theorem function_levels
    (henv : env.Ordered) (term : TermLevels (env := env) (U := U) lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (behavior : FunctionBehavior env U registry lower Γ left right type key output support) :
    FunctionBehavior env U registry lower Γ left' right' type key output support := by
  obtain ⟨anchor, A, B, domain, rows, result, typeMember, rowMember, typed, display, behavior⟩ := behavior
  refine ⟨anchor, A, B, domain, rows, result, typeMember, rowMember, typed, display, ?_⟩
  intro Δ ρ future x y admitted
  have hx := reflexiveLevels henv (future.targetWF henv) admitted.2.1.hasType.1
  have hy := reflexiveLevels henv (future.targetWF henv) admitted.2.1.hasType.2
  obtain ⟨first, second, cross⟩ := behavior Δ ρ future x y admitted
  exact ⟨term (.app (leftLevels.lift' _) hx) (.app (leftLevels.lift' _) hy) first,
    term (.app (rightLevels.lift' _) hx) (.app (rightLevels.lift' _) hy) second,
    term (.app (leftLevels.lift' _) hx) (.app (rightLevels.lift' _) hx) cross⟩

private theorem level_congruence (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (henv : env.Ordered) (n : Nat) :
    CodeLevels (env := env) (U := U) (relations env U registry n) ∧
    TermLevels (env := env) (U := U) (relations env U registry n) := by
  induction n with
  | zero =>
    have code : CodeLevels (env := env) (U := U) (relations env U registry 0) := by
      intro Γ left right left' right' profile leftLevels rightLevels related Δ ρ future atom member
      exact sort_levels henv (leftLevels.lift' ρ) (rightLevels.lift' ρ)
        (related Δ ρ future atom member)
    refine ⟨code, ?_⟩
    intro Γ left right left' right' type value support leftLevels rightLevels related atom member Δ ρ future
    rcases related atom member Δ ρ future with empty | ⟨Ω, τ, frame, typed, typeCode, valueCode⟩
    · exact .inl empty
    · exact .inr ⟨Ω, τ, frame, typed, typeCode,
        code ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) valueCode⟩
  | succ n ih =>
    have atomLevels : ∀ {Γ left right left' right' atom}, EqUpToLevels U left left' →
        EqUpToLevels U right right' →
        CodeAtom env U registry (relations env U registry n) Γ left right atom →
        CodeAtom env U registry (relations env U registry n) Γ left' right' atom := by
      intro Γ left right left' right' atom leftLevels rightLevels related
      cases atom with
      | sort relevant => exact sort_levels henv leftLevels rightLevels related
      | fn | ctor | record => exact False.elim related
      | family data =>
        obtain ⟨witness⟩ := related
        exact witness.levels henv ih.2 leftLevels rightLevels
      | pad atom => exact ih.1 leftLevels rightLevels related
      | pi A B domain rows =>
        obtain ⟨display⟩ := related
        exact pi_levels henv ih.1 leftLevels rightLevels display
    have code : CodeLevels (env := env) (U := U) (relations env U registry (n + 1)) := by
      intro Γ left right left' right' profile leftLevels rightLevels related Δ ρ future atom member
      exact atomLevels (leftLevels.lift' ρ) (rightLevels.lift' ρ)
        (related Δ ρ future atom member)
    refine ⟨code, ?_⟩
    intro Γ left right left' right' type value support leftLevels rightLevels related atom member Δ ρ future
    rcases related atom member Δ ρ future with empty | ⟨Ω, τ, frame, typed, typeCode, values⟩
    · exact .inl empty
    · refine .inr ⟨Ω, τ, frame, typed, typeCode, ?_⟩
      intro atom member
      have value := values atom member
      cases atom with
      | fn key output =>
        exact function_levels henv ih.2
          ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | pad atom => exact ih.2 ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | sort relevant => exact code ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | pi A B domain rows => exact code ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | family data => exact code ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | ctor data =>
        exact RankedData.ConstructorRelation.levels henv ih.2
          ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value
      | record data =>
        exact RankedData.RecordRelation.levels henv ih.2
          ((leftLevels.lift' ρ).lift' τ) ((rightLevels.lift' ρ).lift' τ) value

theorem TypeRelated.levels (henv : env.Ordered)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left' right' profile :=
  (level_congruence env U registry henv _).1 leftLevels rightLevels related

theorem Related.levels (henv : env.Ordered)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : Related env U registry Γ left right type value support) :
    Related env U registry Γ left' right' type value support :=
  (level_congruence env U registry henv _).2 leftLevels rightLevels related

/-- One concrete stored result supplies every scoped equivalent instance at
its unchanged finite demand and support. The declared type moves to the LEFT
packet using its stored code capability, rather than a new typing IH. -/
theorem Related.instances
    {seed leftLevels rightLevels : List VLevel} {expression type : VExpr}
    {Γ : List VExpr} {n : Nat} {value support : Profile n}
    (henv : env.Ordered)
    (seedWF : ∀ level ∈ seed, level.WF U)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (seedLeft : List.Forall₂ (· ≈ ·) seed leftLevels)
    (seedRight : List.Forall₂ (· ≈ ·) seed rightLevels)
    (typed : value.HasType support)
    (code : TypeRelated env U registry Γ (type.instL seed) (type.instL seed) support)
    (related : Related env U registry Γ (expression.instL seed) (expression.instL seed)
      (type.instL seed) value support) :
    TypeRelated env U registry Γ (type.instL leftLevels) (type.instL leftLevels) support ∧
      Related env U registry Γ (expression.instL leftLevels) (expression.instL rightLevels)
        (type.instL leftLevels) value support := by
  have allSelf : ∀ packet : List VLevel, List.Forall₂ (· ≈ ·) packet packet := by
    intro packet
    induction packet with
    | nil => exact .nil
    | cons level rest ih => exact .cons rfl ih
  have seedSelf := allSelf seed
  have typeSelf := EqUpToLevels.instL_expr type seedWF seedWF seedSelf
  have typeLeft := EqUpToLevels.instL_expr type seedWF leftWF seedLeft
  have endpoints := related.levels henv
    (EqUpToLevels.instL_expr expression seedWF leftWF seedLeft)
    (EqUpToLevels.instL_expr expression seedWF rightWF seedRight)
  exact ⟨code.levels henv typeLeft typeLeft,
    Related.convert henv typed (code.levels henv typeSelf typeLeft) endpoints⟩

end Lean4Lean.AnchoredSemantics
