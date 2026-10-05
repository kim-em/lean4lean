import Lean4Lean.Theory.Typing.AnchoredContextCongruence
import Lean4Lean.Theory.Typing.CanonicalHeadTraceLevels

/-! Level-only transport of an individual canonical exposure. Pure trace
congruence supplies the new syntax. All typing and inhabited proof-domain
guards are constructed from the original exposure by raw level congruence;
no equality fundamental theorem or native replay callback is used. -/

namespace Lean4Lean.VEnv
open VExpr

theorem EqUpToLevels.lift' (equal : EqUpToLevels U expression expression') (ρ : Lift) :
    EqUpToLevels U (expression.lift' ρ) (expression'.lift' ρ) := by
  induction equal generalizing ρ with
  | bvar => exact .bvar
  | const left right levels => exact .const left right levels
  | elim left right levels => exact .elim left right levels
  | sort left right levels => exact .sort left right levels
  | app _ _ function argument => exact .app (function ρ) (argument ρ)
  | proj _ major => exact .proj (major ρ)
  | lam _ _ domain body => exact .lam (domain ρ) (body ρ.cons)
  | forallE _ _ domain body => exact .forallE (domain ρ) (body ρ.cons)

private theorem proofSkip_inv
    {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {ρ : Lift} {P : VExpr}
    (H : ProofInsertion env U Γ (P :: Δ) ρ.skip) :
    ∃ q, ProofInsertion env U Γ Δ ρ ∧
      env.HasType U Δ P (.sort .zero) ∧ env.HasType U Δ q P := by
  cases H with
  | skip previous hP hq => exact ⟨_, previous, hP, hq⟩

private theorem conversion_left_type
    (path : TypeConversion env U Γ A B) (right : env.IsType U Γ B) :
    env.IsType U Γ A := by
  induction path with
  | refl => exact right
  | tail _ edge ih => exact ih ⟨_, edge.hasType.1⟩

/-- A generated front consists only of inhabited proof declarations. Their
level-equivalent counterparts use the same witnesses after explicit casts. -/
theorem ProofInsertion.frontLevels
    {env : VEnv} {U : Nat} {Γ : List VExpr} {added added' : List VExpr}
    (henv : env.Ordered)
    (equal : List.Forall₂ (EqUpToLevels U) added added')
    (insertion : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length)) :
    ProofInsertion env U Γ (added' ++ Γ) (.skipN .refl added'.length) ∧
      IsDefEqCtx env U [] (added ++ Γ) (added' ++ Γ) := by
  induction equal with
  | nil =>
    simp only [List.nil_append, List.length_nil, Lift.skipN] at insertion ⊢
    exact ⟨insertion, IsDefEqCtx.refl insertion.baseWF⟩
  | @cons A A' tail tail' levels rest ih =>
    change ProofInsertion env U Γ (A :: (tail ++ Γ))
      (Lift.skip (.skipN .refl tail.length)) at insertion
    obtain ⟨_, previous, formed, witness⟩ := proofSkip_inv insertion
    obtain ⟨next, changed⟩ := ih previous
    have domainEq := formed.eqUpToLevels henv (previous.targetWF henv) levels
    have formed' := domainEq.hasType.2.defeqDFC henv changed
    have witness' := (IsDefEq.defeqDF domainEq witness).defeqDFC henv changed
    exact ⟨next.skip formed' witness', .succ changed domainEq⟩

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- The corresponding pure trace changes generated proof domains. The
literal post-context conversion is reversed at the terminal, retaining the
original final display without identifying context declarations literally. -/
theorem Exposure.levelsOfTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {expression expression' head : VExpr}
    (henv : env.Ordered)
    (exposure : Exposure env U registry Γ expression Δ ρ head)
    (levels : EqUpToLevels U expression expression')
    {added' : List VExpr} {result' : VExpr}
    (trace : CanonicalDataHead.Trace registry expression' added' result')
    (addedLevels : List.Forall₂ (EqUpToLevels U) exposure.added added')
    (resultLevels : EqUpToLevels U exposure.result result') :
    ∃ head', Nonempty (Exposure env U registry Γ expression' Δ ρ head') ∧
      EqUpToLevels U head head' := by
  obtain ⟨generated, changed⟩ := exposure.generated.frontLevels henv addedLevels
  have post := exposure.post.convertBase_exact henv changed
  let newHead := result'.lift' exposure.postMap
  have contextWF : OnCtx Δ (env.IsType U) := exposure.targetWF henv
  have headLevels : EqUpToLevels U head newHead := by
    have h := resultLevels.lift' exposure.postMap
    simpa only [exposure.result_eq] using h
  obtain ⟨u, headTyped⟩ := exposure.headType
  have headEq := headTyped.eqUpToLevels henv contextWF headLevels
  obtain ⟨_, sourceTyped⟩ := conversion_left_type exposure.sound ⟨u, headTyped⟩
  have sourceEq := sourceTyped.eqUpToLevels
    henv contextWF (levels.lift' ρ)
  refine ⟨newHead, ⟨{
    added := added'
    result := result'
    postMap := exposure.postMap
    trace := trace
    generated := generated
    postContext := _
    post := post.1
    terminal := (ContextChain.single (post.2.symm henv)).trans exposure.terminal
    map_eq := ?_
    result_eq := rfl
    sound := (TypeConversion.single sourceEq.symm).trans
      (exposure.sound.trans (.single headEq))
    headType := ⟨u, headEq.hasType.2⟩ }⟩, headLevels⟩
  have lengthOf : ∀ {as bs : List VExpr}, List.Forall₂ (EqUpToLevels U) as bs →
      as.length = bs.length := by
    intro as bs equal
    induction equal with
    | nil => rfl
    | cons _ _ ih => exact congrArg Nat.succ ih
  have lengths := lengthOf addedLevels
  simpa only [← lengths] using exposure.map_eq

/-- Closed level-only exposure transport for the actual canonical machine. -/
theorem Exposure.levels
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {expression expression' head : VExpr}
    (henv : env.Ordered)
    (exposure : Exposure env U registry Γ expression Δ ρ head)
    (levels : EqUpToLevels U expression expression') :
    ∃ head', Nonempty (Exposure env U registry Γ expression' Δ ρ head') ∧
      EqUpToLevels U head head' := by
  obtain ⟨added', result', trace, addedLevels, resultLevels⟩ := exposure.trace.levels levels
  exact exposure.levelsOfTrace henv levels trace addedLevels resultLevels

end Lean4Lean.AnchoredSemantics
