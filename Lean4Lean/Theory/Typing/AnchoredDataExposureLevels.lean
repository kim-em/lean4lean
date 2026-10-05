import Lean4Lean.Theory.Typing.AnchoredExposureLevels
import Lean4Lean.Theory.Typing.CanonicalDataHeadLevels
import Lean4Lean.Theory.Typing.AnchoredDataExposureTransport
import Batteries.Tactic.OpenPrivate

/-! Universe congruence of data displays preserves the literal declaration
header and the concrete generated proof world. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature
open private related_spine from Lean4Lean.Theory.Typing.CanonicalDataHeadLevels
set_option backward.isDefEq.respectTransparency false

theorem ConstructorExposure.levels
    (henv : env.Ordered)
    (exposure : ConstructorExposure env U registry Γ expression type Δ ρ head)
    (levels : EqUpToLevels U expression expression') :
    ∃ head', Nonempty (ConstructorExposure env U registry Γ expression' type Δ ρ head') ∧
      EqUpToLevels U head head' := by
  obtain ⟨added', result', trace, addedLevels, resultLevels⟩ := exposure.trace.levels levels
  obtain ⟨generated, changed⟩ := exposure.generated.frontLevels henv addedLevels
  have post := exposure.post.convertBase_exact henv changed
  let newHead := result'.lift' exposure.postMap
  have contextWF := exposure.terminal.targetWF henv (exposure.post.targetWF henv)
  have headLevels : EqUpToLevels U head newHead := by
    simpa only [exposure.result_eq] using resultLevels.lift' exposure.postMap
  have headEq := exposure.sound.hasType.2.eqUpToLevels henv contextWF headLevels
  have sourceEq := exposure.sound.hasType.1.eqUpToLevels henv contextWF (levels.lift' ρ)
  refine ⟨newHead, ⟨{
    added := added', result := result', postMap := exposure.postMap
    trace := trace, generated := generated, postContext := _, post := post.1
    terminal := (ContextChain.single (post.2.symm henv)).trans exposure.terminal
    map_eq := ?_, result_eq := rfl
    sound := sourceEq.symm.trans (exposure.sound.trans headEq) }⟩, headLevels⟩
  simpa only [← Lean4Lean.List.Forall₂.length_eq addedLevels] using exposure.map_eq

theorem dataHead_levels
    (equal : EqUpToLevels U (mkApps (.const name levels) arguments) head') :
    ∃ levels' arguments', head' = mkApps (.const name levels') arguments' ∧
      (∀ l ∈ levels, l.WF U) ∧ (∀ l ∈ levels', l.WF U) ∧
      List.Forall₂ (· ≈ ·) levels levels' ∧
      List.Forall₂ (EqUpToLevels U) arguments arguments' := by
  obtain ⟨headEq, argumentsEq⟩ := related_spine equal
  rw [VExpr.getAppFnArgs_mkApps_const] at headEq argumentsEq
  cases spine : head'.getAppFnArgs with
  | mk fn args =>
    simp only [spine] at headEq argumentsEq
    cases headEq with
    | const leftWF rightWF levelsEq =>
      refine ⟨_, args, ?_, leftWF, rightWF, levelsEq, argumentsEq⟩
      have rebuild := VExpr.mkApps_getAppFnArgs_eq head'
      change mkApps head'.getAppFnArgs.1 head'.getAppFnArgs.2 = head' at rebuild
      simpa only [spine] using rebuild.symm

theorem dataTerminal_levels (equal : EqUpToLevels U head head')
    (terminal : CanonicalDataHead.step registry head = none) :
    CanonicalDataHead.step registry head' = none := by
  have relation := CanonicalDataHead.step_levels_relation (registry := registry) equal
  rw [terminal] at relation
  cases stopped : CanonicalDataHead.step registry head' with
  | none => rfl
  | some out => rw [stopped] at relation; cases relation

private theorem telescope_levels
    (equal : EqUpToLevels U (wrapForalls domains body) type') :
    ∃ domains' body', type' = wrapForalls domains' body' ∧
      List.Forall₂ (EqUpToLevels U) domains domains' ∧ EqUpToLevels U body body' := by
  induction domains generalizing type' with
  | nil => exact ⟨[], type', rfl, .nil, equal⟩
  | cons domain domains ih =>
    cases equal with
    | forallE domainEq bodyEq =>
      obtain ⟨domains', body', rfl, domainsEq, bodyEq⟩ := ih bodyEq
      exact ⟨_ :: domains', body', rfl, .cons domainEq domainsEq, bodyEq⟩

theorem ConstructorResultHeader.levels
    {levels levels' : List VLevel} {arguments arguments' : List VExpr}
    (header : ConstructorResultHeader env constructor family levels arguments)
    (leftWF : ∀ l ∈ levels, l.WF U) (rightWF : ∀ l ∈ levels', l.WF U)
    (levelsEq : List.Forall₂ (· ≈ ·) levels levels')
    (argumentsEq : List.Forall₂ (EqUpToLevels U) arguments arguments') :
    ∃ changed : ConstructorResultHeader env constructor family levels' arguments',
      EqUpToLevels U header.result changed.result := by
  have typeEq := EqUpToLevels.instL_expr header.info.type leftWF rightWF levelsEq
  rw [header.telescope] at typeEq
  obtain ⟨domains', body', telescope, domainsEq, bodyEq⟩ := telescope_levels typeEq
  obtain ⟨familyLevels', familyArguments', rfl, _, _, _, _⟩ := dataHead_levels bodyEq
  refine ⟨{
    info := header.info, lookup := header.lookup, domains := domains'
    familyLevels := familyLevels', familyArguments := familyArguments'
    telescope := telescope, saturated := ?_ }, bodyEq.instantiateParams_args argumentsEq⟩
  rw [← Lean4Lean.List.Forall₂.length_eq domainsEq,
    ← Lean4Lean.List.Forall₂.length_eq argumentsEq, header.saturated]

end Lean4Lean.AnchoredSemantics
