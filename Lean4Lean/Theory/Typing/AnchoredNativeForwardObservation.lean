import Lean4Lean.Theory.Typing.AnchoredNativeConsumeObservation
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureSupply
import Lean4Lean.Theory.Typing.AnchoredNativeCaptureAgreementLevels
import Lean4Lean.Theory.Typing.AnchoredNativeOriginalObservation
import Lean4Lean.Theory.Typing.AnchoredNativeOriginalOpening
import Lean4Lean.Theory.Typing.AnchoredNativePlanBridge

/-! Forward source transfer for an original singleton equation. Actual
native observers are consumed to their stored RHS, replayed with the caller's
witnesses, and reified from the original finite argument observations. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature
open NativeRecursorData hiding target levels
open AnchoredSource (Footprint Valuation BinderPack Need raiseAtom raiseProfile lowerProfile raiseProfile_singleton raiseProfile_trans)
open AnchoredSource.Adapted AnchoredProfiles AnchoredSemantics
open private related_spine from Lean4Lean.Theory.Typing.CanonicalHeadTraceLevels
open private scope_wrapLams from Lean4Lean.Theory.Inductive.SaturatedNativeRenaming
set_option backward.isDefEq.respectTransparency false

private theorem contextLevels (domains : List VExpr)
    (firstWF : ∀ level ∈ first, level.WF U) (secondWF : ∀ level ∈ second, level.WF U)
    (equal : List.Forall₂ (· ≈ ·) first second) :
    List.Forall₂ (EqUpToLevels U) (domains.map (·.instL first)).reverse
      (domains.map (·.instL second)).reverse := by
  suffices ∀ old new, List.Forall₂ (EqUpToLevels U) old new →
    List.Forall₂ (EqUpToLevels U) ((domains.map (·.instL first)).reverse ++ old)
      ((domains.map (·.instL second)).reverse ++ new) from by
      simpa only [List.append_nil] using this [] [] .nil
  induction domains with
  | nil => intro old new prior; exact prior
  | cons A rest ih =>
    intro old new prior
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (A.instL first :: old) (A.instL second :: new)
        (.cons (.instL_expr A firstWF secondWF equal) prior)

private theorem consumedTerminal
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (body.domains.map (·.instL levels)).reverse)
    (length : (body.lhs.instL levels).getAppFnArgs.2.length = data.majorOffset + 1)
    {requested : Atom n}
    (consumed : NativePlanConsumption env U registry target locals σ available data levels
      (body.lhs.instL levels).getAppFnArgs.2 requested) :
    Nonempty (GradedResult env U registry target locals σ available
      (body.rhs.instL levels) (.singleton requested)) := by
  rcases consumed with ⟨rank, bound, seedLevels, seedWF, equivalent, signature, typeClosed,
    anchors, anchorLength, output, footprint, plan, adapter, valuation, valuationClosed,
    rawArguments, argumentFits, resources, observed⟩
  cases plan with
  | binder domainOrigin domainCode guard child pack covered =>
    have impossible := (List.getElem?_eq_some_iff.mp domainOrigin).1
    rw [anchorLength, length, takeForalls_length signature.telescope] at impossible
    omega
  | terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq witnesses
      witnessLength witnessPrefix argumentAlignment literal bodyObservation captures =>
    have spec := saturatedProgram_spec selected
    have seedEq := spec.1
    subst seedLevels
    have programEq : program.equation = rule := Option.some.inj
      (spec.2.2.2.2.2.2.2.2.1.symm.trans
        (NativeRecursorData.singletonEquation_of_equation singleton.2.1 owner equation))
    have bodyEq : program.equationBody = body := by
      have parse := spec.2.2.2.2.2.2.2.2.2.1
      rw [programEq, extracted] at parse
      exact (Option.some.inj parse).symm
    subst body
    have selectedSelf : data.saturatedProgram program.levels
        (program.prefixArgs ++ program.trailing) = some program := by
      simpa only [prefixEq, noTrailing, List.append_nil] using selected
    have registered := origin.registered
    have hsource := origin.stage.typing.recursorsWF.ordered
    have hle := origin.stage.typing.recursors_le.trans origin.stage.installedBelow
    have original := origin.singletonStrong spec.2.2.2.2.2.2.2.2.1
    have originalLeft := original.1.instL seedWF
    have originalRight := original.2.instL seedWF
    obtain ⟨opened⟩ := NativeRecursorData.originalEquationBodies earlier selectedSelf
      originalLeft.hasType'.1 originalRight.hasType'.1
    obtain ⟨level, formation⟩ := originalRight.isType' hsource hsource.strong (by trivial)
    have sourceFormation := formation
    rw [← (CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1).2.2,
      instL_wrapForalls] at sourceFormation
    have witnessPrefix' : witnesses.take data.indexOffset = program.prefixArgs.take data.indexOffset := by
      simpa only [prefixEq] using witnessPrefix
    obtain ⟨replay⟩ := captures.toSupport.toReplay signature selectedSelf witnessPrefix'
      ⟨_, sourceFormation⟩ sourceFormation.sourcePiFormation.1 valuationClosed resources
    have captureCount := initialCaptureLength selectedSelf
    have declaredEq : ((program.equationBody.domains.take
        (data.indexOffset + program.instructions.length)).map (·.instL program.levels)).reverse =
        (program.equationBody.domains.map (·.instL program.levels)).reverse := by
      rw [← captureCount, List.take_length]
    have fullLength : (program.equationBody.lhs.instL levels).getAppFnArgs.2.length = signature.domains.length :=
      length.trans (takeForalls_length signature.telescope).symm
    have sourceLength : (program.equationBody.lhs.instL program.levels).getAppFnArgs.2.length = program.prefixArgs.length := by
      have same : (program.equationBody.lhs.instL program.levels).getAppFnArgs.2.length =
          (program.equationBody.lhs.instL levels).getAppFnArgs.2.length := by
        simp only [getAppFnArgs_instL, List.length_map]
      exact same.trans (length.trans spec.2.2.1.symm)
    obtain ⟨origins⟩ := origin.captureOrigins_of_singleton henv eliminator singleton seedWF
      (signature := signature) owner equation selectedSelf
    have originalAgreement := origins.indexAgreement selectedSelf sourceLength
      (by simp only [vars, List.length_map, List.length_reverse, List.length_range]; omega) replay Subst.id
    have sourceAgreement : replay.plan.IndexAgreement
        (nativeCaptureSubst (program.equationBody.lhs.instL program.levels).getAppFnArgs.2) Subst.id := by
      have takeVars : (vars program.equationBody.domains.length 0).take
          program.equationBody.domains.length = vars program.equationBody.domains.length 0 :=
        List.take_of_length_le (by simp [vars])
      simp only [subst_id, ← captureCount, takeVars] at originalAgreement
      have identityMap (values : List VExpr) : values.map (fun e => e) = values := by
        induction values with
        | nil => rfl
        | cons value rest ih => exact congrArg (List.cons value) ih
      rw [identityMap, identityMap] at originalAgreement
      apply originalAgreement.witnesses
      intro i hi
      have bound : i < program.equationBody.domains.length := by
        simpa only [declaredEq, List.length_reverse, List.length_map] using hi
      have atVariable := nativeCaptureSubst_variables
        program.equationBody.domains.length Subst.id i bound
      simp only [subst_id] at atVariable
      rw [identityMap] at atVariable
      exact atVariable
    have argumentLevels := (related_spine
      (EqUpToLevels.instL_expr program.equationBody.lhs seedWF levelsWF equivalent)).2
    have agreed := replay.replay.agreementLevels (by
      rw [List.length_reverse]
      exact sourceLength.trans (spec.2.2.1.trans (takeForalls_length signature.telescope).symm))
      argumentLevels sourceAgreement
    have realized := replay.replay.agreementRealized
      (by simpa only [List.length_reverse] using fullLength) agreed σ
    have backwards : List.Forall₂ (· ≈ ·) levels program.levels := by
      have symmetric : ∀ {a b : List VLevel}, List.Forall₂ (· ≈ ·) a b → List.Forall₂ (· ≈ ·) b a := by
        intro a b equal
        induction equal with
        | nil => exact .nil
        | cons h tail ih => exact .cons h.symm ih
      exact symmetric equivalent
    have identity : Subst.id.comp σ = σ := by funext i; rfl
    have rawSeed := substitutions.nativeSourceLevels henv hTarget
      (contextLevels program.equationBody.domains levelsWF seedWF backwards)
    have witnessTyped : Ctx.SubstEq env U target (Subst.id.comp σ) (Subst.id.comp σ)
        ((program.equationBody.domains.take (data.indexOffset + program.instructions.length)).map
          (·.instL program.levels)).reverse := by
      simpa only [declaredEq, identity] using rawSeed
    have rawFull : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
        (nativeCaptureSubst ((program.equationBody.lhs.instL levels).getAppFnArgs.2.map (·.subst σ)))
        signature.domains.reverse := by
      simpa only [prefixEq, fullLength, List.take_length] using rawArguments
    have fitFull : PairedFits env U registry signature.domains.reverse target
        (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
        (nativeCaptureSubst ((program.equationBody.lhs.instL levels).getAppFnArgs.2.map (·.subst σ))) valuation := by
      simpa only [prefixEq, anchorLength, fullLength, List.take_length] using argumentFits
    have rhsOriginal : origin.stage.typing.recursors.IsDefEqStrong U
        ((program.equationBody.domains.take (data.indexOffset + program.instructions.length)).map
          (·.instL program.levels)).reverse
        (program.equationBody.rhs.instL program.levels) (program.equationBody.rhs.instL program.levels)
        opened.right.natural := by
      simpa only [declaredEq, List.append_nil] using opened.right.typing.refl
    have witnessedBody := bodyObservation
    have witnessesFull : witnesses.take (data.indexOffset + program.instructions.length) = witnesses := by
      rw [← captureCount, ← witnessLength, List.take_length]
    rw [← witnessesFull] at witnessedBody
    obtain ⟨result⟩ := replay.replay.chosenSourceTerminal henv hscoped hle (fun H => (earlier H).joint)
      hTarget closed (by simpa only [List.length_reverse] using fullLength) observed rawFull fitFull
      Subst.id witnessTyped agreed (by simpa only [identity] using realized)
      replay.closed rhsOriginal (by simpa only [captureCount] using witnessedBody) replay.resources
    have rhsScope := (scope_of_extract spec.2.2.2.2.2.2.2.2.2.1 rhsClosed).2.instL
      (ls := program.levels)
    have sourceEqual := EqUpToLevels.instL_expr program.equationBody.rhs seedWF levelsWF equivalent
    have realizedEqual := sourceEqual.substScoped rhsScope (by
      simpa only [List.length_reverse, List.length_map] using
        substitutions.nativeValueLevels henv hTarget)
    have rhsTyped := (opened.right.typing.refl.defeq.mono hle).subst henv
      (by simpa only [List.append_nil] using rawSeed) hTarget
    have currentObservation := result.observation
    simp only [subst_id] at currentObservation
    obtain ⟨changed⟩ := currentObservation.levels henv hTarget sourceEqual realizedEqual ⟨_, rhsTyped⟩
    refine ⟨{
      rank := result.rank
      bound := Nat.le_trans bound result.bound
      raw := result.raw
      footprint := result.footprint
      observation := changed
      adapter := ?_
      resources := result.resources
      live := result.live }⟩
    have singletonAdapter : NormalProfileAdapter env U registry target (.singleton output)
        (raiseProfile rank bound (.singleton requested)) := by
      rw [raiseProfile_singleton]
      exact .cons (List.mem_singleton_self _) adapter (.nil _)
    simpa only [raiseProfile_trans] using result.adapter.comp
      (singletonAdapter.raise henv hscoped hTarget result.bound)

/-- Arbitrary original LHS observers transfer to the literal original RHS.
The whole program, its data agreement, proof choices, finite argument supply,
and universe packet transport are produced internally. -/
theorem forwardOpenObservation
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (body.domains.map (·.instL levels)).reverse)
    (fits : PairedFits env U registry (body.domains.map (·.instL levels)).reverse
      target locals σ σ available)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (body.lhs.instL levels) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedResult env U registry target locals σ available (body.rhs.instL levels) demand) := by
  obtain ⟨program, selected, _, _, _, prefixEq, _, head⟩ :=
    origin.initialProgram eliminator singleton.1 singleton.2.1 owner equation extracted levelLength σ
  have length : (body.lhs.instL levels).getAppFnArgs.2.length = data.majorOffset + 1 := by
    have h := (saturatedProgram_spec selected).2.2.1
    rw [prefixEq, List.length_map] at h
    exact h
  have original := origin.singletonStrong
    (NativeRecursorData.singletonEquation_of_equation singleton.2.1 owner equation)
  have lhsClosed : rule.lhs.Closed := VExpr.WF.closedN
    origin.stage.typing.recursorsWF.ordered ⟨_, original.1.defeq⟩ trivial
  have wrappedScope : (wrapLams body.domains body.lhs).Closed := by
    rw [(CaseSchema.EquationBody.extract_sound extracted).1]
    exact lhsClosed
  have scope : (body.lhs.instL levels).ClosedN (body.domains.map (·.instL levels)).reverse.length := by
    simpa only [Nat.zero_add, List.length_reverse, List.length_map] using
      (scope_wrapLams body.domains body.lhs wrappedScope).2.instL (ls := levels)
  have atomic (atom : Atom n) (member : atom ∈ demand.atoms) :
      Nonempty (GradedResult env U registry target locals σ available
        (body.rhs.instL levels) (.singleton atom)) := by
    obtain ⟨consumed⟩ := observation.consumeNative origin henv hscoped
      (fun H => (earlier H).joint) lookup notDefinition hTarget fits.forward head
      (Nat.le_of_eq length) scope resources member
    exact consumedTerminal origin henv hscoped eliminator singleton earlier owner equation
      extracted levelsWF closed hTarget substitutions length consumed
  suffices ∀ requested : List (Atom n), (∀ atom ∈ requested, atom ∈ demand.atoms) →
      Nonempty (GradedResult env U registry target locals σ available
        (body.rhs.instL levels) (Profile.mk requested)) from
    this demand.atoms (fun _ h => h)
  intro requested
  induction requested with
  | nil =>
    intro _
    exact ⟨.exact .empty (fun _ _ hm => nomatch hm) .empty⟩
  | cons atom rest ih =>
    intro included
    obtain ⟨first⟩ := atomic atom (included atom List.mem_cons_self)
    obtain ⟨remaining⟩ := ih (fun a member => included a (List.mem_cons_of_mem _ member))
    exact ⟨first.union henv hscoped hTarget remaining⟩

end Lean4Lean.VEnv.NativeDeclarationOrigin
