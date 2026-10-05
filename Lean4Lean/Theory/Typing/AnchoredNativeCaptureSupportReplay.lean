import Lean4Lean.Theory.Typing.NativeCaptureRoles
import Lean4Lean.Theory.Typing.AnchoredNativePrefixReplay
import Lean4Lean.Theory.Typing.AnchoredNativeTelescopeFits
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Route every concrete native capture requirement into a replay. The
source formation tree is retained from the actual declared equation type;
no newly synthesized typing derivation is interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def nativeCaptureRoles {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels) (count : Nat) : List (Option Nat) :=
  (nativePrefixPlan (program.prefixArgs.length - data.indexOffset)
    (signature.domains.take data.indexOffset).reverse).roles ++
  (program.instructions.take count).map (fun instruction => match instruction with
    | .index _ slot => some (program.prefixArgs.length - 1 - (data.indexOffset + slot))
    | .proof _ => none)

structure NativeCaptureReplayResult
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses : List VExpr) (argumentAvailable : Valuation) (count : Nat) (required : Footprint) where
  available : Valuation
  plan : CapturePlan ((program.equationBody.domains.take (data.indexOffset + count)).map
    (·.instL program.levels)).reverse
  replay : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
    (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) argumentAvailable
    _ plan (nativeCaptureSubst (witnesses.take (data.indexOffset + count)))
    (List.range (data.indexOffset + count)) available
  roles : plan.roles = nativeCaptureRoles program signature count
  closed : available.AtomClosed
  resources : required.Available available

private theorem templateDomains {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (templates : NativeIndexTemplates program) : templates.inputDomains = signature.domains := by
  have typeEq := Option.some.inj (templates.registeredType.symm.trans signature.typeOrigin)
  have same := templates.telescope
  rw [typeEq, signature.telescope] at same
  exact (Prod.mk.inj (Option.some.inj same)).1.symm

private theorem sourceLift_available
    (resources : (Footprint.sourceLift (.skipN .refl count) required).Available available) :
    required.Available (fun index => available (index + count)) := by
  intro index need member
  apply resources (index + count) need
  exact List.mem_map.mpr ⟨(index, need), member, by simp [Lift.liftVar_skipN, Lift.liftVar]⟩

/-- Literal declared formation, obtained by reading the retained source Pi
payload at the instruction's original telescope position. -/
private theorem declaredFormation
    {sourceEnv : VEnv} {U : Nat} {domains : List VExpr} {result : VExpr}
    (root : ∃ u, sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort u))
    (tree : SourcePiFormation (fun Γ A T => sourceEnv.IsDefEqStrong U Γ A A T)
      [] (wrapForalls domains result))
    (origin : domains[position]? = some domain) :
    ∃ u, sourceEnv.IsDefEqStrong U (domains.take position).reverse domain domain (.sort u) := by
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp origin
  simpa only [List.append_nil, equal] using (tree.telescope root).1 position bound |>.1

/-- All certificates accumulated by capture routing remain represented in
the fitting valuation, including those used only for later field domains. -/
theorem NativeCaptureSupport.toReplay
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    {witnesses : List VExpr}
    (prefixEq : witnesses.take data.indexOffset = program.prefixArgs.take data.indexOffset)
    (root : ∃ u, sourceEnv.IsDefEqStrong U []
      (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) result)
      (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) result) (.sort u))
    (formation : SourcePiFormation (fun Γ A T => sourceEnv.IsDefEqStrong U Γ A A T) []
      (wrapForalls (program.equationBody.domains.map (·.instL program.levels)) result))
    {argumentAvailable : Valuation} (closed : argumentAvailable.AtomClosed)
    {count : Nat} {required native : Footprint}
    (support : NativeCaptureSupport env U registry target program witnesses count required native)
    (resources : native.Available argumentAvailable) :
    Nonempty (NativeCaptureReplayResult sourceEnv env U registry target program signature
      witnesses argumentAvailable count required) := by
  have argumentLength := (saturatedProgram_spec selected).2.2.1
  have domainLength := takeForalls_length signature.telescope
  have sameLength : program.prefixArgs.length = signature.domains.length := argumentLength.trans domainLength.symm
  have offsetBound : data.indexOffset ≤ signature.domains.length := by
    rw [domainLength, majorOffset]
    omega
  have common := saturatedProgram_commonPrefix selected signature.typeOrigin signature.telescope
  induction support with
  | «prefix» required =>
    have replay := NativeSupportedReplay.ofNativePrefix (sourceEnv := sourceEnv) (env := env)
      (U := U) (registry := registry) (target := target) (locals := List.range program.prefixArgs.length)
      program.prefixArgs argumentAvailable sameLength data.indexOffset offsetBound
    have captured := nativeCaptureSubst_prefix program.prefixArgs data.indexOffset (by omega)
    have countEq : (signature.domains.take data.indexOffset).reverse.length = data.indexOffset := by
      simp [Nat.min_eq_left offsetBound]
    rw [← sameLength, captured, ← prefixEq, countEq] at replay
    have ctxEq : ((program.equationBody.domains.take data.indexOffset).map
        (·.instL program.levels)).reverse = (signature.domains.take data.indexOffset).reverse := by
      rw [List.map_take, common]
    have paired : Nonempty (Σ plan : CapturePlan ((program.equationBody.domains.take data.indexOffset).map
        (·.instL program.levels)).reverse,
        { proof : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
          (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) argumentAvailable
          _ plan (nativeCaptureSubst (witnesses.take data.indexOffset)) (List.range data.indexOffset)
          (fun index => argumentAvailable (index + (program.prefixArgs.length - data.indexOffset))) // plan.roles = nativeCaptureRoles program signature (0) }) := by
      rw [ctxEq]
      exact ⟨⟨_, replay, by simp only [nativeCaptureRoles, List.take_zero, List.map_nil, List.append_nil]⟩⟩
    obtain ⟨⟨plan, replay, roles⟩⟩ := paired
    refine ⟨⟨_, plan, replay, roles, ?_, ?_⟩⟩
    · exact fun i need member selected hs => closed _ need member selected hs
    · exact sourceLift_available resources
  | @index n templates naturalAvailable captureAvailable input packed required outside previousNative value
      guard nativeValue copiedValue pack covered previous ih =>
    have previousResources : previousNative.Available argumentAvailable := fun i need hm =>
      resources i need (List.mem_append_left _ (List.mem_append_left _ hm))
    obtain ⟨before⟩ := ih previousResources
    have domainsEq := templateDomains signature templates
    have naturalOrigin := templates.naturalOrigin
    rw [domainsEq] at naturalOrigin
    obtain ⟨positionBound, domainEq⟩ := List.getElem?_eq_some_iff.mp naturalOrigin
    let position := program.prefixArgs.length - 1 - (data.indexOffset + templates.slot)
    have lookup : Lookup signature.domains.reverse position
        (templates.naturalDomain.liftN (signature.domains.length - (data.indexOffset + templates.slot))) := by
      simpa only [List.append_nil, domainEq, position, sameLength] using
        Lookup.reverse_append signature.domains [] (data.indexOffset + templates.slot) positionBound
    have needed : (⟨n, input⟩ : Need) ∈ argumentAvailable position :=
      resources position ⟨n, input⟩ (List.mem_append_right _ (List.mem_singleton_self _))
    have domainResources : guard.declaredFootprint.Available before.available := fun i need hm =>
      before.resources i need (List.mem_append_left _ hm)
    have outsideResources : outside.Available before.available := fun i need hm =>
      before.resources i need (List.mem_append_right _ hm)
    obtain ⟨level, typedDomain⟩ := declaredFormation root formation templates.declaredOrigin_exact
    have naturalEq : (templates.naturalDomain.liftN
        (signature.domains.length - (data.indexOffset + templates.slot))).subst
        (nativeCaptureSubst program.prefixArgs) = templates.naturalDomain.subst
        (nativeCaptureSubst (program.prefixArgs.take (data.indexOffset + templates.slot))) := by
      rw [← lift'_consN_skipN (k := 0), subst_lift']
      simp only [Lift.consN]
      rw [← sameLength, nativeCaptureSubst_prefix _ _ (by omega)]
    have capturedValue : nativeCaptureSubst program.prefixArgs position = value := by
      obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp nativeValue
      rw [nativeCaptureSubst, dif_pos (by dsimp [position]; omega)]
      have indexEq : program.prefixArgs.length - 1 - position = data.indexOffset + templates.slot := by
        dsimp [position]
        omega
      simpa only [indexEq] using eq
    have step := NativeSupportedReplay.index before.replay
      (by simpa only [List.map_take, NativeIndexTemplates.declaredContext] using typedDomain)
      lookup needed guard.declaredCertificate domainResources guard.declaredTyped
      (by rw [naturalEq]; exact guard.alignment) guard.declaredCode
      before.closed (required.localNeeds ++ required.localNeeds.flatMap Need.singletons)
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
    have contextEq : ((program.equationBody.domains.take (data.indexOffset + (templates.field + 1))).map
        (·.instL program.levels)).reverse = templates.declaredDomain ::
        ((program.equationBody.domains.take (data.indexOffset + templates.field)).map
          (·.instL program.levels)).reverse := by
      rw [← Nat.add_assoc, List.map_take, List.take_add_one, templates.declaredOrigin_exact]
      simp only [Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_take]
    have capturesEq : nativeCaptureSubst (witnesses.take (data.indexOffset + (templates.field + 1))) =
        (nativeCaptureSubst (witnesses.take (data.indexOffset + templates.field))).cons value := by
      rw [← Nat.add_assoc, List.take_add_one, copiedValue]
      exact nativeCaptureSubst_append _ _
    have localsEq : List.range (data.indexOffset + (templates.field + 1)) =
        Locals.push (List.range (data.indexOffset + templates.field)) := by
      simp only [← Nat.add_assoc, List.range_succ_eq_map, Locals.push]
    have paired : Nonempty (Σ plan : CapturePlan ((program.equationBody.domains.take
        (data.indexOffset + (templates.field + 1))).map (·.instL program.levels)).reverse,
        { proof : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
          (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) argumentAvailable
          _ plan (nativeCaptureSubst (witnesses.take (data.indexOffset + (templates.field + 1))))
          (List.range (data.indexOffset + (templates.field + 1)))
          (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) before.available) // plan.roles = nativeCaptureRoles program signature (templates.field + 1) }) := by
      rw [contextEq, capturesEq, localsEq]
      refine ⟨⟨_, ⟨by simpa only [capturedValue] using step, ?_⟩⟩⟩
      rw [CapturePlan.roles, before.roles]
      simp only [nativeCaptureRoles, List.take_add_one, templates.declaredOrigin, Option.toList_some,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc, position]
    obtain ⟨⟨plan, replay, roles⟩⟩ := paired
    exact ⟨⟨_, plan, replay, roles, Valuation.push_atomized_closed before.closed _,
      pack.available_atomized_localNeeds outsideResources⟩⟩
  | @proof n field domain witness required outside native instruction captured sourceProof domainProof inhabitant
      pack previous ih =>
    have beforeResources : native.Available argumentAvailable := resources
    obtain ⟨before⟩ := ih beforeResources
    have step := NativeSupportedReplay.proof before.replay sourceProof inhabitant
      (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) n
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => by cases (pack.atomized_localNeeds need hm).2 atom ha)
    have instructionDomains := (saturatedProgram_spec selected).2.2.2.2.2.2.2.2.2.2.1
    have domains := fieldInstructions_domains program.source
      ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
    rw [← instructionDomains] at domains
    have origin := congrArg (fun ds => ds[field]?) domains
    rw [List.getElem?_map, instruction] at origin
    have domainOrigin : (program.equationBody.domains.map (·.instL program.levels))[data.indexOffset + field]? = some domain := by
      simpa only [Option.map_some, CaptureInstruction.domain, List.map_drop, List.getElem?_drop] using origin.symm
    have contextEq : ((program.equationBody.domains.take (data.indexOffset + (field + 1))).map
        (·.instL program.levels)).reverse = domain ::
        ((program.equationBody.domains.take (data.indexOffset + field)).map (·.instL program.levels)).reverse := by
      rw [← Nat.add_assoc, List.map_take, List.take_add_one, domainOrigin]
      simp only [Option.toList_some, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_take]
    have capturesEq : nativeCaptureSubst (witnesses.take (data.indexOffset + (field + 1))) =
        (nativeCaptureSubst (witnesses.take (data.indexOffset + field))).cons witness := by
      rw [← Nat.add_assoc, List.take_add_one, captured]
      exact nativeCaptureSubst_append _ _
    have localsEq : List.range (data.indexOffset + (field + 1)) =
        Locals.push (List.range (data.indexOffset + field)) := by
      simp only [← Nat.add_assoc, List.range_succ_eq_map, Locals.push]
    have paired : Nonempty (Σ plan : CapturePlan ((program.equationBody.domains.take
        (data.indexOffset + (field + 1))).map (·.instL program.levels)).reverse,
        { proof : NativeSupportedReplay sourceEnv env U registry target signature.domains.reverse
          (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs) argumentAvailable
          _ plan (nativeCaptureSubst (witnesses.take (data.indexOffset + (field + 1))))
          (List.range (data.indexOffset + (field + 1)))
          (Valuation.push (required.localNeeds ++ required.localNeeds.flatMap Need.singletons) before.available) // plan.roles = nativeCaptureRoles program signature (field + 1) }) := by
      rw [contextEq, capturesEq, localsEq]
      refine ⟨⟨_, ⟨step, ?_⟩⟩⟩
      rw [CapturePlan.roles, before.roles]
      simp only [nativeCaptureRoles, List.take_add_one, instruction, Option.toList_some,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    obtain ⟨⟨plan, replay, roles⟩⟩ := paired
    exact ⟨⟨_, plan, replay, roles, Valuation.push_atomized_closed before.closed _,
      pack.available_atomized_localNeeds before.resources⟩⟩

end Lean4Lean.AnchoredSource.Adapted
