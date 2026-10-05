import Lean4Lean.Theory.Typing.AnchoredNativeSpineSkeleton
import Lean4Lean.Theory.Typing.AnchoredNativeRegisteredCode
import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem TypeRelated.literalPiBody_pair
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {A D C B prototypeDomain prototypeBody : VExpr} {domain : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {result : Profile n} {argument : VExpr}
    (whole : TypeRelated env U registry Γ (.forallE A C) (.forallE D B)
      (.pi prototypeDomain prototypeBody domain rows))
    (member : (key, result) ∈ rows)
    (admitted : Admitted env U registry Γ key argument argument) :
    TypeConversion env U Γ (C.inst argument) (B.inst argument) ∧
      TypeRelated env U registry Γ (C.inst argument) (B.inst argument) result := by
  have atBase := whole Γ .refl (.refl hΓ)
  simp only [lift'_refl, Profile.rename_refl] at atBase
  obtain ⟨display⟩ := atBase (.pi prototypeDomain prototypeBody domain rows)
    (List.mem_singleton_self _)
  have insertion := display.leftExposure.insertion henv
  have hTarget := display.leftExposure.targetWF henv
  have args := insertion.admitted henv admitted
  have row := display.rowBodies key result member display.context .refl (.refl hTarget)
    (argument.lift' display.map) (argument.lift' display.map) (by
      simpa only [Lift.comp, Admitted] using args)
  have leftBody := display.leftExposure.literalPi_components |>.2
  have rightBody := display.rightExposure.literalPi_components |>.2
  have leftEq : display.leftBody.inst (argument.lift' display.map) =
      (C.inst argument).lift' display.map := by
    rw [leftBody, lift'_inst_hi]
  have rightEq : display.rightBody.inst (argument.lift' display.map) =
      (B.inst argument).lift' display.map := by
    rw [rightBody, lift'_inst_hi]
  have bodyCode : TypeRelated env U registry display.context
      ((C.inst argument).lift' display.map) ((B.inst argument).lift' display.map)
      (result.rename display.map) := by
    simpa only [TypeRelated, Lift.comp, lift'_depth_zero (l := Lift.refl.cons) rfl, leftEq, rightEq] using row.2.2
  obtain ⟨support, _, _, _, domainPath, _⟩ := display.rowDomains key result member
  have argumentTyped : env.HasType U display.context (argument.lift' display.map) display.leftDomain :=
    domainPath.cast args.2.1
  obtain ⟨level, formedDomain⟩ := display.leftDomainType
  have substitution : Ctx.SubstEq env U display.context
      (Subst.id.cons (argument.lift' display.map))
      (Subst.id.cons (argument.lift' display.map)) (display.leftDomain :: display.context) := by
    refine .cons (Ctx.SubstEq.id henv hTarget) formedDomain ?_
    simpa only [HasType, Subst.cons_tail, Subst.head, Subst.cons, subst_id] using argumentTyped
  have bodyPath := display.bodies.substTarget henv hTarget substitution
  have renamedPath : TypeConversion env U display.context
      ((C.inst argument).lift' display.map) ((B.inst argument).lift' display.map) := by
    simpa only [← inst_eq, leftEq, rightEq] using bodyPath
  exact ⟨insertion.pathBack henv renamedPath, insertion.codeBack henv hscoped bodyCode⟩


end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
set_option backward.isDefEq.respectTransparency false

namespace PiRowCertificate
variable (row : PiRowCertificate env U registry target locals σ available A B (key : Key n) result)

def seedNeeds (extra : List Need) : List Need :=
  (row.bodyFootprint.localNeeds ++ extra) ++
    (row.bodyFootprint.localNeeds ++ extra).flatMap Need.singletons

theorem seedCoverage (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    ∀ need ∈ row.seedNeeds extra, need.rank ≤ n ∧
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
  have original : ∀ need ∈ row.bodyFootprint.localNeeds ++ extra,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨bound, included⟩ := row.pack.localNeeds need member
      exact ⟨bound, fun atom h => row.covered atom (included atom h)⟩
    · exact ⟨extraBound need member, extraCovered need member⟩
  intro need member
  rcases List.mem_append.mp member with member | member
  · exact original need member
  · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, atomMember, rfl⟩ := List.mem_map.mp selected
    obtain ⟨bound, included⟩ := original old oldMember
    refine ⟨bound, ?_⟩
    intro high member
    apply included high
    simp only [Need.atGrade, dif_pos bound] at member ⊢
    exact raiseProfile_subset bound
      (fun a h => by cases List.mem_singleton.mp h; exact atomMember) high member

theorem seedClosed (extra : List Need) (closed : available.AtomClosed) :
    (Valuation.push (row.seedNeeds extra) available).AtomClosed :=
  Valuation.push_atomized_closed closed _

theorem seedBodyAvailable (extra : List Need) :
    row.bodyFootprint.Available (Valuation.push (row.seedNeeds extra) available) := by
  have original := row.pack.available row.outsideAvailable
  intro index need member
  cases index with
  | zero => exact List.mem_append_left _ (List.mem_append_left _ (original 0 need member))
  | succ index => exact original (index + 1) need member

theorem pushSeed
    {sourceEnv : VEnv} (henv : env.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ env) {source : List VExpr} {level : VLevel}
    (originalDomain : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) ∧
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons key.anchor) (Valuation.push (row.seedNeeds extra) available) := by
  obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    (originalDomain.2 target locals σ σ available closed hTarget substitutions fits).1
    row.domainAvailable
  have admitted := row.alignment.admission henv row.anchor
  obtain ⟨_, anchorTyped, _, _, _, _, anchorRelated, _⟩ := admitted
  have related := Related.retag henv row.inputTyped domain.related anchorRelated
  have coverage := row.seedCoverage extra extraBound extraCovered
  exact ⟨.cons substitutions (originalDomain.1.defeq.mono hle) anchorTyped,
    fits.pushDiagonal henv hTarget row.domain row.domainAvailable row.inputTyped related
      (row.seedNeeds extra) (fun need hm => (coverage need hm).1)
      (fun need hm => (coverage need hm).2)⟩
end PiRowCertificate

private theorem mem_externalArguments {index : Nat} {need : Need} {required : Footprint} :
    (index, need) ∈ externalArguments required ↔ (index + 1, need) ∈ required := by
  induction required with
  | nil => simp [externalArguments]
  | cons entry rest ih =>
    obtain ⟨i, original⟩ := entry
    cases i <;> simp [externalArguments, ih]

private theorem lower_raised {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    lowerProfile n bound (raiseProfile N bound profile) = profile := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simp only [raiseProfile_self, lowerProfile_self]
    · have low : n ≤ N := by omega
      rw [lowerProfile_step low, raiseProfile_step low, Profile.down_pad]
      exact ih low

/-- Registered-prefix fits cover the full computational seed footprint as well
as its recovered source type code. The binary code retains all original spine
conversions to the actual natural assigned result. -/
structure NativeSeededRegisteredPrefix (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {data : NativeRecursorData} {levels : List VLevel} (signature : NativeConstantSignature data levels)
    (arguments : List VExpr) (assigned : VExpr) (support : Profile n) (required : Footprint)
    extends NativeRegisteredCodePrefix env U registry target locals σ available signature arguments support where
  seedAvailable : required.Available valuation
  related : TypeRelated env U registry target
    ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst
      (nativeCaptureSubst (arguments.map (·.subst σ)))) (assigned.subst σ) support

/-- Walk the actual seeded original application spine, including every type
conversion. Seed demands are included before each registered domain is queried. -/
theorem NativeSeededSpineCertificate.registered
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel} {signature : NativeConstantSignature data levels}
    (registered : NativeRecursorRegistered env data) (typeClosed : signature.type.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry [] (signature.type.instL levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] (signature.type.instL levels))
    {expression assigned : VExpr} {profile : Profile n} {footprint required : Footprint}
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      data.name levels expression assigned profile footprint)
    (coverage : NativeSpineSeedCoverage spine.seeds required)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    Nonempty (NativeSeededRegisteredPrefix env U registry target locals σ available signature
      expression.getAppFnArgs.2 assigned profile required) := by
  induction spine generalizing required with
  | @constant n profile footprint info lookup originalFormation certificate resources =>
    cases coverage
    have typeEq : info.type = signature.type := congrArg VConstant.type (Option.some.inj
      ((hle.constants lookup).symm.trans (registered.recursorType signature.typeOrigin)))
    have empty : footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      rintro ⟨index, need⟩ member
      have scope : (info.type.instL levels).Closed := by rw [typeEq]; exact typeClosed.instL
      have impossible := certificate.scoped scope index need member
      omega
    subst footprint
    have actual : CodeCert env U registry target [] (nativeCaptureSubst [])
        (signature.type.instL levels) profile [] := by
      rw [typeEq] at certificate
      exact certificate.closedSource typeClosed.instL [] (nativeCaptureSubst [])
    have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
    obtain ⟨interpreted⟩ := actual.transfer_graded henv hscoped hTarget emptyClosed
      (formation.2 target [] (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => [])
        emptyClosed hTarget .nil .nil).1 (fun _ _ h => nomatch h)
    refine ⟨{
      valuation := fun _ => []
      closed := emptyClosed
      substitutions := .nil
      fits := .nil
      footprint := []
      certificate := ?_
      resources := fun _ _ h => nomatch h
      observed := NativeObservedValuation.empty
      seedAvailable := fun _ _ h => nomatch h
      related := ?_ }⟩
    · simpa only [getAppFnArgs_const, List.length_nil, List.drop_zero, List.range_zero,
        List.map_nil, ← telescope_eq signature.telescope] using actual
    · simpa only [getAppFnArgs_const, List.length_nil, List.drop_zero,
        ← telescope_eq signature.telescope, typeEq, typeClosed.instL.subst_eq Subst.Fixes.zero] using interpreted.related
  | @application A B a n result before f frame function ih =>
    cases coverage with
    | app previousCoverage seedBound seedCovered =>
      have beforeBound : f.getAppFnArgs.2.length < signature.domains.length := by
        simp only [getAppFnArgs_app, List.length_append, List.length_singleton] at bound
        omega
      obtain ⟨previous⟩ := ih previousCoverage (by omega)
      let args := f.getAppFnArgs.2
      have origin : signature.domains[args.length]? = some signature.domains[args.length] :=
        List.getElem?_eq_getElem beforeBound
      have literal := signature.prefixResidual_cons origin
      have tree := (signature.prefixPayload ⟨level, formation⟩ header args.length).1.2
      have certificate := previous.certificate
      rw [literal] at tree certificate
      obtain ⟨domainLevel, rawDomain, originalDomain⟩ := tree.domain.1
      obtain ⟨bodyLevel, rawBody, originalBody⟩ := tree.codomain.1
      have origins := certificate.piOrigins henv hscoped hTarget previous.closed
        (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) previous.substitutions previous.fits
        originalDomain originalBody previous.resources
      have resultBound := Nat.le_trans (Nat.le_max_left n frame.seed.rank) frame.collected.bound
      have raisedSeed := Nat.le_trans (Nat.le_max_right n frame.seed.rank) frame.collected.bound
      obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key
        (raiseProfile frame.collected.rank resultBound result) (List.mem_singleton_self _)
      have extraBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.collected.rank := by
        intro need member
        exact Nat.le_trans (seedBound need (mem_argumentNeeds.mp member)) raisedSeed
      have extraCovered : ∀ need ∈ argumentNeeds required 0,
          ∀ atom ∈ (need.atGrade frame.collected.rank).atoms, atom ∈ frame.key.input.atoms := by
        intro need member atom ha
        rw [need.atGrade_raise raisedSeed (seedBound need (mem_argumentNeeds.mp member))] at ha
        exact frame.seedCovered atom (raiseProfile_subset raisedSeed
          (seedCovered need (mem_argumentNeeds.mp member)) atom ha)
      obtain ⟨raw, localFits⟩ := row.pushSeed henv hscoped hle ⟨rawDomain, originalDomain⟩
        previous.closed hTarget previous.substitutions previous.fits
        (argumentNeeds required 0) extraBound extraCovered
      have keyCoverage := row.seedCoverage (argumentNeeds required 0) extraBound extraCovered
      have localObserved := previous.observed.push closed frame.argumentObservation frame.argumentResources
        (fun need member => (keyCoverage need member).1) (fun need member => (keyCoverage need member).2)
      have contextEq := signature.prefixContext_cons origin
      have localsEq : List.range (args ++ [a]).length = Locals.push (List.range args.length) := by
        simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
      have lengthEq : (args ++ [a]).length = args.length + 1 := by simp
      have realized : nativeCaptureSubst ((args ++ [a]).map (·.subst σ)) =
          (nativeCaptureSubst (args.map (·.subst σ))).cons frame.key.anchor := by
        rw [List.map_append, List.map_singleton, nativeCaptureSubst_append]
        rfl
      have pair := previous.related
      rw [literal] at pair
      change TypeRelated env U registry target
        (.forallE ((signature.domains[args.length]).subst (nativeCaptureSubst (args.map (·.subst σ))))
          ((wrapForalls (signature.domains.drop (args.length + 1)) signature.result).subst
            (nativeCaptureSubst (args.map (·.subst σ))).lift))
        (.forallE (A.subst σ) (B.subst σ.lift)) frame.profile at pair
      have bodies := pair.literalPiBody_pair henv hscoped hTarget
        (List.mem_singleton_self _) frame.guard.anchor
      have lowered := TypeRelated.lower henv resultBound bodies.2
      rw [lower_raised] at lowered
      simp only [getAppFnArgs_app]
      change Nonempty (NativeSeededRegisteredPrefix env U registry target locals σ available
        signature (args ++ [a]) (B.inst a) result required)
      refine ⟨{
        valuation := Valuation.push (row.seedNeeds (argumentNeeds required 0)) previous.valuation
        closed := row.seedClosed _ previous.closed
        substitutions := ?_
        fits := ?_
        footprint := row.bodyFootprint
        certificate := ?_
        resources := row.seedBodyAvailable _
        observed := localObserved
        seedAvailable := ?_
        related := ?_ }⟩
      · simpa only [getAppFnArgs_app, lengthEq, contextEq, realized] using raw
      · simpa only [getAppFnArgs_app, lengthEq, contextEq, realized, localsEq,
          List.range_succ_eq_map, Locals.push] using localFits
      · simpa only [getAppFnArgs_app, lengthEq, realized, localsEq,
          List.range_succ_eq_map, Locals.push] using row.body.lowerRaised resultBound
      · intro index need member
        cases index with
        | zero => exact List.mem_append_left _ (List.mem_append_right _ (mem_argumentNeeds.mpr member))
        | succ index => exact previous.seedAvailable index need (mem_externalArguments.mpr member)
      · simpa only [getAppFnArgs_app, lengthEq, realized, inst_lift_cons,
          subst_inst, SeededApplicationCodeInput.key] using lowered
  | conversion edge certificate transfer term ih =>
    obtain ⟨previous⟩ := ih coverage bound
    exact ⟨{ previous with related := (previous.related.trans henv
      (transfer.related.symm henv certificate.formed.wf_value)) }⟩


/-- End-to-end registered valuation from genuine argument-ledger packets.
Every routed seed is merged into its original argument observation before the
spine is interpreted, including through converted function types. -/
theorem HasTypeStrong.seededRegistered
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {levels : List VLevel} {signature : NativeConstantSignature data levels}
    (registered : NativeRecursorRegistered env data) (typeClosed : signature.type.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry [] (signature.type.instL levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] (signature.type.instL levels))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const data.name levels)
    {profile : Profile n} {footprint required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available expression.getAppFnArgs.2 required)
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    Nonempty (NativeSeededRegisteredPrefix env U registry target locals σ available signature
      expression.getAppFnArgs.2 assigned profile required) := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head n
  obtain ⟨spine, same⟩ := HasTypeStrong.seededSpineCertificate henv hscoped hle earlier
    closed hTarget substitutions fits original head seeds certificate resources
  apply spine.registered henv hscoped hle closed hTarget registered typeClosed formation header _ bound
  rw [same]
  exact coverage

end Lean4Lean.AnchoredSource.Adapted
