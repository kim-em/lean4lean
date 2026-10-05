import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableValue
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSchedule
import Lean4Lean.Theory.Typing.AnchoredApplication

/-! The native-row step of original rich application F. The source result
certificate is returned by the exact captured-codomain/result comparison,
not manufactured by relabelling the body or by assuming whole-app semantics.
Both recursive calls are fixed original children of this application. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def RichGradedResult.restrict
    (result : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (included : ∀ atom ∈ (requested : Profile n).atoms, atom ∈ input.atoms) :
    RichGradedResult sourceEnv env U registry target node locals σ available requested where
  rank := result.rank
  bound := result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := GeneralProfileAdapter.comp result.adapter (GeneralProfileAdapter.select (by
    intro atom member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨old, raiseProfile_subset result.bound included old present, rfl⟩))
  resources := result.resources
  live := result.live

noncomputable def RichGradedResult.localDemand
    (result : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (need : Need) (bound : need.rank ≤ n)
    (included : ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    RichGradedResult sourceEnv env U registry target node locals σ available need.profile := by
  let selected := result.restrict included
  refine ⟨selected.rank, Nat.le_trans bound selected.bound, selected.raw,
    selected.footprint, selected.observation, ?_, selected.resources, selected.live⟩
  simpa only [Need.atGrade, dif_pos bound, raiseProfile_trans] using selected.adapter

noncomputable def RichArgumentSupply.fromResult
    {available : Valuation}
    (argument : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    RichArgumentSupply sourceEnv env U registry target node locals σ available needs :=
  match needs with
  | [] => .nil
  | need :: rest => .cons
      (argument.localDemand need (bounded need List.mem_cons_self) (covered need List.mem_cons_self))
      (RichArgumentSupply.fromResult argument rest
        (fun next member => bounded next (List.mem_cons_of_mem _ member))
        (fun next member => covered next (List.mem_cons_of_mem _ member)))

/-- Literal row extraction keeps the actual domain/body occurrences of the
native certificate. It does not substitute unrelated app typing premises. -/
structure RichNativeRow
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A B : VExpr} {u v : VLevel}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (key : Key n) (output : Profile n) where
  ambient : Profile n
  domainFootprint : Footprint
  domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A key ambient
  bodyFootprint : Footprint
  bodyCode : RichCert sourceEnv env U registry target body (Locals.push locals)
    (σ.cons key.anchor) true output bodyFootprint
  packed : Profile n
  outside : Footprint
  pack : BinderPack n packed bodyFootprint outside
  covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms
  outsideAvailable : outside.Available available

theorem RichRows.nativeRow
    (domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint)
    (rows : RichRows sourceEnv env U registry target domain body locals σ true ambient table footprint)
    (domainAvailable : domainFootprint.Available available)
    (resources : footprint.Available available)
    (member : (key, output) ∈ table) :
    Nonempty (RichNativeRow sourceEnv env U registry target domain body locals σ available key output) := by
  match rows with
  | .nil => cases member
  | .cons guard code pack covered rest =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact ⟨⟨ambient, domainFootprint, domainCode, domainAvailable, guard, _, code, _, _, pack,
        covered, fun i need h => resources i need (List.mem_append_left _ h)⟩⟩
    · exact rest.nativeRow domainCode domainAvailable
        (fun i need h => resources i need (List.mem_append_right _ h)) member
termination_by sizeOf rows

/-- The source side of one particular lower comparison. The result query has
its own exact finite pack and actual ORIGINAL argument replacements. -/
structure RichApplicationCapture
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A B a : VExpr} {v : VLevel}
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (argument : EndpointState sourceEnv U source a A)
    (locals : List Nat) (σ : Subst) (available : Valuation) (headNeeds : List Need) (support : Profile n) where
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target body (Locals.push locals)
    (σ.cons (a.subst σ)) true support footprint
  sourceAvailable : footprint.Available (available.push headNeeds)
  captureRank : Nat
  packed : Profile captureRank
  outside : Footprint
  pack : BinderPack captureRank packed footprint outside
  outsideAvailable : outside.Available available
  replacements : RichArgumentSupply sourceEnv env U registry target argument locals σ available footprint.localNeeds

private theorem anchor_pair
    (admitted : Admitted env U registry target key x x) :
    Admitted env U registry target key key.anchor x := by
  obtain ⟨raw, _, support, typed, formed, code, anchor, _⟩ := admitted
  exact ⟨raw.hasType.1, raw, support, typed, formed, code, Related.left_diagonal anchor, anchor⟩

/-- A finite body answer generates its own capture pack and every replacement
from the actual original argument query; no source instantiation is assumed. -/
theorem RichNativeRow.captureResult
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : RichNativeRow sourceEnv env U registry target domain body locals σ available (key : Key n) support)
    {argument : EndpointState sourceEnv U source a A}
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available key.input)
    (answer : RichCodeTransferResult env U registry target body body (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (a.subst σ))
      (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) true support) :
    Nonempty (RichApplicationCapture sourceEnv env U registry target body argument locals σ available
      (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) support) := by
  have bounded : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := fun need member atom present =>
    row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  obtain ⟨packed, outside, pack, included, resources⟩ :=
    Footprint.pack_available answer.resources bounded covered
  exact ⟨⟨answer.footprint, answer.certificate, answer.resources, n, packed, outside, pack, resources,
    RichArgumentSupply.fromResult argumentQuery answer.footprint.localNeeds
      (fun need member => (pack.localNeeds need member).1)
      (fun need member atom present => included atom ((pack.localNeeds need member).2 atom present))⟩⟩

theorem RichPiRowCertificate.captureResult
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    (row : RichPiRowCertificate env U registry target locals σ available true domain body (key : Key n) support)
    {argument : EndpointState sourceEnv U source a A}
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available key.input)
    (answer : RichCodeTransferResult env U registry target body body (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (a.subst σ))
      (available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)) true support) :
    Nonempty (RichApplicationCapture sourceEnv env U registry target body argument locals σ available
      (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) support) := by
  have bounded : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons,
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms := fun need member atom present =>
    row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  obtain ⟨packed, outside, pack, included, resources⟩ :=
    Footprint.pack_available answer.resources bounded covered
  exact ⟨⟨answer.footprint, answer.certificate, answer.resources, n, packed, outside, pack, resources,
    RichArgumentSupply.fromResult argumentQuery answer.footprint.localNeeds
      (fun need member => (pack.localNeeds need member).1)
      (fun need member atom present => included atom ((pack.localNeeds need member).2 atom present))⟩⟩

/-- The retained source capture also carries the actual rich binder frame.
Its source F environment records the declared domain; its reindex closure
additionally charges the original argument used by the finite replacements. -/
structure HeaderApplicationCapture
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (base : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (argument : EndpointState headerEnv U headerSource a A) (support : Profile n) where
  needs : List Need
  capture : RichApplicationCapture headerEnv env U registry target body argument locals σ available needs support
  frame : HeaderBinderFrame header field major env registry target (.cons context domain)
    (Locals.push locals) (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (available.push needs)
  substitutions : Ctx.SubstEq env U target (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: headerSource)
  environment_eq : ∀ (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) initial,
    frame.dependencyEnvironment hf sf initial =
      .close (domain.dependencyOrigin hf) (base.dependencyEnvironment hf sf initial) ::
        base.dependencyEnvironment hf sf initial

noncomputable def HeaderApplicationCapture.dependencyEnvironment
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {base : HeaderBinderFrame header field major env registry target context locals σ σ available}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {argument : EndpointState headerEnv U headerSource a A}
    (_query : HeaderApplicationCapture base domain body argument support)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) : List Closure :=
  let previous := base.dependencyEnvironment hf sf initial
  .bundle (.close (argument.dependencyOrigin hf) previous) (.close (domain.dependencyOrigin hf) previous) :: previous

/-- Actual original application row consumption. Both induction hypotheses
receive strict bounds at their real source frames. The captured-body/result
comparison receives the exact finite query and actual rich binder frame. -/
theorem HeaderBinderFrame.applicationRowStep
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headerFormed : headerEnv.Ordered) (sourceFormed : sourceEnv.Ordered) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U headerSource f (.forallE A B))
    (argument : EndpointState headerEnv U headerSource a A)
    (result : EndpointState headerEnv U headerSource (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) (initial : List Closure)
    (row : RichPiRowCertificate env U registry target locals σ available true (.ref domain) body (key : Key n) outputSupport)
    (outputTyped : (Profile.singleton output).HasType outputSupport)
    (functionAnswer : RichBinderValue headerEnv env U registry target function locals σ σ available (Profile.fn key output))
    (argumentAnswer : RichBinderValue headerEnv env U registry target argument locals σ σ available rawInput)
    (argumentObservation : RichObs headerEnv env U registry target argument locals σ rawInput argumentFootprint)
    (argumentAvailable : argumentFootprint.Available available)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (domainF : HeaderCodeInductionAt header field major env registry headerFormed sourceFormed initial context (.ref domain)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
        (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost)
    (bodyF : ∀ needs, (available.push needs).AtomClosed →
      ∀ bodyFrame : HeaderBinderFrame header field major env registry target (.cons context domain)
        (Locals.push locals) (σ.cons key.anchor) (σ.cons (a.subst σ)) (available.push needs),
      richSchedule .fundamental
        (Closure.close (body.dependencyOrigin headerFormed)
          (bodyFrame.dependencyEnvironment headerFormed sourceFormed initial)).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost →
      Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons (a.subst σ)) (A :: headerSource) →
      RichCodeTransfer env U registry target body body (Locals.push locals) (Locals.push locals)
        (σ.cons key.anchor) (σ.cons (a.subst σ)) (available.push needs) (available.push needs))
    (resultR : ∀ {q : Profile n} (capture : HeaderApplicationCapture frame domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost +
         (Closure.close (body.dependencyOrigin headerFormed)
           (capture.dependencyEnvironment headerFormed sourceFormed initial)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q)) :
    Nonempty (RichSupportedValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ σ available (.singleton output)) := by
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  have domainBound : (Closure.close (domain.dependencyOrigin headerFormed)
      (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
        (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost :=
    Nat.lt_of_lt_of_le (binder_domain_cost _ [_] [_ , _, _] _)
      (application_cost_le_captured (domain.dependencyOrigin headerFormed) (body.dependencyOrigin headerFormed)
        (function.dependencyOrigin headerFormed) (argument.dependencyOrigin headerFormed)
        (result.dependencyOrigin headerFormed) (frame.dependencyEnvironment headerFormed sourceFormed initial))
  obtain ⟨domainAnswer⟩ := domainF target locals σ σ available frame domainBound closed formed substitutions
    row.domain row.domainAvailable
  have alignedAdmission := row.alignment.admission henv admitted
  obtain ⟨rawPair, rawArgument, _, _, _, _, pair, self⟩ := alignedAdmission
  let bodyFrame := HeaderBinderFrame.bind frame domain location lineage row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related pair) needs bounded covered
  have bodySubstitutions : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons (a.subst σ)) (A :: headerSource) :=
    .cons substitutions (domain.sound.defeq.mono headerBelow) rawPair
  have bodyClosed : (available.push needs).AtomClosed := Valuation.push_atomized_closed closed row.bodyFootprint.localNeeds
  have bodyBound : richSchedule .fundamental
      (Closure.close (body.dependencyOrigin headerFormed)
        (bodyFrame.dependencyEnvironment headerFormed sourceFormed initial)).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed sourceFormed initial)).cost := by
    apply richSchedule_strict
    exact Nat.lt_of_lt_of_le (binder_body_cost (by simp) _)
      (application_cost_le_captured (domain.dependencyOrigin headerFormed) (body.dependencyOrigin headerFormed)
        (function.dependencyOrigin headerFormed) (argument.dependencyOrigin headerFormed)
        (result.dependencyOrigin headerFormed) (frame.dependencyEnvironment headerFormed sourceFormed initial))
  obtain ⟨bodyAnswer⟩ := bodyF needs bodyClosed bodyFrame bodyBound bodySubstitutions row.body
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  let argumentQuery : RichGradedResult headerEnv env U registry target argument locals σ available key.input :=
    ⟨n, Nat.le_refl n, rawInput, argumentFootprint, argumentObservation,
      by simpa only [raiseProfile_self] using arguments, argumentAvailable,
      argumentAnswer.related.live henv hscoped formed⟩
  obtain ⟨query⟩ := row.captureResult argumentQuery bodyAnswer
  let actualFrame := HeaderBinderFrame.bind frame domain location lineage row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related self) needs bounded covered
  let capture : HeaderApplicationCapture frame domain body argument outputSupport := {
    needs := needs, capture := query, frame := actualFrame
    substitutions := .cons substitutions (domain.sound.defeq.mono headerBelow) rawArgument
    environment_eq := fun _ _ _ => rfl }
  obtain ⟨answer⟩ := resultR capture
    (richSchedule_strict (capturedApplication_comparison _ _ _ _ _ _) _ _)
  have resultRode : TypeRelated env U registry target ((B.inst a).subst σ) ((B.inst a).subst σ) outputSupport :=
    TypeRelated.left_diagonal (TypeRelated.symm henv row.body.formed.wf_value answer.related)
  refine ⟨{
    support := outputSupport
    footprint := answer.footprint
    certificate := answer.certificate
    resources := answer.resources
    typed := outputTyped
    typeCode := resultRode
    related := ?_ }⟩
  simpa only [subst, subst_inst, inst_lift_cons] using Related.apply (B := B.subst σ.lift) henv hscoped formed outputTyped
    (by simpa only [subst_inst, inst_lift_cons] using resultRode)
    (by simpa only [subst] using functionAnswer.related) admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
