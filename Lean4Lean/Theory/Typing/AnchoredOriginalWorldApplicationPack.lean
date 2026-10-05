import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRichFrameHead
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowReplayOperations

/-! Finite application binder packing retains controls on the exact selected
head certificates. Every support interpretation is an original domain-child
call; no richer argument or family answer is supplied to the packer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private worldCode singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}

private theorem raiseCertificateControlled
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) (bound : n ≤ N) :
    ∃ raised : RichCert sourceEnv env U registry target node locals σ relevant (raiseProfile N bound profile) footprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate raised)) := by
  obtain ⟨raised, annotation, worlds, depth⟩ := certificate.raise_worlds_depth ready.annotation bound
  refine ⟨raised, ⟨⟨annotation, ?_, ?_⟩⟩⟩
  · intro control active
    change raised.headDepth _ ≤ _
    rw [depth]
    exact ready.within control active
  · simpa only [StoredOriginalQuery.Provenance.worlds, worlds] using ready.sponsored

private theorem transportControlledCertificate
    {certificate : RichCert sourceEnv env U registry target node firstLocals firstSubst relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (localsEq : firstLocals = secondLocals) (substEq : firstSubst = secondSubst) :
    ∃ output : RichCert sourceEnv env U registry target node secondLocals secondSubst relevant profile footprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate output)) := by
  cases localsEq
  cases substEq
  exact ⟨certificate, ⟨ready⟩⟩

private theorem typedBinderPackWorld
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (henv : env.Ordered) (required : Footprint) (minimum : Nat)
    (head : ∀ need, (0, need) ∈ required →
      ∃ support footprint,
        ∃ certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
          (support : Profile need.rank) footprint,
        footprint.Available available ∧ need.profile.HasType support ∧
        TypeRelated env U registry target (A.subst σ) (A.subst σ) support ∧
        Related env U registry target left right (A.subst σ) need.profile support ∧
        Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)))
    (external : ∀ i need, (i+1, need) ∈ required → need ∈ available i) :
    ∃ packed : RichTypedBinderPack domain env registry target locals σ available left right required minimum,
      Nonempty (ControlledStoredQuery controls frontier (.certificate packed.certificate)) := by
  induction required with
  | nil =>
    refine ⟨⟨minimum, Nat.le_refl _, .empty, .empty, [],
      .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true))),
      (fun _ _ h => nomatch h), Profile.HasType.empty Profile.WF.empty,
      TypeRelated.of_singletons (fun _ h => nomatch h), Related.of_singletons (fun _ h => nomatch h),
      [], .nil, (fun _ _ h => nomatch h)⟩, ⟨⟨.legacy _ (.seed _ _ .empty), ?_, ?_⟩⟩⟩
    · intro control active
      simp only [StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    · intro world member
      cases member
  | cons entry rest ih =>
    obtain ⟨tail, ⟨tailReady⟩⟩ := ih (fun need h => head need (List.mem_cons_of_mem _ h))
      (fun i need h => external i need (List.mem_cons_of_mem _ h))
    rcases entry with ⟨i, need⟩
    cases i with
    | succ i =>
      exact ⟨⟨tail.rank, tail.bound, tail.input, tail.support, tail.footprint,
        tail.certificate, tail.resources, tail.typed, tail.code, tail.related,
        (i, need) :: tail.outside, .external i need tail.pack,
        fun index wanted h => (List.mem_cons.mp h).elim
          (fun equal => by cases equal; exact external i need List.mem_cons_self)
          (tail.external index wanted)⟩, ⟨tailReady⟩⟩
    | zero =>
      obtain ⟨support, footprint, certificate, resources, typed, code, related, ⟨certificateReady⟩⟩ := head need List.mem_cons_self
      let N := max need.rank tail.rank
      have hn : need.rank ≤ N := Nat.le_max_left _ _
      have ht : tail.rank ≤ N := Nat.le_max_right _ _
      let combined := (raiseProfile N hn support).union (raiseProfile N ht tail.support)
      have firstTyped := Profile.HasType.raise hn typed
      have tailTyped := Profile.HasType.raise ht tail.typed
      have wf := firstTyped.wf_type.union tailTyped.wf_type
      have firstTyped' := firstTyped.enlarge (Profile.le_union_left _ _) wf
      have tailTyped' := tailTyped.enlarge (Profile.le_union_right _ _) wf
      have combinedCode : TypeRelated env U registry target (A.subst σ) (A.subst σ) combined := by
        apply TypeRelated.of_singletons
        intro atom member
        exact (List.mem_append.mp member).elim
          (fun h => (code.raise henv hn).singleton h)
          (fun h => (tail.code.raise henv ht).singleton h)
      obtain ⟨first, ⟨firstReady⟩⟩ := raiseCertificateControlled certificateReady hn
      obtain ⟨second, ⟨secondReady⟩⟩ := raiseCertificateControlled tailReady ht
      refine ⟨⟨N, Nat.le_trans tail.bound ht,
        (raiseProfile N hn need.profile).union (raiseProfile N ht tail.input), combined,
        footprint ++ tail.footprint, .union first second,
        (fun i need h => (List.mem_append.mp h).elim (resources i need) (tail.resources i need)),
        firstTyped'.union tailTyped', combinedCode,
        (Related.retag henv firstTyped' combinedCode (related.raise henv hn)).union
          (Related.retag henv tailTyped' combinedCode (tail.related.raise henv ht)),
        tail.outside, ?_, tail.external⟩, ⟨firstReady.certUnion secondReady⟩⟩
      simpa only [Need.atGrade, dif_pos hn] using BinderPack.local need hn (tail.pack.raise ht)

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

 theorem ApplicationBackwardQueries.headCode_controlled
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (ready : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query))
    (member : need ∈ packet.footprint.localNeeds) :
    ∃ support footprint,
      ∃ certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
        (support : Profile need.rank) footprint,
      footprint.Available available ∧ need.profile.HasType support ∧
      Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) need.profile support ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) := by
  let selected := packet.reply.answer.reply.realization.frame
  have found := packet.resources 0 need (Footprint.mem_localNeeds.mp member)
  obtain ⟨answer, answerReady⟩ := selected.headCode_controlled henv formed ready found
  have positions : selected.peel.tailLocals = locals := by
    have first := selected.peel.positions
    have second := packet.reply.answer.reply.locals_eq
    change packet.reply.answer.reply.locals = Locals.push locals at second
    exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
      (List.cons.inj (first.trans second)).2
  have external : ∀ i need, need ∈ packet.reply.answer.reply.available (i + 1) → need ∈ available i := by
    intro i wanted present
    exact packet.reply.answer.capped.availableBound (i + 1) wanted present
  have identityTail : ((Subst.id.cons a).comp σ).tail = σ := by funext i; rfl
  obtain ⟨answerReady⟩ := answerReady
  obtain ⟨certificate, ready⟩ := transportControlledCertificate answerReady positions
    (show ((Subst.id.cons (a.subst .id)).comp σ).tail = σ by simpa only [subst_id] using identityTail)
  refine ⟨answer.support, answer.footprint, certificate,
    (fun i wanted present => external i wanted (answer.resources i wanted present)), answer.typed, ?_, ready⟩
  simpa only [applicationBodyDisplay, Subst.comp, Subst.cons, Subst.head, Subst.tail, subst_id, identityTail] using answer.related

/-- The head supplies the actual declared query; unary F interprets each
finite support at the original domain child under the fixed application
baseline. The resulting pack retains those exact query annotations. -/
theorem ApplicationBackwardQueries.typedPackWorld
    {P : VEnv → Prop}
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment sourceControls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment sourceControls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (frameData : WorldUnaryFrameData P sourceControls frontier frame captured)
    (headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery sourceControls frontier query))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (sponsored : Sponsored frontier [originalCallWorld sourceControls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld sourceControls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ packed : RichTypedBinderPack domain env registry target locals σ available
      (a.subst σ) (a.subst τ) packet.footprint n,
      Nonempty (ControlledStoredQuery sourceControls frontier (.certificate packed.certificate)) := by
  let diagonal := frame.leftDiagonal
  let diagonalCaptured := frame.diagonalWorld sourceControls captured
  have diagonalCovered : Covered (@EquationControlMeasure.Less strata.rules.length)
      diagonalCaptured.worlds baseline.worlds := by
    simpa only [diagonalCaptured, OriginalRichFrame.diagonalWorld_worlds] using covered
  have reserve := application_cost_le_captured (domain.dependencyOrigin sourceControls.ordered)
    (body.dependencyOrigin sourceControls.ordered) (function.dependencyOrigin sourceControls.ordered)
    (argument.dependencyOrigin sourceControls.ordered) (result.dependencyOrigin sourceControls.ordered)
    (frame.dependencyEnvironment sourceControls.ordered)
  have smaller : (Closure.close (domain.dependencyOrigin sourceControls.ordered)
      (diagonal.dependencyEnvironment sourceControls.ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin sourceControls.ordered)
        baselineEnvironment).cost := by
    rw [show diagonal.dependencyEnvironment sourceControls.ordered = frame.dependencyEnvironment sourceControls.ordered from
      frame.dependencyEnvironment_leftDiagonal sourceControls.ordered]
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_domain_cost _ _ _ _) reserve)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1))
  have child : WorldBelow strata.rules.length
      (originalCallWorld sourceControls .fundamental (.ref domain) diagonalCaptured)
      (originalCallWorld sourceControls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
    smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict smaller _ _) _ _ _ _) diagonalCovered
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld sourceControls .fundamental (.ref domain) diagonalCaptured])
      (frontier ++ [originalCallWorld sourceControls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have lower := split_call (calls := [originalCallWorld sourceControls .fundamental (.ref domain) diagonalCaptured])
      (fun node member => by cases List.mem_singleton.mp member; exact child)
    have appendLower : ∀ sponsors : List (World strata.rules.length), CallBelow strata.rules.length
        (sponsors ++ [originalCallWorld sourceControls .fundamental (.ref domain) diagonalCaptured])
        (sponsors ++ [originalCallWorld sourceControls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact lower
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  apply typedBinderPackWorld domain henv packet.footprint n
  · intro need member
    obtain ⟨support, footprint, certificate, resources, typed, related, ⟨certificateReady⟩⟩ :=
      packet.headCode_controlled henv formed headReady (Footprint.mem_localNeeds.mpr member)
    obtain ⟨meaning, _⟩ := worldCode sourceControls diagonal diagonalCaptured frontier _ bank funded
      (singletonSponsoredBelow sponsored child) (.ofLocation (.appDomain location) initial)
      frameData.leftDiagonal henv hscoped closed formed substitutions.left certificate resources certificateReady
    exact ⟨support, footprint, certificate, resources, typed, meaning.related, related, ⟨certificateReady⟩⟩
  · intro i need member
    exact packet.reply.answer.capped.availableBound (i + 1) need (packet.resources (i + 1) need member)

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
