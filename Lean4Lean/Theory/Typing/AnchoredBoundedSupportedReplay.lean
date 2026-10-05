import Lean4Lean.Theory.Typing.AnchoredBoundedCaptureFits
import Lean4Lean.Theory.Typing.AnchoredBoundedRhsOpening
import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredTerminalPair

/-! Exact witnessed-to-canonical capture replay at one declaration-stage
fuel. Only stored domain certificates are interpreted, through their actual
original source formation children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Only actual source certificates in the finite replay consume fuel. -/
def NativeSupportedReplay.nativeDepth (current : Name → Bool)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available) : Nat :=
  match replay with
  | .nil | .commonPrefix .. => 0
  | .index previous _ _ _ domainCode .. =>
    max (previous.nativeDepth current) (domainCode.nativeDepth current)
  | .proof previous .. => previous.nativeDepth current

private theorem lift_skipN (e : VExpr) (n : Nat) :
    e.lift' (.skipN .refl n) = e.liftN n := lift'_consN_skipN (k := 0)

private theorem valuation_rename_step (available : Valuation) (n : Nat) :
    Valuation.rename (.skip .refl) (Valuation.rename (.skipN .refl n) available) =
      Valuation.rename (.skipN .refl (n + 1)) available := by
  funext i
  simp only [Valuation.rename, List.map_map]
  congr 1
  funext need
  cases need with
  | mk rank profile =>
    simp only [Function.comp_def, Need.rename, ← Profile.rename_comp, Lift.comp, Lift.skipN]

private theorem raised_lift_r (σ : Subst) (n : Nat) :
    σ.lift_r (.skipN .refl n) = raisedSubst σ n := by
  funext i
  exact lift'_consN_skipN (k := 0)

private theorem raised_cons (σ : Subst) (value : VExpr) (n : Nat) :
    raisedSubst (σ.cons value) n = (raisedSubst σ n).cons (value.liftN n) := by
  funext i
  cases i <;> rfl

private theorem rename_needs_bound {needs : List Need} {n : Nat} (bounded : ∀ need ∈ needs, need.rank ≤ n) (ρ : Lift) :
    ∀ need ∈ needs.map (Need.rename ρ), need.rank ≤ n := by
  intro need member
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp member
  exact bounded old hm

private theorem rename_needs_covered {needs : List Need} {n : Nat} {input : Profile n}
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) (ρ : Lift) :
    ∀ need ∈ needs.map (Need.rename ρ), ∀ atom ∈ (need.atGrade n).atoms,
      atom ∈ (input.rename ρ).atoms := by
  intro need member atom hm
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp member
  rw [← Need.atGrade_rename] at hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  exact List.mem_map_of_mem (covered old hold a ha)

theorem NativeSupportedReplay.canonicalPairBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ A level}, sourceEnv.IsDefEqStrong U Γ A A (.sort level) →
      Staged.Joint current fuel env U registry Γ A A (.sort level))
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : Staged.PairedFits current fuel env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    {declared : List VExpr} {plan : CapturePlan declared} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable declared plan captures locals available)
    (replayBound : replay.nativeDepth current ≤ fuel) :
    ProofInsertion env U target (plan.added (nativeCaptureSubst newValues) ++ target) (.skipN .refl plan.count) ∧
    Ctx.SubstEq env U (plan.added (nativeCaptureSubst newValues) ++ target)
      (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues)) declared ∧
    Staged.PairedFits current fuel env U registry declared (plan.added (nativeCaptureSubst newValues) ++ target) locals
      (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues))
      (Valuation.rename (.skipN .refl plan.count) available) := by
  induction replay with
  | nil => exact ⟨.refl hTarget, .nil, by constructor <;> constructor <;> intro _ _ h <;> cases h⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have raw' := rawArguments
    have fits' := argumentFits
    rw [source] at raw' fits'
    have rawBase := Ctx.SubstEq.nativePrefix raw'
    have fitsBase := fits'.nativePrefix (List.range declared.length)
    have captureNew : plan.captures (nativeCaptureSubst newValues) =
        Subst.lift_l (.skipN .refl later.length) (nativeCaptureSubst newValues) := by
      rw [literal]
      exact nativePrefixPlan_captures _ _ _ (by simpa only [source, List.length_append] using newLength)
    have addedNew : plan.added (nativeCaptureSubst newValues) = [] := by
      rw [literal, nativePrefixPlan_added]
    have zero (σ : Subst) : raisedSubst σ 0 = σ := by
      funext i
      exact liftN_zero _ _
    have renameZero (v : Valuation) : Valuation.rename .refl v = v := by
      funext i
      have hr : Need.rename .refl = id := by
        funext need
        cases need
        simp only [Need.rename, Profile.rename_refl, id_eq]
      simp only [Valuation.rename, hr, List.map_id]
    simpa only [count, addedNew, List.nil_append, Lift.skipN, zero, captureNew, renameZero] using
      And.intro (ProofInsertion.refl hTarget) (And.intro rawBase fitsBase)
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed localNeeds bounded covered ih =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativeSupportedReplay.nativeDepth] using replayBound)
    obtain ⟨insertion, raw, fits⟩ := ih bounds.1
    have hFrame := insertion.targetWF henv
    have formed := formation.defeq.mono hle |>.hasType.1
    have original := earlier formation
    obtain ⟨entry, entryBound⟩ := argumentFits.forward.entry position ⟨n, input⟩ needed natural lookup
    have pair := alignment.related henv typed declaredCode entry.related
    have pair' := pair.future henv insertion.toFuture
    rw [lift'_subst] at pair'
    have certificateData : ∃ certificate : CodeCert env U registry
        (plan.added (nativeCaptureSubst newValues) ++ target) locals
        (captures.lift_r (.skipN .refl plan.count)) domain
        (support.rename (.skipN .refl plan.count)) (footprint.rename (.skipN .refl plan.count)),
        certificate.nativeDepth current ≤ fuel :=
      ⟨domainCode.future henv insertion.toFuture, by
        simpa only [CodeCert.nativeDepth_future] using bounds.2⟩
    rw [raised_lift_r] at certificateData pair'
    obtain ⟨certificate, certificateBound⟩ := certificateData
    have newFits := fits.pushGraded henv hscoped hFrame (closed.rename _)
      (original _ locals _ _ _ (closed.rename _) hFrame raw fits).1
      certificate certificateBound (resources.rename _) (Profile.rename_hasType_iff.mpr typed) pair'
      (localNeeds.map (Need.rename (.skipN .refl plan.count)))
      (rename_needs_bound bounded _) (rename_needs_covered covered _)
    have rawPair := (alignment.path.cast (rawArguments.lookup lookup)).weak' henv insertion.toFuture.weakening
    rw [lift'_subst, raised_lift_r] at rawPair
    simp only [lift_skipN] at rawPair
    refine ⟨insertion, ?_, ?_⟩
    · simpa only [CapturePlan.count, CapturePlan.added, CapturePlan.captures, raised_cons,
        lift_skipN] using Ctx.SubstEq.cons raw formed rawPair
    · simpa only [CapturePlan.count, CapturePlan.added, CapturePlan.captures, raised_cons,
        Valuation.rename_push, lift_skipN] using newFits
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      localNeeds n bounded empty ih =>
    obtain ⟨insertion, raw, fits⟩ := ih (by simpa only [NativeSupportedReplay.nativeDepth] using replayBound)
    have hFrame := insertion.targetWF henv
    have witnessTyped := inhabitant.weak' henv insertion.toFuture.weakening
    rw [lift'_subst, raised_lift_r] at witnessTyped
    have empty' : ∀ need ∈ localNeeds.map (Need.rename (.skipN .refl (plan.count + 1))),
        ∀ atom ∈ (need.atGrade n).atoms, False := by
      intro need member atom hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp member
      rw [← Need.atGrade_rename] at hm
      obtain ⟨a, ha, _⟩ := List.mem_map.mp hm
      exact empty old hold a ha
    obtain ⟨last, newRaw, newFits⟩ := fits.openNativeProof henv hFrame raw
      formation witnessTyped
      (localNeeds.map (Need.rename (.skipN .refl (plan.count + 1)))) n
      (rename_needs_bound bounded _) empty'
    refine ⟨?_, ?_, ?_⟩
    · simpa only [CapturePlan.added, CapturePlan.count, List.cons_append, Lift.comp,
        Lift.skipN] using insertion.comp last henv
    · simpa only [CapturePlan.added, CapturePlan.count, CapturePlan.captures,
        List.cons_append, CapturePlan.skip_raised, CapturePlan.raised_raised, raised_cons,
        lift_skipN, liftN_succ (n := plan.count)] using newRaw
    · simpa only [CapturePlan.added, CapturePlan.count, CapturePlan.captures,
        List.cons_append, CapturePlan.skip_raised, CapturePlan.raised_raised, raised_cons,
        lift_skipN, liftN_succ (n := plan.count), Valuation.rename_push, valuation_rename_step] using newFits

/-- Combine the checked capture producer with the strictly earlier-stage
whole RHS theorem. No natural-body typing is reinterpreted at the native rule
stage, and no caller-provided terminal conversion is required. -/
theorem NativeSupportedReplay.declaredTerminalPairBounded
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Staged.Joint current fuel env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : Staged.PairedFits current fuel env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    {domains : List VExpr} {plan : CapturePlan domains.reverse} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable domains.reverse plan captures locals available)
    (replayBound : replay.nativeDepth current ≤ fuel)
    (closed : available.AtomClosed)
    {rhs result : VExpr}
    (original : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ProofInsertion env U target (plan.added (nativeCaptureSubst newValues) ++ target) (.skipN .refl plan.count) ∧
      Nonempty (Staged.DeclaredRhsResult current fuel env U registry (plan.added (nativeCaptureSubst newValues) ++ target) locals
        (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues))
        (Valuation.rename (.skipN .refl plan.count) available) domains rhs result
        (demand.rename (.skipN .refl plan.count))) := by
  obtain ⟨insertion, raw, fits⟩ := replay.canonicalPairBounded henv hscoped hle
    (fun original => earlier original) hTarget newValues newLength rawArguments argumentFits replayBound
  have observationData : ∃ obs : Obs env U registry (plan.added (nativeCaptureSubst newValues) ++ target)
      locals (captures.lift_r (.skipN .refl plan.count)) rhs (demand.rename (.skipN .refl plan.count))
      (footprint.rename (.skipN .refl plan.count)), obs.nativeDepth current ≤ fuel :=
    ⟨body.future henv insertion.toFuture, by simpa only [Obs.nativeDepth_future] using bodyBound⟩
  have lifted : captures.lift_r (.skipN .refl plan.count) = raisedSubst captures plan.count := by
    funext i
    exact lift'_consN_skipN (k := 0)
  rw [lifted] at observationData
  obtain ⟨observation, observationBound⟩ := observationData
  refine ⟨insertion, ?_⟩
  exact Staged.HasTypeStrong.declaredRhs (source := []) henv hscoped hsource hle earlier trivial original formation
    (closed.rename _) (insertion.targetWF henv)
    (by simpa only [List.append_nil] using raw)
    (by simpa only [List.append_nil] using fits) observation observationBound (resources.rename _)


end Lean4Lean.AnchoredSource.Adapted
