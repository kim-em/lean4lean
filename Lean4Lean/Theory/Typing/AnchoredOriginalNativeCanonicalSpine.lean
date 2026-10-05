import Lean4Lean.Theory.Typing.AnchoredOriginalNativePairedSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalNativeCaptureSpineReplay

/-! Full finite witnessed-to-canonical capture replay with retained forward
certificates. All proof insertions and both substitutions are constructed;
the old unrestricted predecessor theorem is not an input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private lift_skipN raised_cons raised_lift_r valuation_rename_step
  rename_needs_bound rename_needs_covered from
  Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure NativeCanonicalSpineResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target declared : List VExpr)
    (plan : CapturePlan declared) (captures : Subst) (newValues : List VExpr)
    (locals : List Nat) (available : Valuation) where
  insertion : ProofInsertion env U target (plan.added (nativeCaptureSubst newValues) ++ target)
    (.skipN .refl plan.count)
  substitutions : Ctx.SubstEq env U (plan.added (nativeCaptureSubst newValues) ++ target)
    (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues)) declared
  locals_eq : locals = List.range declared.length
  spine : NativeCertificateSpine env U registry (plan.added (nativeCaptureSubst newValues) ++ target)
    declared (raisedSubst captures plan.count) (plan.captures (nativeCaptureSubst newValues))
    (Valuation.rename (.skipN .refl plan.count) available)

noncomputable def NativeSupportedReplay.canonicalSpine
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target argumentSource
      arguments (nativeCaptureSubst newValues) argumentAvailable)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    NativeCanonicalSpineResult env U registry target declared plan captures newValues locals available := by
  induction replay with
  | nil => exact ⟨.refl formed, .nil, rfl, .nil⟩
  | @commonPrefix later declared plan source literal count added captures =>
    have raw := rawArguments
    have spine := argumentsSpine
    rw [source] at raw spine
    have rawBase := Ctx.SubstEq.nativePrefix raw
    have spineBase := spine.drop later
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
    have shift (σ : Subst) : Subst.lift_l (.skipN .refl later.length) σ =
        fun i => σ (i + later.length) := by
      funext i
      simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar]
    refine ⟨?_, ?_, rfl, ?_⟩
    · simpa only [count, addedNew, List.nil_append, Lift.skipN] using ProofInsertion.refl formed
    · simpa only [count, addedNew, List.nil_append, Lift.skipN, zero, captureNew] using rawBase
    · simpa only [count, addedNew, List.nil_append, Lift.skipN, zero, captureNew, renameZero, shift]
        using spineBase
  | @index n level declared plan captures locals available domain natural position support input footprint
      previous formation lookup needed domainCode resources typed alignment declaredCode closed
      needs bounded covered ih =>
    let insertion := ih.insertion
    have hFrame := insertion.targetWF henv
    have domainFormation := formation.defeq.mono below |>.hasType.1
    let entry := Classical.choose ((argumentsSpine.frame argumentContext).lookup_allDepth
      henv formed needed lookup)
    have pair := alignment.related henv typed declaredCode entry.related
    have pair' := pair.future henv insertion.toFuture
    rw [lift'_subst] at pair'
    have certificate := domainCode.future henv insertion.toFuture
    rw [raised_lift_r, ih.locals_eq] at certificate
    rw [raised_lift_r] at pair'
    let next := NativeCertificateSpine.cons ih.spine certificate (resources.rename _)
      (Profile.rename_hasType_iff.mpr typed) pair'
      (needs.map (Need.rename (.skipN .refl plan.count)))
      (rename_needs_bound bounded _) (rename_needs_covered covered _)
    have rawPair := (alignment.path.cast (rawArguments.lookup lookup)).weak' henv insertion.toFuture.weakening
    rw [lift'_subst, raised_lift_r] at rawPair
    simp only [lift_skipN] at rawPair
    refine ⟨insertion, ?_, ?_, ?_⟩
    · simpa only [CapturePlan.count, CapturePlan.added, CapturePlan.captures, raised_cons,
        lift_skipN] using Ctx.SubstEq.cons ih.substitutions domainFormation rawPair
    · simp only [ih.locals_eq, List.length_cons, List.range_succ_eq_map, Locals.push]
    · simpa only [CapturePlan.count, CapturePlan.added, CapturePlan.captures, raised_cons,
        Valuation.rename_push, lift_skipN] using next
  | @proof declared plan captures locals available domain witness previous formation inhabitant
      needs n bounded empty ih =>
    let insertion := ih.insertion
    have hFrame := insertion.targetWF henv
    have witnessTyped := inhabitant.weak' henv insertion.toFuture.weakening
    rw [lift'_subst, raised_lift_r] at witnessTyped
    have empty' : ∀ need ∈ needs.map (Need.rename (.skipN .refl (plan.count + 1))),
        ∀ atom ∈ (need.atGrade n).atoms, False := by
      intro need member atom hm
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp member
      rw [← Need.atGrade_rename] at hm
      obtain ⟨a, ha, _⟩ := List.mem_map.mp hm
      exact empty old hold a ha
    let next := ih.spine.openProof henv hFrame ih.substitutions formation witnessTyped
      (needs.map (Need.rename (.skipN .refl (plan.count + 1)))) n
      (rename_needs_bound bounded _) empty'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [CapturePlan.added, CapturePlan.count, List.cons_append, Lift.comp,
        Lift.skipN] using insertion.comp next.insertion henv
    · simpa only [CapturePlan.added, CapturePlan.count, CapturePlan.captures,
        List.cons_append, CapturePlan.skip_raised, CapturePlan.raised_raised, raised_cons,
        lift_skipN, liftN_succ (n := plan.count)] using next.substitutions
    · simp only [ih.locals_eq, List.length_cons, List.range_succ_eq_map, Locals.push]
    · simpa only [CapturePlan.added, CapturePlan.count, CapturePlan.captures,
        List.cons_append, CapturePlan.skip_raised, CapturePlan.raised_raised, raised_cons,
        lift_skipN, liftN_succ (n := plan.count), Valuation.rename_push, valuation_rename_step] using next.spine

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
