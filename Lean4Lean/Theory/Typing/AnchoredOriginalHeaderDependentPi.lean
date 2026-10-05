import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPairedApplication
import Lean4Lean.Theory.Typing.AnchoredLiteralPiPair

/-! A genuinely dependent original header Pi: its codomain applies a captured
function to the fresh argument. Replaying the original application admission
under paired binder frames constructs its capabilities at arbitrary admitted
arguments, rather than assuming a general rich-body fundamental theorem.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem admitted_from_anchor
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry target key x y) :
    Admitted env U registry target key key.anchor x ∧
      Admitted env U registry target key key.anchor y := by
  obtain ⟨anchorRaw, pairRaw, support, typed, formed, code, anchor, pair⟩ := admitted
  have anchorSelf := Related.left_diagonal anchor
  exact ⟨⟨anchorRaw.hasType.1, anchorRaw, support, typed, formed, code, anchorSelf, anchor⟩,
    ⟨anchorRaw.hasType.1, anchorRaw.trans pairRaw, support, typed, formed, code,
      anchorSelf, Related.trans henv hscoped anchor pair⟩⟩

/-- The exact original domain answer and frozen application payload generate
both source Pi syntax and all future dependent rows. In particular, no body
certificate or capability for an arbitrary new argument is supplied. -/
theorem HeaderBinderFrame.dependentApplicationPi
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (frame : HeaderBinderFrame header field major env registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (body : EndpointState headerEnv U (A :: headerSource)
      (.app (.bvar (functionIndex + 1)) (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (domainAnswer : RichCodeTransferResult env U registry target (.ref domain) (.ref domain)
      locals σ σ available true (ambient : Profile n))
    (outerKey innerKey : Key n) (output : Atom n)
    (outputFormed : (Profile.singleton output).HasType (.sort relevant))
    (guard : LambdaGuard env U registry target σ A outerKey ambient)
    (prototype : PiGuard env U target σ A (.app (.bvar (functionIndex + 1)) (.bvar 0))
      prototypeDomain prototypeBody)
    (functionNeed : Need.mk (n + 1) (Profile.fn innerKey output) ∈ available functionIndex)
    (functionLookup : Lookup headerSource functionIndex (.forallE A familyBody))
    (rawInput : Profile n)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput innerKey.input)
    (inputCovered : ∀ atom ∈ rawInput.atoms, atom ∈ outerKey.input.atoms)
    (admitted : Admitted env U registry target innerKey outerKey.anchor outerKey.anchor) :
    ∃ footprint,
      Nonempty (RichCert headerEnv env U registry target (.pi hu hv (.ref domain) body)
        locals σ relevant
        (Profile.pi prototypeDomain prototypeBody ambient [(outerKey, .singleton output)]) footprint) ∧
      footprint.Available available ∧
      TypeRelated env U registry target
        ((VExpr.forallE A (.app (.bvar (functionIndex + 1)) (.bvar 0))).subst σ)
        ((VExpr.forallE A (.app (.bvar (functionIndex + 1)) (.bvar 0))).subst σ)
        (Profile.pi prototypeDomain prototypeBody ambient [(outerKey, .singleton output)]) := by
  let bodyFootprint : Footprint :=
    [(functionIndex + 1, Need.mk (n + 1) (Profile.fn innerKey output)), (0, Need.mk n rawInput)]
  let bodyCode : RichCert headerEnv env U registry target body (Locals.push locals)
      (σ.cons outerKey.anchor) relevant (.singleton output) bodyFootprint :=
    .legacy (.observe (.app (.legacy (.var _ _ _ _)) (.legacy (.var _ _ _ _))
      arguments admitted) outputFormed)
  have pack : BinderPack n rawInput bodyFootprint
      [(functionIndex, Need.mk (n + 1) (Profile.fn innerKey output))] := by
    apply BinderPack.external
    simpa only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self,
      Profile.union, Profile.empty, Profile.atoms, Profile.mk, List.append_nil] using
      (BinderPack.local (Need.mk n rawInput) (Nat.le_refl n) BinderPack.nil)
  let rows := RichRows.cons (domain := EndpointState.ref domain) guard bodyCode pack inputCovered RichRows.nil
  refine ⟨_, ⟨.pi hu hv domainAnswer.certificate prototype rows⟩, ?_, ?_⟩
  · intro index need member
    rcases List.mem_append.mp member with member | member
    · exact domainAnswer.resources index need member
    · cases List.mem_singleton.mp member
      exact functionNeed
  · have originalDomain := domain.sound.defeq.mono headerBelow
    have originalBody := body.sound.defeq.mono headerBelow
    have hA := originalDomain.subst henv substitutions formed
    have hB := originalBody.subst henv (substitutions.lift henv originalDomain) ⟨formed, _, hA⟩
    apply TypeRelated.literalPiPair henv formed ⟨_, hA⟩ ⟨_, hA⟩ ⟨_, hB⟩ ⟨_, hB⟩
      .refl .refl prototype.domainPath prototype.bodyPath domainAnswer.related
    · intro key result member
      cases List.mem_singleton.mp member
      exact ⟨ambient, guard.inputTyped, domainAnswer.certificate.formed, Profile.le_refl _,
        guard.path, guard.domains⟩
    · intro key result member Δ ρ future x y incoming
      cases List.mem_singleton.mp member
      have shiftedFrame := frame.future henv future
      have shiftedDomain := domainAnswer.certificate.future henv future
      have shiftedGuard := guard.future henv future
      have shiftedArguments := GeneralNormalProfileAdapter.future henv future arguments
      have shiftedAdmitted := Admitted.future henv future admitted
      have shiftedSubstitutions := substitutions.future henv future
      have shiftedFunctionNeed : Need.mk (n + 1)
          (Profile.fn (innerKey.rename ρ) (output.rename ρ)) ∈ (available.rename ρ) functionIndex := by
        simpa only [Valuation.rename, Need.rename, Profile.fn, Profile.rename_singleton,
          Atom.rename_fn] using List.mem_map_of_mem (f := Need.rename ρ) functionNeed
      have shiftedSorted : (Profile.singleton (output.rename ρ)).HasType (.sort relevant) := by
        simpa only [Profile.rename_singleton, Profile.rename_sort] using
          (Profile.rename_hasType_iff (ρ := ρ)).mpr outputFormed
      have boundNeeds : ∀ need ∈ [Need.mk n (rawInput.rename ρ)], need.rank ≤ n := by
        intro need member; cases List.mem_singleton.mp member; exact Nat.le_refl _
      have coverNeeds : ∀ need ∈ [Need.mk n (rawInput.rename ρ)],
          ∀ atom ∈ (need.atGrade n).atoms, atom ∈ (outerKey.rename ρ).input.atoms := by
        intro need member atom atomMember
        cases List.mem_singleton.mp member
        simp only [Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self] at atomMember
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp atomMember
        exact List.mem_map_of_mem (inputCovered old oldMember)
      have atArgument : ∀ z, Admitted env U registry Δ (outerKey.rename ρ) (outerKey.rename ρ).anchor z →
          TypeRelated env U registry Δ
            (.app ((σ functionIndex).lift' ρ) (outerKey.anchor.lift' ρ))
            (.app ((σ functionIndex).lift' ρ) z) (.singleton (output.rename ρ)) := by
        intro z hz
        obtain ⟨⟨localFrame⟩, localSubstitutions⟩ := shiftedFrame.pushAdmitted henv headerBelow
          shiftedSubstitutions domain location lineage shiftedDomain (domainAnswer.resources.rename ρ)
          shiftedGuard hz [Need.mk n (rawInput.rename ρ)] boundNeeds coverNeeds
        have localFunction : Lookup (A :: headerSource) (functionIndex + 1)
            (.forallE A.lift (familyBody.liftN 1 1)) := functionLookup.succ
        obtain ⟨_, _, _, related⟩ := localFrame.pairedCapturedApplication henv hscoped
          (future.targetWF henv) localSubstitutions body (innerKey.rename ρ) (output.rename ρ)
          shiftedSorted shiftedFunctionNeed localFunction (rawInput.rename ρ) shiftedArguments
          (List.mem_singleton_self _) Lookup.zero shiftedAdmitted
        simpa only [Subst.cons, Subst.lift_r, Key.rename] using related
      obtain ⟨toLeft, toRight⟩ := admitted_from_anchor henv hscoped incoming
      have left := atArgument x toLeft
      have right := atArgument y toRight
      have pair := (left.symm henv shiftedSorted.wf_value).trans henv right
      have instantiated (z : VExpr) :
          (((VExpr.app (.bvar (functionIndex + 1)) (.bvar 0)).subst σ.lift).lift' ρ.cons).inst z =
            .app ((σ functionIndex).lift' ρ) z := by
        rw [lift'_subst, ← Subst.lift_r_lift, inst_lift_cons]
        rfl
      exact ⟨by simpa only [instantiated, Profile.rename_singleton] using pair,
        by simpa only [instantiated, Profile.rename_singleton] using pair,
        by simpa only [instantiated, Profile.rename_singleton] using pair.left_diagonal⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
