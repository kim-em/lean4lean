import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredSortableHeadDepth

/-! Constant relocation constructs the moved query and its world annotation
jointly. Closed declaration payloads and their exact query sites are retained;
only the surrounding locals and substitution change. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem append_eq {first nextFirst second nextSecond : List α}
    (firstEq : first = nextFirst) (secondEq : second = nextSecond) :
    first ++ second = nextFirst ++ nextSecond := by
  cases firstEq
  cases secondEq
  rfl

mutual
theorem WorldLegacyObsProvenance.relocateConstant
    {query : Obs env U registry target locals σ (.const name levels) profile footprint}
    (annotation : WorldLegacyObsProvenance strata query) (newLocals : List Nat) (τ : Subst) :
    ∃ moved : Obs env U registry target newLocals τ (.const name levels) profile footprint,
      ∃ next : WorldLegacyObsProvenance strata moved,
        next.worlds = annotation.worlds ∧ ∀ policy, moved.headDepth policy = query.headDepth policy := by
  match annotation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body certificateProvenance bodyProvenance origin typeSite bodySite =>
    exact ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body, .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body certificateProvenance bodyProvenance origin typeSite bodySite, rfl,
      fun policy => by simp only [Obs.headDepth]⟩
  | .native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerType headerSite =>
    exact ⟨.native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed certificate typed tree, .native lookup notDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerType headerSite, rfl,
      fun policy => by simp only [Obs.headDepth]⟩
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite =>
    exact ⟨.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite, rfl,
      fun policy => by simp only [Obs.headDepth]⟩
  | .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite =>
    exact ⟨.constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite, rfl,
      fun policy => by simp only [Obs.headDepth]⟩
  | .empty => exact ⟨.empty, .empty, rfl, fun policy => by simp only [Obs.headDepth]⟩
  | .union first second firstAnnotation secondAnnotation =>
    obtain ⟨first, firstNext, firstWorlds, firstDepth⟩ := firstAnnotation.relocateConstant newLocals τ
    obtain ⟨second, secondNext, secondWorlds, secondDepth⟩ := secondAnnotation.relocateConstant newLocals τ
    exact ⟨.union first second, .union first second firstNext secondNext,
      append_eq firstWorlds secondWorlds,
      fun policy => by simp only [Obs.headDepth, firstDepth, secondDepth]⟩
  | .view child change childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.view child change, .view child change childNext, childWorlds,
      fun policy => by simp only [Obs.headDepth, childDepth]⟩
  | .pad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.pad child, .pad child childNext, childWorlds,
      fun policy => by simp only [Obs.headDepth, childDepth]⟩
  | .unpad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.unpad child, .unpad child childNext, childWorlds,
      fun policy => by simp only [Obs.headDepth, childDepth]⟩
  | .rowShift child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.rowShift child, .rowShift child childNext, childWorlds,
      fun policy => by simp only [Obs.headDepth, childDepth]⟩
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldLegacyCertProvenance.relocateConstant
    {query : CodeCert env U registry target locals σ (.const name levels) profile footprint}
    (annotation : WorldLegacyCertProvenance strata query) (newLocals : List Nat) (τ : Subst) :
    ∃ moved : CodeCert env U registry target newLocals τ (.const name levels) profile footprint,
      ∃ next : WorldLegacyCertProvenance strata moved,
        next.worlds = annotation.worlds ∧ ∀ policy, moved.headDepth policy = query.headDepth policy := by
  match annotation with
  | .union first second firstAnnotation secondAnnotation =>
    obtain ⟨first, firstNext, firstWorlds, firstDepth⟩ := firstAnnotation.relocateConstant newLocals τ
    obtain ⟨second, secondNext, secondWorlds, secondDepth⟩ := secondAnnotation.relocateConstant newLocals τ
    exact ⟨.union first second, .union first second firstNext secondNext,
      append_eq firstWorlds secondWorlds,
      fun policy => by simp only [CodeCert.headDepth, firstDepth, secondDepth]⟩
  | .seed child formed childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.seed child formed, .seed child formed childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .pad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.pad child, .pad child childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .familyPad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.familyPad child, .familyPad child childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .unpad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.unpad child, .unpad child childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .down child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.down child, .down child childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .map change child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.map change child, .map change child childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .select child member childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.select child member, .select child member childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
  | .focusMinimal child minimal bound childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.focusMinimal child minimal bound, .focusMinimal child minimal bound childNext, childWorlds,
      fun policy => by simp only [CodeCert.headDepth, childDepth]⟩
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableObsProvenance.relocateConstant
    {query : SortableObs env U registry target locals σ (.const name levels) profile footprint}
    (annotation : WorldSortableObsProvenance strata query) (newLocals : List Nat) (τ : Subst) :
    ∃ moved : SortableObs env U registry target newLocals τ (.const name levels) profile footprint,
      ∃ next : WorldSortableObsProvenance strata moved,
        next.worlds = annotation.worlds ∧ ∀ policy, moved.headDepth policy = query.headDepth policy := by
  match annotation with
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite =>
    exact ⟨.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree certificateProvenance treeProvenance origin headerSite, rfl,
      fun policy => by simp only [SortableObs.headDepth]⟩
  | .union first second firstAnnotation secondAnnotation =>
    obtain ⟨first, firstNext, firstWorlds, firstDepth⟩ := firstAnnotation.relocateConstant newLocals τ
    obtain ⟨second, secondNext, secondWorlds, secondDepth⟩ := secondAnnotation.relocateConstant newLocals τ
    exact ⟨.union first second, .union first second firstNext secondNext,
      append_eq firstWorlds secondWorlds,
      fun policy => by simp only [SortableObs.headDepth, firstDepth, secondDepth]⟩
  | .legacy child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.legacy child, .legacy child childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .code relevant child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.code relevant child, .code relevant child childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .view child change childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.view child change, .view child change childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .action child change childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.action child change, .action child change childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .pad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.pad child, .pad child childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .unpad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.unpad child, .unpad child childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
  | .rowShift child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.rowShift child, .rowShift child childNext, childWorlds,
      fun policy => by simp only [SortableObs.headDepth, childDepth]⟩
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableCertProvenance.relocateConstant
    {query : SortableCert env U registry target locals σ (.const name levels) relevant profile footprint}
    (annotation : WorldSortableCertProvenance strata query) (newLocals : List Nat) (τ : Subst) :
    ∃ moved : SortableCert env U registry target newLocals τ (.const name levels) relevant profile footprint,
      ∃ next : WorldSortableCertProvenance strata moved,
        next.worlds = annotation.worlds ∧ ∀ policy, moved.headDepth policy = query.headDepth policy := by
  match annotation with
  | .union first second firstAnnotation secondAnnotation =>
    obtain ⟨first, firstNext, firstWorlds, firstDepth⟩ := firstAnnotation.relocateConstant newLocals τ
    obtain ⟨second, secondNext, secondWorlds, secondDepth⟩ := secondAnnotation.relocateConstant newLocals τ
    exact ⟨.union first second, .union first second firstNext secondNext,
      append_eq firstWorlds secondWorlds,
      fun policy => by simp only [SortableCert.headDepth, firstDepth, secondDepth]⟩
  | .ofCode child formed childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.ofCode child formed, .ofCode child formed childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .observe child formed childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.observe child formed, .observe child formed childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .seed child formed childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.seed child formed, .seed child formed childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .pad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.pad child, .pad child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .sortPad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.sortPad child, .sortPad child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .familyPad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.familyPad child, .familyPad child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .unpad child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.unpad child, .unpad child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .down child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.down child, .down child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .map change child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.map change child, .map change child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .support change child childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.support change child, .support change child childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .select child member childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.select child member, .select child member childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
  | .focusMinimal child minimal bound childAnnotation =>
    obtain ⟨child, childNext, childWorlds, childDepth⟩ := childAnnotation.relocateConstant newLocals τ
    exact ⟨.focusMinimal child minimal bound, .focusMinimal child minimal bound childNext, childWorlds,
      fun policy => by simp only [SortableCert.headDepth, childDepth]⟩
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
