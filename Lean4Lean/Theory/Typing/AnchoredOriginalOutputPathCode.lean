import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin
import Lean4Lean.Theory.Typing.AnchoredAtomActionCode

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GeneralOutputPath.codeAtOutput
    (henv : env.Ordered)
    (path : GeneralOutputPath env U registry target source atom)
    (formed : (Profile.singleton atom).HasType (.sort relevant)) :
    ∃ flag, (Profile.singleton source).HasType (.sort flag) ∧
      Nonempty (SortableCodeAction env U registry target flag (.singleton source)
        relevant (.singleton atom)) := by
  induction path generalizing relevant with
  | refl => exact ⟨_, formed, ⟨.id⟩⟩
  | action path action ih =>
    obtain ⟨middle, inputFormed, ⟨last⟩⟩ := action.toCodeAtOutput henv formed
    obtain ⟨flag, firstFormed, ⟨first⟩⟩ := ih inputFormed
    exact ⟨flag, firstFormed, ⟨.comp first last⟩⟩
  | code path action inputFormed ih =>
    obtain ⟨flag, firstFormed, ⟨first⟩⟩ := ih inputFormed
    exact ⟨flag, firstFormed, ⟨.comp first (.comp action (.retag formed))⟩⟩
  | @pad n atom path ih =>
    change (Profile.singleton atom).pad.HasType (.sort relevant) at formed
    have low : (Profile.singleton atom).HasType (.sort relevant) := by
      simpa only [Profile.down_sort] using formed.pad_inv
    obtain ⟨flag, firstFormed, ⟨first⟩⟩ := ih low
    exact ⟨flag, firstFormed, ⟨.comp first (by simpa only [Profile.pad_singleton] using
      (SortableCodeAction.pad (profile := Profile.singleton atom)))⟩⟩
  | @unpad n atom path ih =>
    obtain ⟨flag, firstFormed, ⟨first⟩⟩ := ih formed.pad_sort
    exact ⟨flag, firstFormed, ⟨.comp first (by simpa only [Profile.pad_singleton] using
      (SortableCodeAction.unpad (profile := Profile.singleton atom)))⟩⟩


/-- A retained sortable leaf can compile its output path without recovering
any semantics of an earlier profile. This direction needs no ambient order. -/
noncomputable def GeneralOutputPath.codeAtInput
    (path : GeneralOutputPath env U registry target source atom)
    (formed : (Profile.singleton source).HasType (.sort relevant)) :
    SortableCodeAction env U registry target relevant (.singleton source)
      relevant (.singleton atom) := by
  induction path with
  | refl => exact .id
  | action path change ih => exact .comp ih (change.toCode (ih.preservesSort formed))
  | code path change required ih =>
    exact .comp ih (.comp (.retag required)
      (.comp change (.retag (change.preservesSort (ih.preservesSort formed)))))
  | pad path ih =>
    exact .comp ih (by simpa only [Profile.pad_singleton] using
      (SortableCodeAction.pad (profile := Profile.singleton _)))
  | unpad path ih =>
    exact .comp ih (by simpa only [Profile.pad_singleton] using
      (SortableCodeAction.unpad (profile := Profile.singleton _)))

noncomputable def GeneralOutputPath.lowerRaisedPi
    {a : Atom n} (bound : n ≤ N)
    (path : GeneralOutputPath env U registry target source (raiseAtom N bound a)) :
    GeneralOutputPath env U registry target source a := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact path
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n; simpa only [raiseAtom_self] using path
    · have previous : n ≤ N := by omega
      rw [raiseAtom_step previous] at path
      exact ih previous (.unpad path)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
