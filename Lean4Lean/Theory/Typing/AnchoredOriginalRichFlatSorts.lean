import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredFlatSortsGrades

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

theorem RichCert.sortFlag
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (profile : Profile n) footprint)
    (resources : footprint.Available available) (member : flag ∈ profile.sortFlags) :
    ∃ required, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.sort (n := n) flag) required) ∧ required.Available available := by
  induction n with
  | zero => exact ⟨_, ⟨.select certificate member⟩, resources⟩
  | succ n ih =>
    obtain ⟨_, ⟨source⟩, resources⟩ := ih certificate.down member
    exact source.codeAction .sortPad resources

theorem RichCert.sortAt {n m : Nat}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.sort (n := n) flag) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.sort (n := m) flag) required) ∧ required.Available available := by
  have base : ∃ required, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.sort (n := 0) flag) required) ∧ required.Available available := by
    induction n with
    | zero => exact ⟨_, ⟨certificate⟩, resources⟩
    | succ n ih => exact ih (by simpa only [Profile.down_sort] using certificate.down)
  induction m with
  | zero => exact base
  | succ m ih =>
    obtain ⟨_, ⟨source⟩, resources⟩ := ih
    exact source.codeAction .sortPad resources

theorem RichCert.flatSortsAt {profile : Profile n}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant
      (profile.flatSortsAt m) required) ∧ required.Available available := by
  have build (flags : List Bool) (included : List.Subset flags profile.sortFlags) :
      ∃ required, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant
        (Profile.sortsAt m flags) required) ∧ required.Available available := by
    induction flags with
    | nil => exact ⟨[], ⟨.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)))⟩,
        fun _ _ h => nomatch h⟩
    | cons flag rest ih =>
      obtain ⟨_, ⟨tail⟩, tailResources⟩ := ih (fun _ h => included (List.mem_cons_of_mem _ h))
      obtain ⟨_, ⟨head⟩, headResources⟩ := certificate.sortFlag resources (included List.mem_cons_self)
      obtain ⟨_, ⟨head⟩, headResources⟩ := head.sortAt (m := m) headResources
      exact ⟨_, ⟨.union head tail⟩, fun i need member =>
        (List.mem_append.mp member).elim (headResources i need) (tailResources i need)⟩
  exact build profile.sortFlags (fun _ h => h)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
