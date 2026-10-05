import Lean4Lean.Theory.Typing.AnchoredLiveInterpretation
import Lean4Lean.Theory.Typing.AnchoredSourceObservation

/-! Finite liveness across the actual source binder footprint. -/
namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem raiseProfile_live_iff {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    Profile.Live env U registry Γ (raiseProfile N bound profile) ↔
      Profile.Live env U registry Γ profile := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rw [raiseProfile_self]
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; rw [raiseProfile_self]
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn, Profile.Live.pad_iff, ih hn]

def Footprint.Live (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (footprint : Footprint) : Prop :=
  ∀ index need, (index, need) ∈ footprint → Profile.Live env U registry Γ need.profile

theorem Footprint.Live.append_iff :
    Footprint.Live env U registry Γ (left ++ right) ↔
      Footprint.Live env U registry Γ left ∧ Footprint.Live env U registry Γ right := by
  constructor
  · intro h
    exact ⟨fun i need hm => h i need (List.mem_append_left _ hm),
      fun i need hm => h i need (List.mem_append_right _ hm)⟩
  · rintro ⟨hl, hr⟩ i need hm
    exact (List.mem_append.mp hm).elim (hl i need) (hr i need)

theorem BinderPack.live {input : Profile n}
    (pack : BinderPack n input required outside)
    (inside : Profile.Live env U registry Γ input)
    (external : Footprint.Live env U registry Γ outside) :
    Footprint.Live env U registry Γ required := by
  induction pack with
  | nil => exact fun _ _ h => nomatch h
  | «local» need bound rest ih =>
    obtain ⟨head, tail⟩ := Profile.Live.union_iff.mp inside
    have lower : Profile.Live env U registry Γ need.profile := by
      simp only [Need.atGrade, dif_pos bound] at head
      exact (raiseProfile_live_iff bound need.profile).mp head
    intro index wanted member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact lower
    · exact ih tail external index wanted member
  | external index need rest ih =>
    intro i wanted member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact external index need List.mem_cons_self
    · exact ih inside (fun j need hm => external j need (List.mem_cons_of_mem _ hm))
        i wanted member

/-- Actual variable leaves supply finite liveness. Lambda-local demands are
recovered from the guard's genuine input relation and the original binder
pack; they are not added to the ambient source valuation. -/
theorem Obs.live
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (observation : Obs env U registry Γ locals σ expression (profile : Profile n) footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ profile := by
  match observation with
  | .var _ _ i demand => exact leaves i _ List.mem_cons_self
  | .empty => exact .empty
  | .sort relevant =>
    cases n with
    | zero => exact fun _ _ => True.intro
    | succ n =>
      intro atom member
      cases List.mem_singleton.mp member
      trivial
  | .app fn arg admitted =>
    have fnLive := fn.live henv hscoped hΓ (Footprint.Live.append_iff.mp leaves).1
    exact Profile.Live.singleton_iff.mpr (Profile.Live.singleton_iff.mp fnLive).2
  | .lam domain guard body pack =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live inputLive (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
  | .pi domain guard bodies =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial
  | .union left right =>
    have parts := Footprint.Live.append_iff.mp leaves
    exact Profile.Live.union_iff.mpr
      ⟨left.live henv hscoped hΓ parts.1, right.live henv hscoped hΓ parts.2⟩
  | .view source change =>
    exact Profile.Live.singleton_iff.mpr
      (change.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .pad source => exact Profile.Live.pad_iff.mpr (source.live henv hscoped hΓ leaves)
  | .unpad source => exact Profile.Live.pad_iff.mp (source.live henv hscoped hΓ leaves)
  | .rowShift source =>
    have old := Profile.Live.singleton_iff.mp (source.live henv hscoped hΓ leaves)
    exact Profile.Live.singleton_iff.mpr ⟨Admitted.pad henv old.1, old.2⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource
