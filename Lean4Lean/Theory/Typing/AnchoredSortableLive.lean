import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredSortableFamilyPlan
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLive
import Lean4Lean.Theory.Typing.AnchoredAtomActionLive

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic sortability excludes live function demands, including below
padding; no semantic leaf or data-relevance restriction is needed. -/
theorem Profile.HasType.sortable_live
    {profile : Profile n} (formed : profile.HasType (.sort relevant)) :
    Profile.Live env U registry Γ profile := by
  induction n with
  | zero => exact fun _ _ => True.intro
  | succ n ih =>
    intro atom member
    cases atom with
    | sort | pi | family | ctor | record => trivial
    | fn key output =>
      obtain ⟨other, hm, typed⟩ := formed.2.2 _ member
      cases List.mem_singleton.mp hm
      contradiction
    | pad atom =>
      have padded : (Profile.singleton atom).pad.HasType (.sort relevant) := by
        simpa only [Profile.pad_singleton] using formed.singleton_of_mem member
      have lower := padded.pad_inv
      simp only [Profile.down_sort] at lower
      exact (ih lower) atom (List.mem_singleton_self _)

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem SortableCert.live
    (certificate : SortableCert env U registry Γ locals σ expression relevant profile footprint) :
    Profile.Live env U registry Γ profile :=
  AnchoredSemantics.Profile.HasType.sortable_live certificate.formed

theorem SortableObs.live
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (observation : SortableObs env U registry Γ locals σ expression (profile : Profile n) footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ profile := by
  match observation with
  | .family _ _ _ _ _ _ _ _ _ _ _ _ tree => exact tree.live henv hscoped hΓ leaves
  | .legacy observation => exact observation.live henv hscoped hΓ leaves
  | .code relevant certificate => exact certificate.live
  | .app fn arg arguments admitted =>
    have fnLive := fn.live henv hscoped hΓ (Footprint.Live.append_iff.mp leaves).1
    exact Profile.Live.singleton_iff.mpr (Profile.Live.singleton_iff.mp fnLive).2
  | .lam domain guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
  | .union left right =>
    have parts := Footprint.Live.append_iff.mp leaves
    exact Profile.Live.union_iff.mpr
      ⟨left.live henv hscoped hΓ parts.1, right.live henv hscoped hΓ parts.2⟩
  | .view source change =>
    exact Profile.Live.singleton_iff.mpr
      (change.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .action source act =>
    exact Profile.Live.singleton_iff.mpr
      (act.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .pad source => exact Profile.Live.pad_iff.mpr (source.live henv hscoped hΓ leaves)
  | .unpad source => exact Profile.Live.pad_iff.mp (source.live henv hscoped hΓ leaves)
  | .rowShift source =>
    have old := Profile.Live.singleton_iff.mp (source.live henv hscoped hΓ leaves)
    exact Profile.Live.singleton_iff.mpr ⟨Admitted.pad henv old.1, old.2⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
