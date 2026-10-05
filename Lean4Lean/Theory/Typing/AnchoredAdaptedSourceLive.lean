import Lean4Lean.Theory.Typing.AnchoredSourceLive
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax

/-! Finite liveness for the adapted source core, with covered binder inputs. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeCaptures.live
    (captures : NativeCaptures env U registry Γ program witnesses field required native)
    (leaves : Footprint.Live env U registry Γ native) :
    Footprint.Live env U registry Γ required := by
  match captures with
  | .prefix required =>
    intro index need member
    exact leaves _ need (List.mem_map_of_mem (f := fun p => (Lift.liftVar _ p.1, p.2)) member)
  | .index _ _ _ _ _ _ _ _ _ _ pack covered previous =>
    have previousLive := previous.live (Footprint.Live.append_iff.mp
      (Footprint.Live.append_iff.mp leaves).1).1
    have inputLive := (Footprint.Live.append_iff.mp leaves).2 _ _ List.mem_cons_self
    exact pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp previousLive).2
  | .proof _ _ _ _ _ pack previous => exact pack.live .empty (previous.live leaves)
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

mutual
theorem Obs.live
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (observation : Obs env U registry Γ locals σ expression (profile : Profile n) footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ profile := by
  match observation with
  | .delta _ _ _ _ _ _ _ _ _ _ _ body => exact body.live henv hscoped hΓ leaves
  | .native _ _ _ _ _ _ _ _ _ _ _ tree => exact tree.live henv hscoped hΓ leaves
  | .family _ _ _ _ _ _ _ _ _ _ _ _ tree => exact tree.live henv hscoped hΓ leaves
  | .constructor _ _ _ _ _ _ _ _ _ _ _ _ tree => exact tree.live henv hscoped hΓ leaves
  | .var _ _ i demand => exact leaves i _ List.mem_cons_self
  | .empty => exact .empty
  | .sort relevant =>
    cases n with
    | zero => exact fun _ _ => True.intro
    | succ n =>
      intro atom member
      cases List.mem_singleton.mp member
      trivial
  | .app fn arg arguments admitted =>
    have fnLive := fn.live henv hscoped hΓ (Footprint.Live.append_iff.mp leaves).1
    exact Profile.Live.singleton_iff.mpr (Profile.Live.singleton_iff.mp fnLive).2
  | .lam domain guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
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

theorem NativePlan.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (tree : NativePlan env U registry Γ signature arguments demand footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ demand := by
  match tree with
  | .terminal _ _ _ _ _ _ _ _ _ _ _ _ body captures =>
    exact body.live henv hscoped hΓ (captures.live leaves)
  | .binder _ _ guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega
theorem FamilyPlan.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (tree : FamilyPlan env U registry Γ name levels signature arguments demand footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ demand := by
  match tree with
  | .terminal _ _ _ _ => exact Profile.Live.singleton_iff.mpr True.intro
  | .binder _ _ guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
  | .view source change =>
    exact Profile.Live.singleton_iff.mpr
      (change.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .pad source => exact Profile.Live.pad_iff.mpr (source.live henv hscoped hΓ leaves)
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega
theorem ConstructorPlan.live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (tree : ConstructorPlan env U registry Γ name levels signature arguments demand footprint)
    (leaves : Footprint.Live env U registry Γ footprint) :
    Profile.Live env U registry Γ demand := by
  match tree with
  | .terminal _ _ _ _ _ => exact Profile.Live.singleton_iff.mpr True.intro
  | .binder _ _ guard body pack covered =>
    obtain ⟨_, _, support, _, _, _, anchor, _⟩ := guard.anchor
    have inputLive := Related.live henv hscoped hΓ anchor
    have bodyLeaves := pack.live (inputLive.subset covered) (Footprint.Live.append_iff.mp leaves).2
    have bodyLive := body.live henv hscoped hΓ bodyLeaves
    exact Profile.Live.singleton_iff.mpr ⟨guard.anchor, Profile.Live.singleton_iff.mp bodyLive⟩
  | .view source change =>
    exact Profile.Live.singleton_iff.mpr
      (change.live henv hscoped hΓ (Profile.Live.singleton_iff.mp
        (source.live henv hscoped hΓ leaves)))
  | .pad source => exact Profile.Live.pad_iff.mpr (source.live henv hscoped hΓ leaves)
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega
end
end Lean4Lean.AnchoredSource.Adapted
