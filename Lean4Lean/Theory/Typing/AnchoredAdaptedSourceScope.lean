import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFundamental
import Lean4Lean.Theory.Typing.AnchoredSourceLive

/-! Every required source variable occurs in the actual expression. This
lets finite beta replacement supplies obtain external liveness from genuine
context lookup entries; target-only guards add no source occurrences. -/
namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def Footprint.Scoped (count : Nat) (footprint : Footprint) : Prop :=
  ∀ i need, (i, need) ∈ footprint → i < count

theorem Footprint.Scoped.append
    (left : Footprint.Scoped count first) (right : Footprint.Scoped count second) :
    Footprint.Scoped count (first ++ second) := by
  intro i need hm
  exact (List.mem_append.mp hm).elim (left i need) (right i need)

theorem BinderPack.scoped
    (pack : BinderPack n packed required outside)
    (bounded : Footprint.Scoped (count + 1) required) : Footprint.Scoped count outside := by
  induction pack with
  | nil => exact fun _ _ h => nomatch h
  | «local» need bound rest ih =>
    exact ih (fun i need hm => bounded i need (List.mem_cons_of_mem _ hm))
  | external index need rest ih =>
    intro i original hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      have := bounded (index + 1) need List.mem_cons_self
      omega
    · exact ih (fun i need hm => bounded i need (List.mem_cons_of_mem _ hm)) i original hm

namespace Adapted
mutual
theorem Obs.scoped
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) : Footprint.Scoped count footprint := by
  match observation with
  | .var _ _ i demand =>
    intro index need hm
    cases List.mem_singleton.mp hm
    exact scope
  | .delta .. | .native .. | .family .. | .constructor .. => exact fun _ _ h => nomatch h
  | .empty | .sort _ => exact fun _ _ h => nomatch h
  | .app fn arg _ _ =>
    exact Footprint.Scoped.append (fn.scoped scope.1) (arg.scoped scope.2)
  | .lam domain _ body normal _ =>
    exact Footprint.Scoped.append (domain.scoped scope.1)
      (normal.scoped (body.scoped scope.2))
  | .pi domain _ bodies =>
    exact Footprint.Scoped.append (domain.scoped scope.1) (bodies.scoped scope.2)
  | .union left right => exact Footprint.Scoped.append (left.scoped scope) (right.scoped scope)
  | .view source _ | .pad source | .unpad source | .rowShift source => exact source.scoped scope
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.scoped
    (certificate : CodeCert env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) : Footprint.Scoped count footprint := by
  match certificate with
  | .seed observation _ => exact observation.scoped scope
  | .union left right => exact Footprint.Scoped.append (left.scoped scope) (right.scoped scope)
  | .pad source | .familyPad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ =>
    exact source.scoped scope
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

theorem PiRows.scoped
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (scope : B.ClosedN (count + 1)) : Footprint.Scoped count footprint := by
  match bodies with
  | .nil => exact fun _ _ h => nomatch h
  | .cons _ body normal _ tail =>
    exact Footprint.Scoped.append (normal.scoped (body.scoped scope)) (tail.scoped scope)
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega
end

theorem Fits.leavesLive
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (fits : Fits env U registry source Γ locals σ τ available)
    (resources : footprint.Available available)
    (bounded : Footprint.Scoped source.length footprint) :
    Footprint.Live env U registry Γ footprint := by
  intro index need member
  obtain ⟨sourceType, lookup⟩ := Lookup.ofLt (bounded index need member)
  obtain ⟨entry⟩ := fits.entry index need (resources index need member) sourceType lookup
  exact Related.live henv hscoped hΓ entry.related

end Adapted
end Lean4Lean.AnchoredSource
