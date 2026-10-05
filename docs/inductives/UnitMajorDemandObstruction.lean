import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
/-! The original result type of a dependent eliminator can retain a query on
its major even when the selected computation does not use that major.

For every closed, originally formed family, `originalMotiveQuery` derives
actual Strong formation of `motive major` in the original two-binder context.
`CodeCert.motiveQuery` constructs an actual certificate of that same source
expression whose footprint retains any supplied admitted major input.
Consequently runtime independence alone cannot establish empty major demand
for the current unrestricted certificate grammar. The admitted key is an
explicit premise; this file does not construct a new constant environment or
claim that the obstruction survives a future eligibility restriction. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- A valid dependent result-type certificate retains its admitted major
query independently of the implementation of the target motive. -/
noncomputable def CodeCert.motiveQuery
    {env : VEnv} {U n : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst}
    (key : Key (n + 1))
    (admitted : Admitted env U registry target key (σ 0) (σ 0)) :
    CodeCert env U registry target locals σ (.app (.bvar 1) (.bvar 0)) (.sort (n := n + 1) true)
      [(1, ⟨n + 2, Profile.fn key (.sort true)⟩), (0, ⟨n + 1, key.input⟩)] := by
  exact .seed (.app (.var locals σ 1 (Profile.fn key (.sort true)))
    (.var locals σ 0 key.input) (ProfileAdapter.refl _) admitted) (Profile.HasType.sort true)

theorem motiveQuery_hasMajor (key : Key (n + 1)) :
    (0, ⟨n + 1, key.input⟩) ∈
      ([(1, ⟨n + 2, Profile.fn key (.sort true)⟩), (0, ⟨n + 1, key.input⟩)] : Footprint) := by
  simp
end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.VEnv
open VExpr

theorem originalMotiveQuery
    {env : VEnv} {U : Nat} (henv : env.Ordered) {family : VExpr} {u v : VLevel}
    (uWF : u.WF U) (vWF : v.WF U)
    (familyFormation : env.IsDefEqStrong U [] family family (.sort u)) :
    env.IsDefEqStrong U [family, .forallE family (.sort v)]
      (.app (.bvar 1) (.bvar 0)) (.app (.bvar 1) (.bvar 0)) (.sort v) := by
  have closed : family.Closed := (familyFormation.defeq.closedN' henv.closed trivial).1
  have fnClosed : (VExpr.forallE family (.sort v)).Closed := ⟨closed, trivial⟩
  have fnLookup : Lookup [family, .forallE family (.sort v)] 1 (.forallE family (.sort v)) := by
    simpa only [fnClosed.lift_eq] using
      (Lookup.succ (A := family) (Lookup.zero (Γ := []) (ty := .forallE family (.sort v))))
  have majorLookup : Lookup [family, .forallE family (.sort v)] 0 family := by
    simpa only [closed.lift_eq] using
      (Lookup.zero (Γ := [.forallE family (.sort v)]) (ty := family))
  have formation := familyFormation.weak0 henv (Γ := [family, .forallE family (.sort v)])
  have bodyFormation : ∀ Γ, env.IsDefEqStrong U Γ (.sort v) (.sort v) (.sort (.succ v)) :=
    fun _ => .sortDF vWF vWF (by rfl)
  have fnFormation : env.IsDefEqStrong U [family, .forallE family (.sort v)]
      (.forallE family (.sort v)) (.forallE family (.sort v)) (.sort (.imax u (.succ v))) :=
    .forallEDF uWF vWF formation (bodyFormation _) (bodyFormation _)
  have fnTyped : env.IsDefEqStrong U [family, .forallE family (.sort v)]
      (.bvar 1) (.bvar 1) (.forallE family (.sort v)) :=
    .bvar fnLookup (u := .imax u (.succ v)) ⟨uWF, vWF⟩ fnFormation
  exact .appDF (v := .succ v) uWF vWF formation (bodyFormation _) fnTyped
    (.bvar majorLookup uWF formation) (bodyFormation _)
end Lean4Lean.VEnv
