import Lean4Lean.Theory.Typing.AnchoredNativeDepth
import Lean4Lean.Theory.Typing.AnchoredSortableCert

/-! Declaration fuel for the hereditary source grammar. A control charges
only its named delta/native heads. Code actions retain finite target proof
data, and do not introduce source unfoldings. Every source certificate child,
including rich family telescope domains, contributes to the same measure. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

mutual
def SortableCert.nativeDepth (current : Name → Bool)
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) : Nat :=
  match certificate with
  | .ofCode source _ => source.nativeDepth current
  | .seed source _ => source.nativeDepth current
  | .observe source _ => source.nativeDepth current
  | .pi domain _ bodies => max (domain.nativeDepth current) (bodies.nativeDepth current)
  | .union left right => max (left.nativeDepth current) (right.nativeDepth current)
  | .pad source | .sortPad source | .familyPad source | .unpad source | .down source
  | .map _ source | .support _ source | .select source _ | .focusMinimal source _ _ =>
    source.nativeDepth current
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

def SortableRows.nativeDepth (current : Name → Bool)
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ body _ _ tail => max (body.nativeDepth current) (tail.nativeDepth current)
termination_by sizeOf rows
decreasing_by all_goals (simp_wf <;> omega)

def SortableObs.nativeDepth (current : Name → Bool)
    (observation : SortableObs env U registry target locals σ expression demand footprint) : Nat :=
  match observation with
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.nativeDepth current) (certificate.nativeDepth current)
  | .legacy source => source.nativeDepth current
  | .code _ certificate => certificate.nativeDepth current
  | .app fn arg _ _ => max (fn.nativeDepth current) (arg.nativeDepth current)
  | .lam domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .union left right => max (left.nativeDepth current) (right.nativeDepth current)
  | .view source _ | .action source _ | .pad source | .unpad source | .rowShift source =>
    source.nativeDepth current
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

def SortableFamilyPlan.nativeDepth (current : Name → Bool)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.nativeDepth current
  | .binder _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .view source _ | .pad source => source.nativeDepth current
termination_by sizeOf plan
decreasing_by all_goals (simp_wf <;> omega)
end

theorem SortableCert.nativeDepth_cast (current : Name → Bool)
    {p q : Profile n} (profiles : p = q)
    (equal : SortableCert env U registry target locals σ expression relevant p footprint =
      SortableCert env U registry target locals σ expression relevant q footprint)
    (certificate : SortableCert env U registry target locals σ expression relevant p footprint) :
    (cast equal certificate).nativeDepth current = certificate.nativeDepth current := by
  cases profiles; cases equal; rfl

theorem SortableObs.nativeDepth_cast (current : Name → Bool)
    {p q : Profile n} (profiles : p = q)
    (equal : SortableObs env U registry target locals σ expression p footprint =
      SortableObs env U registry target locals σ expression q footprint)
    (observation : SortableObs env U registry target locals σ expression p footprint) :
    (cast equal observation).nativeDepth current = observation.nativeDepth current := by
  cases profiles; cases equal; rfl

end Lean4Lean.AnchoredSource.Adapted
