import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaPacket
import Lean4Lean.Theory.Typing.EquationControls
import Lean4Lean.Theory.Typing.EquationControlMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalDeltaBudgetSpend
import Lean4Lean.Theory.Typing.AnchoredEquationControlBudgets

/-! The canonical packet's actual finite children fund its opening. The
source cutoff and strict alternating-order decrease are both computed from
the retained packet. Simultaneous caller controls are spent and reconstructed
on those same children, including multiple controls selecting this head.
This does not yet construct the caller's returned formation certificate. -/
/-! The unmasked budget lemmas below are local compatibility facts, not the
global preservation contract. Opening rank j can install equations selected
by lower caller controls. `EquationStratifiedFuel` instead masks those lower
controls at the rebuilt head and requires child preservation only at ranks
at least j. -/
namespace Lean4Lean.AnchoredSource.Adapted.CanonicalDeltaPacket
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
set_option Elab.async false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {name : Name} {levels : List VLevel}
  {profile : Profile n}

noncomputable def fuel
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (ordinal : Nat) : Nat := packet.nativeDepth (strata.headControl registry ordinal)

noncomputable def childFuel
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (ordinal : Nat) : Nat :=
  max (packet.body.nativeDepth (strata.headControl registry ordinal))
    (packet.certificate.nativeDepth (strata.headControl registry ordinal))

theorem childFuel_le
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (ordinal : Nat) : packet.childFuel ordinal ≤ packet.fuel ordinal :=
  Nat.le_add_right _ _

theorem childFuel_selected_lt
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile) :
    packet.childFuel packet.selected.ordinal < packet.fuel packet.selected.ordinal := by
  apply packet.children_lt
  exact strata.headControl_definition packet.lookup packet.registered.2

/-- No supplied bound on the borrowed proof size or constant count is used.
The child fuel is the maximum of the actual stored body and type queries. -/
theorem openingDecrease
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (cutoff : Nat) (bounded : cutoff ≤ strata.rules.length)
    (constants schedule childSchedule : Nat) :
    strata.SourceCutoff packet.selected.origin.source (packet.selected.ordinal - 1) ∧
      EquationControlMeasure.Less
        (EquationControlMeasure.key strata.rules.length (packet.selected.ordinal - 1)
          packet.childFuel packet.selected.origin.ordered.constantCount childSchedule)
        (EquationControlMeasure.key strata.rules.length cutoff packet.fuel constants schedule) := by
  refine ⟨packet.selected.sourceCutoff, ?_⟩
  apply EquationControlMeasure.selectedSourceDecrease packet.selected bounded
  · intro index _ _
    exact packet.childFuel_le index
  · intro _
    exact packet.childFuel_selected_lt

/-- The usable call edge for an enclosing state: its controls can be larger
than this query's exact depth because they also fund frames and dormant
histories. The input budget proves the decrease, without an extra numerical
smaller-call premise. All lower controls are computed from the actual children. -/
theorem openingWithinDecrease
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length)
    {callerFuel : Nat → Nat}
    (bounded : Budgeted.Within (strata.controlBudgets registry cutoff callerFuel) packet.nativeDepth)
    (constants schedule childSchedule : Nat) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (packet.selected.ordinal - 1)
        packet.childFuel packet.selected.origin.ordered.constantCount childSchedule)
      (EquationControlMeasure.key strata.rules.length cutoff callerFuel constants schedule) := by
  have controls := EquationStratification.within_controlBudgets.mp bounded
  apply EquationControlMeasure.selectedSourceDecrease packet.selected cutoffBound
  · intro index above inRange
    exact Nat.le_trans (packet.childFuel_le index) (controls index (by omega) inRange)
  · intro above
    exact Nat.lt_of_lt_of_le packet.childFuel_selected_lt
      (controls packet.selected.ordinal above packet.selected.ordinal_le)

/-- Each selecting caller control is spent, not assumed quiet. This also
retains the payment evidence needed when the actual returned query is rebuilt. -/
theorem spentChildren
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (bounded : Budgeted.Within budgets packet.nativeDepth) :
    Budgeted.HeadPaid name budgets ∧
      Budgeted.Within (Budgeted.spend name budgets) packet.body.nativeDepth ∧
      Budgeted.Within (Budgeted.spend name budgets) packet.certificate.nativeDepth :=
  Budgeted.Within.spendDelta bounded

/-- This applies to the selected returned packet itself, so it does not
replace its children with unrelated witnesses satisfying different bounds. -/
theorem rebuildWithin
    (packet : CanonicalDeltaPacket env U registry target strata name levels profile)
    (paid : Budgeted.HeadPaid name budgets)
    (bodyBound : Budgeted.Within (Budgeted.spend name budgets) packet.body.nativeDepth)
    (certificateBound : Budgeted.Within (Budgeted.spend name budgets) packet.certificate.nativeDepth) :
    Budgeted.Within budgets packet.nativeDepth :=
  Budgeted.Within.rebuildDelta paid bodyBound certificateBound

end Lean4Lean.AnchoredSource.Adapted.CanonicalDeltaPacket
