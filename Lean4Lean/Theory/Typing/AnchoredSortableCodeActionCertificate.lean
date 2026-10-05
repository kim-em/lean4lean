import Lean4Lean.Theory.Typing.AnchoredCodeAction
import Lean4Lean.Theory.Typing.AnchoredSortableCert

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The resource footprint is computed by the finite action. Only conjunction
repeats leaves; all primitive actions retain the original footprint. -/
def SortableCodeAction.footprint
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (source : Footprint) : Footprint :=
  match action with
  | .id | .retag .. | .pad | .down | .unpad | .sortPad | .familyPad |
      .map .. | .support .. | .select .. | .focusMinimal .. => source
  | .comp first second => second.footprint (first.footprint source)
  | .union first second => first.footprint source ++ second.footprint source

noncomputable def SortableCodeAction.applyCertificate
    {footprint : Footprint}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (certificate : SortableCert env U registry target locals σ expression relevant profile footprint) :
    SortableCert env U registry target locals σ expression next nextProfile (action.footprint footprint) :=
  match action with
  | .id => certificate
  | .comp first second => second.applyCertificate (first.applyCertificate certificate)
  | .union first second => .union (first.applyCertificate certificate) (second.applyCertificate certificate)
  | .retag formed => .observe (.code _ certificate) formed
  | .pad => .pad certificate
  | .down => .down certificate
  | .unpad => .unpad certificate
  | .sortPad => .sortPad certificate
  | .familyPad => .familyPad certificate
  | .map view => .map view certificate
  | .support action => .support action certificate
  | .select member => .select certificate member
  | .focusMinimal minimal bound => .focusMinimal certificate minimal bound

theorem SortableCodeAction.available
    {footprint : Footprint} {available : Valuation}
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    (resources : footprint.Available available) : (action.footprint footprint).Available available := by
  induction action generalizing footprint with
  | comp first second firstIH secondIH => exact secondIH (firstIH resources)
  | union first second firstIH secondIH =>
    intro index need member
    exact (List.mem_append.mp member).elim (firstIH resources index need) (secondIH resources index need)
  | _ => exact resources

end Lean4Lean.AnchoredSource.Adapted
