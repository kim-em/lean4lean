import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax

/-! In the current source grammar, observations of one source variable do not
supply a nonempty code certificate for another source variable. This is the
structural resource obligation behind the dependent Box projection example
in RECORD-ETA-COVERAGE.md; no revised projection grammar is assumed here. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem AtomView.mapType_empty {a b : Atom n}
    (view : AtomView env U registry target a b) :
    view.mapType .empty = .empty := by
  match n, a, b, view with
  | _, _, _, .refl _ => rfl
  | _ + 1, _, _, .reanchor _ => rfl
  | _ + 1, _, _, .domainRekey .. => rfl
  | _ + 1, _, _, .input .. => rfl
  | _ + 2, _, _, .commutePadFn .. => rfl
  | _ + 2, _, _, .uncommutePadFn .. => rfl
  | _ + 1, _, _, .fn .. => rfl
  | _ + 1, _, _, .pad child =>
    change (child.mapType .empty).pad = .empty
    rw [AtomView.mapType_empty child]
    rfl
  | _, _, _, .trans first second =>
    change second.mapType (first.mapType .empty) = .empty
    rw [AtomView.mapType_empty first, AtomView.mapType_empty second]
termination_by sizeOf view

theorem Obs.variable_absent_empty
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {index : Nat}
    {demand : Profile n} {footprint : Footprint} {available : Valuation}
    (observation : Obs env U registry target locals σ (.bvar index) demand footprint)
    (resources : footprint.Available available) (absent : available index = []) :
    demand = .empty := by
  match n, demand, footprint, observation with
  | _, _, _, .var .. =>
    have present := resources _ _ List.mem_cons_self
    rw [absent] at present
    exact False.elim (List.not_mem_nil present)
  | _, _, _, .empty => rfl
  | _, _, _, .union left right =>
    have hl := left.variable_absent_empty
      (fun i need member => resources i need (List.mem_append_left _ member)) absent
    have hr := right.variable_absent_empty
      (fun i need member => resources i need (List.mem_append_right _ member)) absent
    rw [hl, hr]; rfl
  | _, _, _, .view source _ =>
    have empty := source.variable_absent_empty resources absent
    cases empty
  | _, _, _, .pad source =>
    rw [source.variable_absent_empty resources absent]; rfl
  | _, _, _, .unpad source =>
    have empty := source.variable_absent_empty resources absent
    exact List.map_eq_nil_iff.mp empty
  | _, _, _, .rowShift source =>
    have empty := source.variable_absent_empty resources absent
    cases empty
termination_by sizeOf observation

theorem CodeCert.variable_absent_empty
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {index : Nat}
    {support : Profile n} {footprint : Footprint} {available : Valuation}
    (certificate : CodeCert env U registry target locals σ (.bvar index) support footprint)
    (resources : footprint.Available available) (absent : available index = []) :
    support = .empty := by
  match certificate with
  | .seed observation _ => exact observation.variable_absent_empty resources absent
  | .union left right =>
    have hl := left.variable_absent_empty
      (fun i need member => resources i need (List.mem_append_left _ member)) absent
    have hr := right.variable_absent_empty
      (fun i need member => resources i need (List.mem_append_right _ member)) absent
    rw [hl, hr]; rfl
  | .pad source => rw [source.variable_absent_empty resources absent]; rfl
  | .familyPad source =>
    have empty := source.variable_absent_empty resources absent
    cases empty
  | .unpad source => exact List.map_eq_nil_iff.mp (source.variable_absent_empty resources absent)
  | .down source => rw [source.variable_absent_empty resources absent]; rfl
  | .map view source => rw [source.variable_absent_empty resources absent, AtomView.mapType_empty view]
  | .select source member =>
    have empty := source.variable_absent_empty resources absent
    rw [empty] at member
    cases member
termination_by sizeOf certificate

end Lean4Lean.AnchoredSource.Adapted
