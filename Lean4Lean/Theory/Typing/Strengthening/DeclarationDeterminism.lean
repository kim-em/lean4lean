import Lean4Lean.Theory.Typing.Strengthening.RegisteredStructureEquations

/-! # Deterministic stored and structure equations

Stored constant equations recover the unique installed definition at that head.
Registered structure equations have an owned constructor and hence an actual
registered iota rule, whose head is disjoint from every stored equation. Their
union is therefore deterministic at fixed universe syntax.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- A stored bare-constant equation is exactly the installed definition's value
at the displayed universe list. The quotient equation has a lambda left side. -/
theorem Definitions.ofEnv_origin (henv : env.WF)
    (H : (Definitions.ofEnv env U henv).unfolds name levels rhs) :
    ∃ value : VDefVal, env.definitionRegistry name = some value ∧
      value.name = name ∧ rhs = value.value.instL levels := by
  obtain ⟨df, us, hd, hw, hl, he, hr⟩ := H
  obtain ⟨ds, henv'⟩ := henv
  rcases henv'.defeqs_origin hd with rfl | ⟨value, hv, rfl⟩
  · cases he
  · change us.length = value.uvars at hl
    have he' : .const value.name us = VExpr.const name levels := by
      simpa only [VDefVal.toDefEq, instL, VLevel.inst_map_id hl] using he
    obtain ⟨hn, rfl⟩ := VExpr.const.inj he'
    exact ⟨value, hn ▸ (show env.WF from ⟨ds, henv'⟩).definitionRegistry_of_defeq hv,
      hn, hr.symm⟩

/-- Stored equations are functional at fixed name and universe arguments,
including recursive definitions. No termination premise is used. -/
theorem Definitions.ofEnv_unique (henv : env.WF)
    (H1 : (Definitions.ofEnv env U henv).unfolds name levels rhs1)
    (H2 : (Definitions.ofEnv env U henv).unfolds name levels rhs2) : rhs1 = rhs2 := by
  obtain ⟨v1, h1, _, rfl⟩ := Definitions.ofEnv_origin henv H1
  obtain ⟨v2, h2, _, rfl⟩ := Definitions.ofEnv_origin henv H2
  cases Option.some.inj (h1.symm.trans h2)
  rfl

/-- A registered recursor with an owned constructor heads an actual iota rule;
therefore it cannot also have a stored bare-constant equation. -/
theorem Definitions.ofEnv_no_registered (henv : env.WF)
    (hr : RecursorRegistered env data)
    (hi : ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner)
    (H : (Definitions.ofEnv env U henv).unfolds data.name levels rhs) : False := by
  obtain ⟨index, howner⟩ := hi
  obtain ⟨equation, hgen⟩ := hr.equation_exists' index
  obtain ⟨rec, ru, hc, hof, hp⟩ := hr.restoredEquation_pat index hgen
  have hh := hr.equation_head howner hgen
  rw [VExpr.stripLams_eq_lamBody, ← VExpr.getAppFn_eq_fst] at hh
  have hn := hof.2.1
  rw [VExpr.headConst?_eq_some, hh] at hn
  obtain ⟨_, hn⟩ := hn
  obtain ⟨v, hv, hvn, _⟩ := Definitions.ofEnv_origin henv H
  have hdef := (definitionRegistry_registered hv).1.2
  exact henv.defeq_head_not_pat hdef (show v.toDefEq.lhs.stripLams.getAppFnArgs.1 =
    .const v.name (VLevel.params v.uvars) from rfl) hp
    (by rw [SimplePattern.iota_headConst]; exact (VExpr.const.inj hn).1.symm.trans hvn.symm)

end Lean4Lean.VEnv.Strengthening.PureObservation

namespace Lean4Lean.VEnv.Strengthening.RegisteredStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]

/-- Registry-selected structure equations are disjoint from all stored constant
unfoldings, independently of the universe lists used by either occurrence. -/
theorem Unfolds.no_ofEnv (H : Unfolds name levels rhs)
    (H' : (Definitions.ofEnv env univs henv).unfolds name levels' rhs') : False := by
  cases H with
  | intro hreg hw hl hi hx hz hp hc =>
    obtain ⟨hr, hname⟩ := recursorData_registered hreg
    rcases pat_recursor hp with ⟨data', hr', hn', _, hreg', howner, _⟩ | ⟨hq, hn, _⟩
    · rw [hname, hreg] at hreg'
      cases hreg'
      exact Definitions.ofEnv_no_registered henv hr howner (hname ▸ H')
    · rw [hname] at hn
      rw [hn, recursorData_quot hq] at hreg
      cases hreg

/-- The union of actual stored definitions and registry-selected structure
programs is deterministic at fixed universes. -/
theorem definitions_ofEnv_unique
    (H1 : (definitions (Definitions.ofEnv env univs henv)).unfolds name levels rhs1)
    (H2 : (definitions (Definitions.ofEnv env univs henv)).unfolds name levels rhs2) :
    rhs1 = rhs2 := by
  rcases H1 with H1 | H1 <;> rcases H2 with H2 | H2
  · exact Definitions.ofEnv_unique henv H1 H2
  · exact (H2.no_ofEnv H1).elim
  · exact (H1.no_ofEnv H2).elim
  · exact H1.unique H2

end Lean4Lean.VEnv.Strengthening.RegisteredStructure
