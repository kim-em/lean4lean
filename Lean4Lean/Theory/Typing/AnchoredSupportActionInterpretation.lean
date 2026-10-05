import Lean4Lean.Theory.Typing.AnchoredSupportAction
import Lean4Lean.Theory.Typing.AnchoredViewInterpretation

/-! Interpret finite support actions in all actual private and future worlds.
The output case reuses the retained Pi display and its original row admission. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

def PiWitness.outputSupport
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ} (action : SupportAction env U registry Δ n)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (action.apply profile))
    {Γ : List VExpr} {left right A B : VExpr} {key : Key n}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (action : SupportAction env U registry Γ n)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B domain (outputRows key action.apply rows) := by
  refine { display with rowDomains := ?_, rowBodies := ?_ }
  · intro k result hm
    rcases mem_outputRows.mp hm with old | ⟨rfl, oldResult, old, rfl⟩
    · exact display.rowDomains k result old
    · exact display.rowDomains k oldResult old
  · intro k result hm Δ ρ future x y admitted
    rcases mem_outputRows.mp hm with old | ⟨rfl, oldResult, old, rfl⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · have insertion := display.leftExposure.insertion henv
      let action' := (action.mixed henv insertion).future henv future
      obtain ⟨hl, hr, hc⟩ := display.rowBodies k oldResult old Δ ρ future x y admitted
      have hl' := lowerCode action' hl
      have hr' := lowerCode action' hr
      have hc' := lowerCode action' hc
      simpa only [action', Profile.rename_comp, ← SupportAction.apply_future,
        ← SupportAction.apply_mixed, TypeRelated] using And.intro hl' (And.intro hr' hc')

theorem TypeRelated.outputSupportWith
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ} (action : SupportAction env U registry Δ n)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (action.apply profile))
    {Γ : List VExpr} {left right : VExpr} {key : Key n}
    {profile : Profile (n + 1)} (action : SupportAction env U registry Γ n)
    (code : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (outputTypes key action.apply profile) := by
  intro Δ ρ future atom ha
  rw [outputTypes_rename key action.apply (action.future henv future).apply
    (fun p => action.apply_future henv future p)] at ha
  obtain ⟨oldAtom, hm, rfl⟩ := List.mem_map.mp ha
  have hc := code Δ ρ future oldAtom hm
  cases oldAtom with
  | sort relevant => exact hc
  | family _ | ctor _ | record _ => exact hc
  | fn k output => exact False.elim hc
  | pad lowerAtom => exact hc
  | pi A B domain rows =>
    obtain ⟨display⟩ := hc
    exact ⟨display.outputSupport henv lowerCode (action.future henv future)⟩

theorem SupportAction.codeMap
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (action : SupportAction env U registry Γ n)
    (code : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (action.apply profile) := by
  match n, action with
  | _, .id => exact code
  | _, .flatSorts => exact code.flatSorts henv
  | _, .view v => exact v.codeMap henv hscoped code
  | _ + 1, .output key child =>
    exact code.outputSupportWith henv (fun {_} action {_ _ _} code => action.codeMap henv hscoped code) child
  | _ + 1, .pad child => exact (child.codeMap henv hscoped (code.down henv)).pad henv
  | _, .comp first second => exact second.codeMap henv hscoped (first.codeMap henv hscoped code)
  | _, .union first second =>
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => (first.codeMap henv hscoped code).singleton h)
      (fun h => (second.codeMap henv hscoped code).singleton h)
termination_by (n, sizeOf action)
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSemantics
