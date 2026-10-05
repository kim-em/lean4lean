import Lean4Lean.Theory.Typing.ChurchRosser

/-! Concrete native delta patterns of ordinary definitions. The right-hand
side is the actual installed value, and lookup fixes one value per name. -/

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {value : VDefVal}

/-- Both the constant and its exact defining equation were installed. -/
def DefinitionRegistered (env : VEnv) (value : VDefVal) : Prop :=
  env.constants value.name = some value.toVConstant ∧ env.defeqs value.toDefEq

theorem DefinitionRegistered.mono (H : DefinitionRegistered env value) (hle : env ≤ env') :
    DefinitionRegistered env' value := ⟨hle.constants H.1, hle.defeqs H.2⟩

theorem DefinitionRegistered.of_addConst
    (H : env.addConst value.name value.toVConstant = some extended) :
    DefinitionRegistered (extended.addDefEq value.toDefEq) value :=
  ⟨by simpa only [VEnv.addDefEq] using VEnv.addConst_self H, Or.inl rfl⟩

theorem DefinitionRegistered.closed (henv : env.WF)
    (H : DefinitionRegistered env value) : value.value.Closed := by
  have hw := (henv.ordered.defEqWF H.2).2
  exact VExpr.WF.closedN henv.ordered ⟨_, hw⟩ (by trivial)

/-- Actual definition values produce constant-head delta patterns. -/
inductive DefinitionPattern (registry : Name → Option VDefVal) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | intro {value : VDefVal} (hlookup : registry value.name = some value)
      (hclosed : value.value.Closed) :
      DefinitionPattern registry (.const value.name) (.fixed value.value hclosed, .true)

namespace DefinitionPattern

variable {registry : Name → Option VDefVal}

theorem simple (H : DefinitionPattern registry p rhs) :
    ∃ shape : SimplePattern, p = shape.toPattern := by
  cases H with | intro _ _ => exact ⟨.defn _, rfl⟩

theorem origin
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs) : NativePatternOrigin env p := by
  cases H with
  | @intro value hl hc =>
    exact ⟨value.toDefEq, value.name, VLevel.params value.uvars,
      (hregistry _ _ hl).2, rfl, rfl⟩

theorem not_iota (H : DefinitionPattern registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) : False := by
  cases H

theorem unique (H : DefinitionPattern registry p rhs)
    (H' : DefinitionPattern registry q rhs') (hs : Subpattern sub p)
    (hi : q.inter sub = some intersection) : p = q ∧ q = sub ∧ rhs ≍ rhs' := by
  cases H with
  | @intro value hl hc =>
    cases H' with
    | @intro value' hl' hc' =>
      cases hs
      simp only [Pattern.inter] at hi
      split at hi <;> try contradiction
      rename_i hname
      have hn : value'.name = value.name := by simpa using hname
      rw [hn] at hl'
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl, HEq.rfl⟩

theorem no_app_subpattern (H : DefinitionPattern registry p rhs)
    (hs : Subpattern (.app fn arg) p) : False := by
  cases H
  cases hs

/-- Soundness uses the installed equation at the occurrence's actual
universe list, recovered from its typing and constant lookup. -/
theorem sound (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hregistry : ∀ name value, registry name = some value → DefinitionRegistered env value)
    (H : DefinitionPattern registry p rhs)
    (hm : p.Matches expr levels values) (ht : env.HasType U Γ expr type) :
    env.IsDefEqU U Γ expr (rhs.1.apply levels values) := by
  cases H with
  | @intro value hl hc =>
    cases hm
    obtain ⟨constant, hconstant, hlevels, hlength⟩ := ht.const_inv henv.ordered hΓ
    have hregistered := hregistry _ _ hl
    cases Option.some.inj (hconstant.symm.trans hregistered.1)
    have he := IsDefEq.extra (Γ := Γ) hregistered.2 hlevels hlength
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength,
      Pattern.RHS.apply] using (show env.IsDefEqU U Γ _ _ from ⟨_, he⟩)

/-- Every actual definition equation has a concrete one-step native trace;
there are no captured terms or additional equality guards. -/
theorem equation_trace (hlookup : registry value.name = some value)
    (hclosed : value.value.Closed) (hlength : levels.length = value.uvars) :
    NativeReductionTrace env U (DefinitionPattern registry) Γ
      (value.toDefEq.lhs.instL levels) (value.toDefEq.rhs.instL levels) := by
  simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hlength]
  exact .native (DefinitionPattern.intro hlookup hclosed) .const trivial

end DefinitionPattern
end Lean4Lean.VEnv
