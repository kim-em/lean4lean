import Lean4Lean.Theory.Typing.AnchoredRankLaws

/-! Closed hereditary support laws. The rank construction below discharges
every lower-rank hypothesis of the Pi constructors. Public operations take
only finite intrinsic typing certificates and concrete semantic evidence. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

private theorem supportLaws
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (n : Nat) : SupportLaws env U registry n :=
  (rankLaws henv n).toSupportLaws

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {left middle right left' right' : VExpr}
  {value support bound other : Profile n}

theorem TypeRelated.symm (henv : env.Ordered) (hw : support.WF)
    (h : TypeRelated env U registry Γ left right support) :
    TypeRelated env U registry Γ right left support :=
  (supportLaws henv n).symm _ _ _ _ hw h

theorem TypeRelated.focusMinimal (henv : env.Ordered)
    (minimal : Minimal value support) (hle : support ≤ bound)
    (h : TypeRelated env U registry Γ left right bound) :
    TypeRelated env U registry Γ left right support :=
  (supportLaws henv n).focus _ _ _ _ _ _ minimal minimal.typed hle h

theorem TypeRelated.composeMinimal (henv : env.Ordered)
    (minimal : Minimal value support) (typed : value.HasType other)
    (first : TypeRelated env U registry Γ left middle support)
    (second : TypeRelated env U registry Γ middle right other) :
    TypeRelated env U registry Γ left right support :=
  (supportLaws henv n).compose _ _ _ _ _ _ _ minimal typed first second

theorem TypeRelated.transportMinimal (henv : env.Ordered)
    (minimal : Minimal value support) (typed : value.HasType other)
    (first : TypeRelated env U registry Γ left right support)
    (hl : TypeRelated env U registry Γ left left' other)
    (hr : TypeRelated env U registry Γ right right' other) :
    TypeRelated env U registry Γ left' right' support :=
  (supportLaws henv n).transport _ _ _ _ _ _ _ _ minimal typed first hl hr

/-- Select a finite support before composing binary code evidence. The
selection is made from the intrinsic basis, independently of future worlds. -/
theorem TypeRelated.compose_support (henv : env.Ordered)
    (typed : value.HasType support) (typedOther : value.HasType other)
    (first : TypeRelated env U registry Γ left middle support)
    (second : TypeRelated env U registry Γ middle right other) :
    ∃ selected, Minimal value selected ∧ value.HasType selected ∧ selected ≤ support ∧
      TypeRelated env U registry Γ left right selected := by
  obtain ⟨selected, hm⟩ := Basis.exists typed
  obtain ⟨ht, hle⟩ := Basis.valid hm
  have minimal := Basis.minimal hm
  exact ⟨selected, minimal, ht, hle,
    (first.focusMinimal henv minimal hle).composeMinimal henv minimal typedOther second⟩

/-- Replacing a frozen raw domain preserves one finite input support for
EVERY later caller domain. The support is chosen before that caller and its
future contexts, which is required by source eta's frozen function key. -/
theorem TypeRelated.rekey_domain
    (henv : env.Ordered)
    {oldDomain newDomain annotation : VExpr}
    {input oldSupport newSupport : Profile n}
    (oldTyped : input.HasType oldSupport) (newTyped : input.HasType newSupport)
    (newFormation : newSupport.HasType (.sort true))
    (oldLink : TypeRelated env U registry Γ oldDomain annotation oldSupport)
    (newLink : TypeRelated env U registry Γ newDomain annotation newSupport) :
    ∃ selected, Minimal input selected ∧ input.HasType selected ∧
      selected.HasType (.sort true) ∧ selected ≤ newSupport ∧
      ∀ caller callerSupport, input.HasType callerSupport →
        TypeRelated env U registry Γ oldDomain caller callerSupport →
        TypeRelated env U registry Γ newDomain caller selected := by
  obtain ⟨selected, hm⟩ := Basis.exists newTyped
  obtain ⟨ht, hle⟩ := Basis.valid hm
  have minimal := Basis.minimal hm
  have bridge := (newLink.focusMinimal henv minimal hle).composeMinimal henv minimal
    oldTyped (oldLink.symm henv oldTyped.wf_type)
  refine ⟨selected, minimal, ht, newFormation.restrict hle ht.wf_type, hle, ?_⟩
  intro caller callerSupport callerTyped callerLink
  exact bridge.composeMinimal henv minimal callerTyped callerLink

end Lean4Lean.AnchoredSemantics
