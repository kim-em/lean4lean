import Lean4Lean.Theory.Typing.AnchoredPadding

/-! Literal universe capabilities enforce the intrinsic proof/data flag.
This derives sort correctness from the actual assigned-type capability,
including explicit padding and proof-saturated term observations. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Relevant.unique (first : Relevant level a) (second : Relevant level b) : a = b := by
  cases a <;> cases b <;> simp_all [Relevant]

private theorem literalSort_trace
    (trace : CanonicalDataHead.Trace registry (.sort level) added result) :
    added = [] ∧ result = .sort level := by
  cases trace with
  | refl => exact ⟨rfl, rfl⟩
  | next step _ => simp only [CanonicalDataHead.step_sort] at step; contradiction

theorem Exposure.literalSort_head
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {head : VExpr} {level : VLevel}
    (E : Exposure env U registry Γ (.sort level) Δ ρ head) : head = .sort level := by
  have shape := literalSort_trace E.trace
  have he := E.result_eq
  rw [shape.2] at he
  exact he.symm

theorem SortRelated.literal_relevant
    (H : SortRelated env U registry Γ (.sort level) right relevant) :
    Relevant level relevant := by
  obtain ⟨Δ, ρ, u, v, ⟨E⟩, _, _, hu⟩ := H
  have he := VExpr.sort.inj E.literalSort_head
  exact he ▸ hu

theorem TypeRelated.sort_typed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {level : VLevel} {relevant : Bool}
    (hΓ : OnCtx Γ (env.IsType U)) (flag : Relevant level relevant)
    {value support : Profile n}
    (code : TypeRelated env U registry Γ (.sort level) (.sort level) support)
    (typed : value.HasType support) : value.HasType (.sort relevant) := by
  induction n generalizing Γ with
  | zero =>
    intro atom member
    obtain ⟨cover, hm, ht⟩ := typed atom member
    have capability := code Γ .refl (.refl hΓ) cover
      (by simpa only [Profile.rename_refl] using hm)
    simp only [lift'_refl] at capability
    have he := Relevant.unique capability.literal_relevant flag
    change cover = true at ht
    exact ⟨relevant, List.mem_singleton_self _, he ▸ ht⟩
  | succ n ih =>
    refine ⟨typed.wf_value, Profile.WF.sort (n := n + 1) relevant, ?_⟩
    intro atom member
    obtain ⟨cover, hm, ht⟩ := typed.2.2 atom member
    have capability := code Γ .refl (.refl hΓ) cover
      (by simpa only [Profile.rename_refl] using hm)
    simp only [lift'_refl] at capability
    cases cover with
    | sort r =>
      have he := Relevant.unique (SortRelated.literal_relevant capability) flag
      subst r
      exact ⟨.sort relevant, List.mem_singleton_self _, ht⟩
    | fn | ctor | record => exact capability.elim
    | family demand =>
      obtain ⟨display⟩ := capability
      have impossible := display.leftExposure.literalSort_head
      have head := congrArg (fun expression => expression.getAppFnArgs.1) impossible
      have familyHead := VExpr.getAppFnArgs_mkApps_head
        (.const demand.name display.leftLevels) display.leftArguments
      rw [familyHead] at head
      contradiction
    | pi A B domain rows =>
      obtain ⟨display⟩ := capability
      have impossible := display.leftExposure.literalSort_head
      contradiction
    | pad lower =>
      cases atom with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad atom =>
        exact ⟨.sort relevant, List.mem_singleton_self _, ih hΓ capability ht⟩

end Lean4Lean.AnchoredSemantics
