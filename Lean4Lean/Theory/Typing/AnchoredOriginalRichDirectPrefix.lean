import Lean4Lean.Theory.Typing.AnchoredOriginalRichExposureStep

/-! A non-lambda original endpoint cannot acquire the synthetic lambda Pi
conversion while exposing its head. This classification follows the actual
original derivation; it is not an extra eligibility premise on an application. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

def EndpointState.DirectPrefix : EndpointState env U source expression assigned → Prop
  | .convert (.piDomain ..) _ => False
  | .convert (.forward ..) term => term.DirectPrefix
  | .convert (.backward ..) term => term.DirectPrefix
  | _ => True

theorem Derivation.expose_directPrefix
    (original : Derivation env U source left right assigned) :
    ((∀ A body, left ≠ .lam A body) → original.expose.1.DirectPrefix) ∧
    ((∀ A body, right ≠ .lam A body) → original.expose.2.DirectPrefix) := by
  induction original with
  | symm original ih => exact ih.symm
  | trans first second firstIH secondIH => exact ⟨firstIH.1, secondIH.2⟩
  | lamDF =>
    constructor <;> intro notLam <;> exact False.elim (notLam _ _ rfl)
  | eta _ _ _ _ _ term _ _ _ _ _ ih _ _ =>
    constructor
    · intro notLam; exact False.elim (notLam _ _ rfl)
    · exact ih.1
  | beta _ _ _ _ _ _ _ instantiated _ _ _ _ _ ih => exact ⟨fun _ => trivial, ih.1⟩
  | proofIrrel _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra _ _ _ _ _ _ _ left right _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | elimIota _ _ _ _ _ _ _ left right _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | projIota _ projection _ field ihProjection ihField => exact ⟨ihProjection.1, ihField.1⟩
  | structEta _ _ _ major constructor ihMajor ihConstructor => exact ⟨ihConstructor.1, ihMajor.1⟩
  | unitLike _ _ _ _ left right ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | _ => constructor <;> intro _ <;> simp [expose, EndpointState.DirectPrefix]

theorem EndpointRef.expose_directPrefix
    (reference : EndpointRef env U source expression assigned)
    (notLam : ∀ A body, expression ≠ .lam A body) : reference.expose.DirectPrefix := by
  cases reference with
  | left original => exact original.expose_directPrefix.1 notLam
  | right original => exact original.expose_directPrefix.2 notLam

end Lean4Lean.AnchoredSource.OriginalClosureMeasure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- A finite route whose conversions are actual equality references. The
Pi-domain conversion is excluded by the original non-lambda shape proof. -/
inductive DirectPrefixRoute (sourceEnv : VEnv) (U : Nat) (source : List VExpr) (expression : VExpr) :
    {A B : VExpr} → EndpointState sourceEnv U source expression A →
      EndpointState sourceEnv U source expression B → Type where
  | done (node) : DirectPrefixRoute sourceEnv U source expression node node
  | expose (reference : EndpointRef sourceEnv U source expression A)
      (rest : DirectPrefixRoute sourceEnv U source expression reference.expose last) :
      DirectPrefixRoute sourceEnv U source expression (.ref reference) last
  | forward (levelWF : level.WF U) (original : Derivation sourceEnv U source A B (.sort level))
      (term : EndpointState sourceEnv U source expression A)
      (rest : DirectPrefixRoute sourceEnv U source expression term last) :
      DirectPrefixRoute sourceEnv U source expression (.convert (.forward levelWF original) term) last
  | backward (levelWF : level.WF U) (original : Derivation sourceEnv U source A B (.sort level))
      (term : EndpointState sourceEnv U source expression B)
      (rest : DirectPrefixRoute sourceEnv U source expression term last) :
      DirectPrefixRoute sourceEnv U source expression (.convert (.backward levelWF original) term) last

def DirectPrefixRoute.toRoute (route : DirectPrefixRoute sourceEnv U source expression first last) :
    PrefixRoute sourceEnv U source expression first last :=
  match route with
  | .done node => .done node
  | .expose reference rest => .expose reference rest.toRoute
  | .forward wf original term rest => .convert (.forward wf original) term rest.toRoute
  | .backward wf original term rest => .convert (.backward wf original) term rest.toRoute

theorem PrefixRoute.direct
    (route : PrefixRoute sourceEnv U source expression first last)
    (notLam : ∀ A body, expression ≠ .lam A body)
    (start : first.DirectPrefix) : Nonempty (DirectPrefixRoute sourceEnv U source expression first last) := by
  induction route with
  | done node => exact ⟨.done node⟩
  | expose reference rest ih =>
    obtain ⟨next⟩ := ih (reference.expose_directPrefix notLam)
    exact ⟨.expose reference next⟩
  | convert plan term rest ih =>
    cases plan with
    | forward wf original =>
      obtain ⟨next⟩ := ih (by simpa [EndpointState.DirectPrefix] using start)
      exact ⟨.forward wf original term next⟩
    | backward wf original =>
      obtain ⟨next⟩ := ih (by simpa [EndpointState.DirectPrefix] using start)
      exact ⟨.backward wf original term next⟩
    | piDomain => exact False.elim start

/-- Every original application prefix satisfies the direct classification. -/
theorem PrefixRoute.applicationDirect
    {reference : EndpointRef sourceEnv U source (.app f a) assigned}
    (route : PrefixRoute sourceEnv U source (.app f a) (.ref reference) last) :
    Nonempty (DirectPrefixRoute sourceEnv U source (.app f a) (.ref reference) last) :=
  route.direct (fun _ _ equal => by cases equal) trivial

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
