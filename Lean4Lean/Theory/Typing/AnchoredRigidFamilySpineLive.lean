import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpinePreparation
import Lean4Lean.Theory.Typing.AnchoredLive

/-! The finite spine's stored anchor admissions are exactly the guards
needed to package its constant observation as a graded result. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false

namespace RigidFamilySpine

theorem Ready.atomLive (plan : RigidFamilySpine n)
    (ready : plan.Ready env U registry Γ)
    (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    Atom.Live env U registry Γ (plan.atom name levels past) := by
  induction plan generalizing past with
  | terminal => trivial
  | binder key child ih => exact ⟨ready.1, ih ready.2 _⟩
  | pad child ih => exact ih ready past

theorem Ready.live (plan : RigidFamilySpine n)
    (ready : plan.Ready env U registry Γ)
    (name : Name) (levels : List VLevel) (past : List RigidFamilyArgument) :
    Profile.Live env U registry Γ (.singleton (plan.atom name levels past)) :=
  Profile.Live.singleton_iff.mpr (ready.atomLive plan name levels past)

theorem Prepared.live
    (prepared : Prepared env U registry Γ name levels support)
    (past : List RigidFamilyArgument) :
    Profile.Live env U registry Γ (.singleton (prepared.plan.atom name levels past)) :=
  prepared.ready.live prepared.plan name levels past

end RigidFamilySpine
end Lean4Lean.AnchoredSemantics
