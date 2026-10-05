import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpine
import Lean4Lean.Theory.Typing.AnchoredGradedAdapters

/-! Backward preparation of a finite rigid-family spine. The actual packed
application supplies the key, its domain support, and the paired argument
admission. The result uses that same key and exact outer rank raising. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace RigidFamilySpine

/-- The remaining earlier frozen arguments have not been chosen yet. Typing
is uniform in that finite prefix, so preparation can proceed backwards from
the terminal sort certificate before constructing the final family atom. -/
structure Prepared (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (name : Name) (levels : List VLevel) (support : Profile n) where
  plan : RigidFamilySpine n
  ready : plan.Ready env U registry Γ
  typed : ∀ past, (Profile.singleton (plan.atom name levels past)).HasType support

/-- Every frozen terminal request has empty profiles; raw argument equality
is supplied later by the semantic interpreter's actual runtime accumulator. -/
theorem terminal_typed (name : Name) (levels : List VLevel) (relevant : Bool)
    (past : List RigidFamilyArgument) :
    (Profile.singleton ((RigidFamilySpine.terminal relevant).atom name levels past)).HasType
      (.sort relevant) := by
  refine ⟨?_, Profile.WF.sort (n := 1) relevant, ?_⟩
  · intro atom member
    cases List.mem_singleton.mp member
    change ∀ request ∈ past.map RigidFamilyArgument.request,
      request.input.WF ∧ request.support.WF
    intro request member
    obtain ⟨argument, _, rfl⟩ := List.mem_map.mp member
    exact ⟨Profile.WF.empty, Profile.WF.empty⟩
  · intro atom member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, rfl⟩

def Prepared.terminal (relevant : Bool) :
    Prepared env U registry Γ name levels (Profile.sort (n := 1) relevant) where
  plan := .terminal relevant
  ready := trivial
  typed := terminal_typed name levels relevant

/-- This is the same self-guard used by ordinary fn queries, extracted from
the actual paired argument admission returned by the application packer. -/
theorem anchorAdmission (admitted : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ key key.anchor key.anchor := by
  obtain ⟨raw, _, support, typed, formed, code, anchor, _⟩ := admitted
  change Related env U registry Γ key.anchor left key.domain key.input support at anchor
  exact ⟨raw.hasType.1, raw.hasType.1, support, typed, formed, code,
    anchor.left_diagonal, anchor.left_diagonal⟩

/-- Exact rank raising retains both the finite key guards and the universal
prefix typing needed by a later, earlier application in the actual spine. -/
def Prepared.raise
    (before : Prepared env U registry Γ name levels (support : Profile n))
    (bound : n ≤ N) :
    Prepared env U registry Γ name levels (raiseProfile N bound support) where
  plan := before.plan.raise N bound
  ready := before.plan.ready_raise bound before.ready
  typed := by
    intro past
    rw [before.plan.profile_raise]
    exact Profile.HasType.raise bound (before.typed past)

/-- One actual packed application prepends its SAME key. No family observer,
header shape, current comparison answer, or supplied Pi semantic witness is
an input. The support is exactly the packer's singleton whole-Pi profile. -/
def Prepared.prepend
    (before : Prepared env U registry Γ name levels (support : Profile n))
    (bound : n ≤ N) (key : Key N) (domainSupport : Profile N)
    (inputTyped : key.input.HasType domainSupport)
    (domainFormed : domainSupport.HasType (.sort true))
    (admitted : Admitted env U registry Γ key left right)
    (A B : VExpr) :
    Prepared env U registry Γ name levels
      (Profile.pi A B domainSupport [(key, raiseProfile N bound support)]) where
  plan := .binder key (before.plan.raise N bound)
  ready := ⟨anchorAdmission admitted, before.plan.ready_raise bound before.ready⟩
  typed := by
    intro past
    have childTyped := (before.raise bound).typed
      (past ++ [⟨key.domain, key.anchor⟩])
    apply Profile.HasType.fn ?_ (List.mem_singleton_self _) childTyped
    apply Profile.WF.pi_iff.mpr
    refine ⟨domainFormed, ?_⟩
    intro selected result member
    cases List.mem_singleton.mp member
    exact ⟨inputTyped, childTyped.wf_type⟩

@[simp] theorem Prepared.prepend_plan
    (before : Prepared env U registry Γ name levels (support : Profile n))
    (bound : n ≤ N) (key : Key N) (domainSupport : Profile N)
    (inputTyped : key.input.HasType domainSupport)
    (domainFormed : domainSupport.HasType (.sort true))
    (admitted : Admitted env U registry Γ key left right) (A B : VExpr) :
    (before.prepend bound key domainSupport inputTyped domainFormed admitted A B).plan =
      .binder key (before.plan.raise N bound) := rfl

end RigidFamilySpine
end Lean4Lean.AnchoredSemantics
