import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeSeparation
import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaLoop

/-! # Type constraints on recursive-loop eta

The loop's computational terms use three closed types: the recursive domain,
Prop → Prop, and Prop. Their function domains are determined by typing, even
when eta introduces noncanonical annotations. This is the typed information a
loop-separation invariant must retain instead of erasing every annotation.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- The three types used by the recursive diagonal and its result. -/
inductive LoopRole where
  | recursive | function | proposition
  deriving DecidableEq

def LoopRole.type (c : Name) : LoopRole → VExpr
  | .recursive => domain c
  | .function => resultType
  | .proposition => prop

/-- Only the recursive role and the function role admit application. -/
def LoopRole.arrow : LoopRole → Option (LoopRole × LoopRole)
  | .recursive => some (.recursive, .function)
  | .function => some (.proposition, .proposition)
  | .proposition => none

theorem LoopRole.type_closed (r : LoopRole) : (r.type c).Closed := by
  cases r <;> simp [LoopRole.type, domain, resultType, prop, Closed, ClosedN]

variable [Params] {r r' : LoopRole}

/-- All three role types live in Type, including Prop itself as a universe. -/
theorem LoopRole.type_typed (hc : env.constants c = some (declaration c).toVConstant)
    (r : LoopRole) : env.HasType univs Γ (r.type c) (.sort (.succ .zero)) := by
  cases r with
  | recursive => exact domain_typed hc univs Γ
  | function => exact result_typed env univs Γ
  | proposition => exact .sort (by trivial)

/-- None of the computational roles is a proof role. -/
theorem LoopRole.not_proof (hc : env.constants c = some (declaration c).toVConstant)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (r.type c)) :
    ¬ IsProof Γ e := by
  rintro ⟨P, he, hP⟩
  have H := (ht.uniqU henv hΓ he).of_l henv hΓ (r.type_typed hc)
  have Hsort := (H.hasType.2.uniqU henv hΓ hP).sort_inv henv hΓ
  have Hvalue := congrFun Hsort []
  simp [VLevel.eval] at Hvalue

/-- Every displayed Pi typing of a role-typed function has the role's unique
domain and codomain up to conversion. The body equation lives under the actual
displayed domain, so its annotation need not be closed. -/
theorem LoopRole.pi_typing
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (r.type c))
    (hf : env.HasType univs Γ e (.forallE A B)) :
    ∃ a b, r.arrow = some (a, b) ∧
      env.IsDefEqU univs Γ A (a.type c) ∧ env.IsDefEqU univs (A :: Γ) B (b.type c) := by
  cases r with
  | recursive =>
    have hcanon := (hδ Γ).defeq ht
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := (hf.uniqU henv hΓ hcanon).forallE_inv henv hΓ
    exact ⟨.recursive, .function, rfl, ⟨_, hA⟩, ⟨_, hB⟩⟩
  | function =>
    obtain ⟨⟨_, hA⟩, ⟨_, hB⟩⟩ := (hf.uniqU henv hΓ ht).forallE_inv henv hΓ
    exact ⟨.proposition, .proposition, rfl, ⟨_, hA⟩, ⟨_, hB⟩⟩
  | proposition => exact ((ht.uniqU henv hΓ hf).sort_forallE_inv henv hΓ).elim

/-- Registered structure eta cannot apply to a term at any computational role.
All three types have a Pi telescope ending in a sort. -/
theorem LoopRole.not_structure
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (r.type c))
    (hi : env.projections s info)
    (hm : env.HasType univs Γ e (mkApps (.const s ls) args)) : False := by
  cases r with
  | recursive =>
    exact HasType.sortTele_not_rigid hΓ (henv.projectionRigid hi)
      (as := []) (doms := [domain c, prop]) ((hδ Γ).defeq ht) hm
  | function =>
    exact HasType.sortTele_not_rigid hΓ (henv.projectionRigid hi)
      (as := []) (doms := [prop]) ht hm
  | proposition =>
    exact HasType.sortTele_not_rigid hΓ (henv.projectionRigid hi)
      (as := []) (doms := []) ht hm

/-- Unfolding the recursive domain separates it from the proposition universe. -/
theorem domain_not_prop
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs)) : ¬ env.IsDefEqU univs Γ (domain c) prop := by
  intro H
  exact ((H.symm.trans henv hΓ ⟨_, hδ Γ⟩).sort_forallE_inv henv hΓ)

/-- The recursive domain is also distinct from the loop's function result. -/
theorem domain_not_result
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs)) : ¬ env.IsDefEqU univs Γ (domain c) resultType := by
  intro H
  have HPi := (show env.IsDefEqU univs Γ _ _ from ⟨_, (hδ Γ).symm⟩).trans henv hΓ H
  obtain ⟨u, hA⟩ := (HPi.forallE_inv henv hΓ).1
  exact domain_not_prop hδ hΓ ⟨_, hA⟩

/-- A role is determined by its type; eta cannot reinterpret a recursive
argument as a proposition argument or conversely. -/
theorem LoopRole.type_injective
    (hδ : ∀ Δ, env.IsDefEq univs Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEqU univs Γ (r.type c) (r'.type c)) : r = r' := by
  cases r <;> cases r'
  · rfl
  · exact (domain_not_result hδ hΓ H).elim
  · exact (domain_not_prop hδ hΓ H).elim
  · exact (domain_not_result hδ hΓ H.symm).elim
  · rfl
  · exact (H.symm.sort_forallE_inv henv hΓ).elim
  · exact (domain_not_prop hδ hΓ H.symm).elim
  · exact (H.sort_forallE_inv henv hΓ).elim
  · rfl

end Lean4Lean.VEnv.Strengthening.GuardedEta
