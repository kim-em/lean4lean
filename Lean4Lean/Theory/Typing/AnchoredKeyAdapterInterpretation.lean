import Lean4Lean.Theory.Typing.AnchoredAdapters
import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredProfileViewInterpretation
import Lean4Lean.Theory.Typing.AnchoredInputAdmission

/-! A finite key program transports actual self-admissions forward and pulls
admitted arguments backward. Intermediate supports come from those concrete
admissions, never from a requested intermediate function type capability. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem AdapterSeed.admission
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {input : Profile n}
    (next : AdapterSeed env U registry Γ key input)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (seed : Admitted env U registry Γ key key.anchor key.anchor) :
    Admitted env U registry Γ (inputKey key input) key.anchor key.anchor := by
  match next with
  | .same => exact seed
  | .supplied admitted => exact admitted
  | @AdapterSeed.view _ _ _ _ _ _ middle _ previous change =>
    exact ProfileView.admissionMapWith (key := inputKey key middle) change hΓ
      (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
      (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h)
      (previous.admission henv hscoped hΓ seed)
termination_by sizeOf next
decreasing_by simp_wf; omega

theorem KeyProgram.forward
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key newKey : Key n}
    (keys : KeyProgram env U registry Γ key newKey) (henv : env.Ordered)
    (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (seed : Admitted env U registry Γ key key.anchor key.anchor) :
    Admitted env U registry Γ newKey newKey.anchor newKey.anchor := by
  match keys with
  | .refl _ => exact seed
  | .input next _ => exact next.admission henv hscoped hΓ seed
  | .reanchor admitted => exact admitted.reset_anchor
  | .domainRekey path typed formed bridge =>
    exact seed.rekey henv path typed formed bridge
  | .comp first second => exact second.forward henv hscoped hΓ (first.forward henv hscoped hΓ seed)
termination_by sizeOf keys
decreasing_by all_goals simp_wf; omega

/-- Internal smaller-rank interpretation step. The public closed operation
is `KeyProgram.pull` in `AnchoredAdapterInterpretation`. -/
theorem KeyProgram.pullWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key newKey : Key n}
    (keys : KeyProgram env U registry Γ key newKey)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U))
    (lower : ∀ {p q : Profile n}, ProfileAdapter env U registry Γ p q →
      ∀ {l r A : VExpr} {old new : Profile n}, q.HasType new →
      TypeRelated env U registry Γ A A new → Related env U registry Γ l r A p old →
      Related env U registry Γ l r A q new)
    (seed : Admitted env U registry Γ key key.anchor key.anchor)
    (admitted : Admitted env U registry Γ newKey x y) :
    Admitted env U registry Γ key x y := by
  match keys with
  | .refl _ => exact admitted
  | .input _ arguments =>
    obtain ⟨_, _, support, typed, formed, code, _, _⟩ := seed
    obtain ⟨raw, pair, _, _, _, _, first, second⟩ := admitted
    exact ⟨raw, pair, support, typed, formed, code,
      lower arguments typed code first, lower arguments typed code second⟩
  | .reanchor anchor => exact Admitted.prepend_anchor henv hscoped anchor admitted
  | @KeyProgram.domainRekey _ _ _ _ _ _ newDomain _ path typed formed bridge =>
    have reversed := Admitted.rekey (key := domainKey key newDomain) henv path.symm typed formed
      (bridge.symm henv typed.wf_type) admitted
    simpa only [domainKey] using reversed
  | .comp first second =>
    exact first.pullWith henv hscoped hΓ lower seed
      (second.pullWith henv hscoped hΓ lower (first.forward henv hscoped hΓ seed) admitted)
termination_by sizeOf keys
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSemantics
