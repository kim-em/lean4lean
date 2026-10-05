import Lean4Lean.Theory.Typing.AnchoredAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredProfileViewInterpretation

/-! Embed the existing guarded views at canonical adapter endpoints. Rank
padding is lifted structurally through the finite normal form; all altered
seed and domain guards are produced by the already checked view interpreter. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def ProfileView.compose
    (first : ProfileView env U registry Γ p q)
    (second : ProfileView env U registry Γ q r) :
    ProfileView env U registry Γ p r := by
  match first, second with
  | .nil, .nil => exact .nil
  | .cons first tail₁, .cons second tail₂ =>
    exact .cons (.trans first second) (tail₁.compose tail₂)
termination_by sizeOf first
decreasing_by simp_wf; omega

def ProfileView.padAll (view : ProfileView env U registry Γ p q) :
    ProfileView env U registry Γ p.pad q.pad := by
  match view with
  | .nil => exact .nil
  | .cons head tail => exact .cons (.pad head) tail.padAll
termination_by sizeOf view
decreasing_by simp_wf; omega

private theorem viewAdmission
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {key : Key n} (view : ProfileView env U registry Γ key.input input)
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (inputKey key input) x y :=
  view.admissionMapWith hΓ (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) admitted

namespace AdapterNormal

noncomputable def shiftedProfileView (henv : env.Ordered)
    (change : ProfileView env U registry Γ p q) :
    ProfileView env U registry Γ (shiftProfile p) (shiftProfile q) :=
  ((shiftProfileView (U := U) (registry := registry) (Γ := Γ) henv p).inverse henv).compose
    (change.padAll.compose (shiftProfileView henv q))

noncomputable def normalizedProfileView (henv : env.Ordered)
    (change : ProfileView env U registry Γ p q) :
    ProfileView env U registry Γ (profile p) (profile q) :=
  ((profileView (U := U) (registry := registry) (Γ := Γ) henv p).inverse henv).compose
    (change.compose (profileView henv q))

theorem shiftAdmission
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {key : Key n} (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (shiftKey key) x y := by
  exact viewAdmission henv hscoped hΓ (shiftProfileView henv key.input)
    (Admitted.pad henv admitted)

theorem normalizeAdmission
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {k : Key n} (admitted : Admitted env U registry Γ k x y) :
    Admitted env U registry Γ (key k) x y :=
  viewAdmission henv hscoped hΓ (profileView henv k.input) admitted

end AdapterNormal

noncomputable def AdapterSeed.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (seed : AdapterSeed env U registry Γ key input) :
    AdapterSeed env U registry Γ (AdapterNormal.shiftKey key) (AdapterNormal.shiftProfile input) := by
  match seed with
  | .same => exact .same
  | .supplied admitted => exact .supplied (AdapterNormal.shiftAdmission henv hscoped hΓ admitted)
  | .view previous change =>
    exact .view (previous.shift henv hscoped hΓ) (AdapterNormal.shiftedProfileView henv change)
termination_by sizeOf seed
decreasing_by simp_wf; omega

mutual
noncomputable def AtomAdapter.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (adapter : AtomAdapter env U registry Γ a b) :
    AtomAdapter env U registry Γ (AdapterNormal.shiftAtom a) (AdapterNormal.shiftAtom b) := by
  match n, a, b, adapter with
  | _, _, _, .refl value => exact .refl _
  | _ + 1, _, _, .fn keys output =>
    exact .fn (keys.shift henv hscoped hΓ) (output.shift henv hscoped hΓ)
  | _ + 1, _, _, .pad adapter => exact .pad (.pad adapter)
termination_by (3 * n, 0)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileAdapter.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (adapter : ProfileAdapter env U registry Γ p q) :
    ProfileAdapter env U registry Γ (AdapterNormal.shiftProfile p) (AdapterNormal.shiftProfile q) := by
  match adapter with
  | .nil _ => exact .nil _
  | .cons member head tail =>
    exact .cons (List.mem_map.mpr ⟨_, member, rfl⟩)
      (head.shift henv hscoped hΓ) (tail.shift henv hscoped hΓ)
termination_by (3 * n + 1, sizeOf adapter)
decreasing_by all_goals simp_wf; omega

noncomputable def KeyProgram.shift
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {old new : Key n} (program : KeyProgram env U registry Γ old new) :
    KeyProgram env U registry Γ (AdapterNormal.shiftKey old) (AdapterNormal.shiftKey new) := by
  match program with
  | .refl _ => exact .refl _
  | .input seed arguments => exact .input (seed.shift henv hscoped hΓ) (arguments.shift henv hscoped hΓ)
  | .reanchor admitted => exact .reanchor (AdapterNormal.shiftAdmission henv hscoped hΓ admitted)
  | .domainRekey path typed formed bridge =>
    let view := AdapterNormal.shiftProfileView (U := U) (registry := registry) (Γ := Γ) henv old.input
    exact .domainRekey path (view.mapType_typed typed.pad)
      (view.mapType_sort formed.pad_sort) (view.codeMap henv hscoped (bridge.pad henv))
  | .comp first second => exact .comp (first.shift henv hscoped hΓ) (second.shift henv hscoped hΓ)
termination_by (3 * n + 2, sizeOf program)
decreasing_by all_goals simp_wf; omega
end

mutual
noncomputable def AtomView.toAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (view : AtomView env U registry Γ a b) :
    NormalAtomAdapter env U registry Γ a b := by
  match n, a, b, view with
  | _, _, _, .refl _ => exact .refl _
  | _ + 1, _, _, .reanchor admitted =>
    exact .fn (.reanchor (AdapterNormal.normalizeAdmission henv hscoped hΓ admitted)) (.refl _)
  | _ + 1, _, _, @AtomView.domainRekey _ _ _ _ _ key _ _ _ path typed formed bridge =>
    let inputs := AdapterNormal.profileView (U := U) (registry := registry) (Γ := Γ) henv key.input
    exact .fn (.domainRekey path (inputs.mapType_typed typed) (inputs.mapType_sort formed)
      (inputs.codeMap henv hscoped bridge)) (.refl _)
  | _ + 1, _, _, .input forward backward =>
    exact .fn (.input (.view .same (AdapterNormal.normalizedProfileView henv backward))
      (forward.toAdapter henv hscoped hΓ)) (.refl _)
  | _ + 2, _, _, .commutePadFn key output =>
    rw [NormalAtomAdapter, AdapterNormal.atom_commutePadFn]
    exact .refl _
  | _ + 2, _, _, .uncommutePadFn key output =>
    rw [NormalAtomAdapter, AdapterNormal.atom_commutePadFn]
    exact .refl _
  | _ + 1, _, _, .fn key output =>
    exact .fn (.refl (AdapterNormal.key key)) (output.toAdapter henv hscoped hΓ)
  | _ + 1, _, _, .pad view => exact AtomAdapter.shift henv hscoped hΓ (view.toAdapter henv hscoped hΓ)
  | _, _, _, .trans first second =>
    exact AtomAdapter.comp (first.toAdapter henv hscoped hΓ) (second.toAdapter henv hscoped hΓ)
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

noncomputable def ProfileView.toAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {p q : Profile n} (view : ProfileView env U registry Γ p q) :
    ProfileAdapter env U registry Γ (AdapterNormal.profile p) (AdapterNormal.profile q) := by
  match view with
  | .nil => exact .nil _
  | .cons head tail =>
    have rest := tail.toAdapter henv hscoped hΓ
    -- The tail keeps its original origins after the new head is prefixed.
    let rec extend {source target : Profile n} (adapter : ProfileAdapter env U registry Γ source target)
        (extra : Atom n) : ProfileAdapter env U registry Γ (extra :: source) target :=
      match adapter with
      | .nil _ => .nil _
      | .cons member entry rest => .cons (List.mem_cons_of_mem _ member) entry (extend rest extra)
    exact .cons List.mem_cons_self (head.toAdapter henv hscoped hΓ)
      (extend rest _)
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega
end

end Lean4Lean.AnchoredSemantics
