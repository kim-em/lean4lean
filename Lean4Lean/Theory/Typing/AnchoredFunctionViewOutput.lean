import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

/-! A reversible function view retains an actual reversible output view.
This is stronger than its adapter projection, and permits source beta replay
to transform the original body certificate without inventing endpoint code. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem shift_fn_inv {a : Atom (n + 1)} {key : Key (n + 1)}
    {output : Atom (n + 1)} (h : AdapterNormal.shiftAtom a = .fn key output) :
    ∃ k o, a = .fn k o ∧ key = AdapterNormal.shiftKey k ∧
      output = AdapterNormal.shiftAtom o := by
  cases a with
  | sort | pi | pad | family | ctor | record => cases h
  | fn k o =>
    have h := AtomData.fn.inj h
    exact ⟨k, o, rfl, h.1.symm, h.2.symm⟩

/-- The only changes made outside a function's output are guarded key
changes. Padding is normalized by the existing concrete shift views. -/
theorem AtomView.normal_fn_output
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom (n + 1)} (view : AtomView env U registry Γ a b)
    {leftKey rightKey : Key n} {leftOutput rightOutput : Atom n}
    (left : AdapterNormal.atom a = .fn leftKey leftOutput)
    (right : AdapterNormal.atom b = .fn rightKey rightOutput) :
    Nonempty (AtomView env U registry Γ leftOutput rightOutput) := by
  match n, a, b, view with
  | _, _, _, .refl _ =>
    have he := (AtomData.fn.inj (left.symm.trans right)).2
    exact ⟨he ▸ .refl _⟩
  | _, _, _, .reanchor _ =>
    have he := (AtomData.fn.inj left).2.symm.trans (AtomData.fn.inj right).2
    exact ⟨he ▸ .refl _⟩
  | _, _, _, .domainRekey .. =>
    have he := (AtomData.fn.inj left).2.symm.trans (AtomData.fn.inj right).2
    exact ⟨he ▸ .refl _⟩
  | _, _, _, .input .. =>
    have he := (AtomData.fn.inj left).2.symm.trans (AtomData.fn.inj right).2
    exact ⟨he ▸ .refl _⟩
  | _, _, _, .commutePadFn k o =>
    have he := left.symm.trans ((AdapterNormal.atom_commutePadFn k o).trans right)
    exact ⟨(AtomData.fn.inj he).2 ▸ .refl _⟩
  | _, _, _, .uncommutePadFn k o =>
    have he := left.symm.trans ((AdapterNormal.atom_commutePadFn k o).symm.trans right)
    exact ⟨(AtomData.fn.inj he).2 ▸ .refl _⟩
  | _, _, _, .fn k change =>
    have hl := (AtomData.fn.inj left).2
    have hr := (AtomData.fn.inj right).2
    cases hl
    cases hr
    exact ⟨.trans ((AdapterNormal.view henv _).inverse henv)
      (.trans change (AdapterNormal.view henv _))⟩
  | 0, _, _, .pad change => cases left
  | n + 1, _, _, .pad change =>
    obtain ⟨lk, lo, hl, rfl, rfl⟩ := shift_fn_inv left
    obtain ⟨rk, ro, hr, rfl, rfl⟩ := shift_fn_inv right
    obtain ⟨output⟩ := change.normal_fn_output henv hscoped hΓ hl hr
    exact ⟨.trans ((AdapterNormal.shiftView henv lo).inverse henv)
      (.trans (.pad output) (AdapterNormal.shiftView henv ro))⟩
  | _, _, _, .trans first second =>
    have middle := second.toAdapter henv hscoped hΓ
    change AtomAdapter env U registry Γ _ _ at middle
    rw [right] at middle
    obtain ⟨mk, mo, hm, _, _⟩ := middle.fn_inv
    obtain ⟨a⟩ := first.normal_fn_output henv hscoped hΓ left hm
    obtain ⟨b⟩ := second.normal_fn_output henv hscoped hΓ hm right
    exact ⟨.trans a b⟩
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSemantics
