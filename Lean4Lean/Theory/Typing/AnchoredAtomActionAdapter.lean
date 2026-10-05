import Lean4Lean.Theory.Typing.AnchoredAtomAction
import Lean4Lean.Theory.Typing.AnchoredSourceAdapterCode
import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

/-! Concrete commuting steps for a returned directional adapter and a
subsequent finite action. Sortable leaves normalize by an actual reversible
view before applying the code action. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

structure ActionAfterAdapter (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (context : List VExpr) (raw output : Atom n) where
  actual : Atom n
  action : AtomAction env U registry context raw actual
  adapter : NormalAtomAdapter env U registry context actual output

theorem AtomAction.followCode
    (henv : env.Ordered)
    (adapter : NormalAtomAdapter env U registry context raw source)
    (action : SortableCodeAction env U registry context relevant
      (.singleton source) next (.singleton output))
    (formed : (Profile.singleton source).HasType (.sort relevant)) :
    Nonempty (ActionAfterAdapter env U registry context raw output) := by
  have canonical := AdapterNormal.atom_sortable formed
  have rigid : AdapterNormal.atom raw = source := by
    have direct : AtomAdapter env U registry context (AdapterNormal.atom raw) source := by
      simpa only [NormalAtomAdapter, canonical] using adapter
    exact direct.sortable_rigid formed
  have normalization : AtomView env U registry context raw source :=
    rigid ▸ AdapterNormal.view henv raw
  exact ⟨⟨output, .comp (.view normalization) (.code action formed), .refl _⟩⟩

theorem AtomAction.followView
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx context (env.IsType U))
    (adapter : NormalAtomAdapter env U registry context raw source)
    (view : AtomView env U registry context source output) :
    Nonempty (ActionAfterAdapter env U registry context raw output) :=
  ⟨⟨raw, .view (.refl _), adapter.comp (view.toAdapter henv hscoped formed)⟩⟩

/-- Function-output actions retain the returned function's own key program.
Only the lower-rank result action is replayed; no reverse input adapter is needed. -/
theorem AtomAction.followFn
    (henv : env.Ordered)
    {key : Key n} {source output : Atom n} {raw : Atom (n + 1)}
    (adapter : NormalAtomAdapter env U registry context raw (.fn key source))
    (_child : AtomAction env U registry context source output)
    (replay : ∀ {actual : Atom n}, NormalAtomAdapter env U registry context actual source →
      Nonempty (ActionAfterAdapter env U registry context actual output)) :
    Nonempty (ActionAfterAdapter env U registry context raw (.fn key output)) := by
  obtain ⟨actualKey, actualOutput, equal, ⟨keys⟩, ⟨results⟩⟩ := adapter.fn_inv
  have normalized : AdapterNormal.atom actualOutput = actualOutput := by
    have idem := AdapterNormal.atom_idem raw
    rw [equal] at idem
    exact (AtomData.fn.inj idem).2
  have resultAdapter : NormalAtomAdapter env U registry context actualOutput source := by
    simpa only [NormalAtomAdapter, normalized] using results
  obtain ⟨next⟩ := replay resultAdapter
  have normalKey : AdapterNormal.key actualKey = actualKey := by
    have idem := AdapterNormal.atom_idem raw
    rw [equal] at idem
    exact (AtomData.fn.inj idem).1
  refine ⟨⟨.fn actualKey next.actual,
    .comp (.view (equal ▸ AdapterNormal.view henv raw)) (.fn actualKey next.action), ?_⟩⟩
  change AtomAdapter env U registry context (n := n + 1)
    (.fn (AdapterNormal.key actualKey) (AdapterNormal.atom next.actual))
    (.fn (AdapterNormal.key key) (AdapterNormal.atom output))
  rw [normalKey]
  exact .fn keys next.adapter

/-- Padding is pushed into code leaves and function outputs. This finite
normal form keeps directional key programs out of the source action syntax. -/
inductive OutputAction (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (context : List VExpr) : {n : Nat} → Atom n → Atom n → Type where
  | view (view : AtomView env U registry context a b) : OutputAction env U registry context a b
  | code (action : SortableCodeAction env U registry context relevant
        (.singleton a) next (.singleton b))
      (formed : (Profile.singleton a).HasType (.sort relevant)) : OutputAction env U registry context a b
  | fn (key : Key n) (child : OutputAction env U registry context a b) :
      OutputAction env U registry context (n := n + 1) (.fn key a) (.fn key b)
  | comp (first : OutputAction env U registry context a b)
      (second : OutputAction env U registry context b c) : OutputAction env U registry context a c

noncomputable def OutputAction.toAction {n : Nat} {a b : Atom n} (action : OutputAction env U registry context a b) :
    AtomAction env U registry context a b :=
  match n, a, b, action with
  | _, _, _, .view v => .view v
  | _, _, _, .code action formed => .code action formed
  | _ + 1, _, _, .fn key child => .fn key child.toAction
  | _, _, _, .comp first second => .comp first.toAction second.toAction

noncomputable def OutputAction.pad (action : OutputAction env U registry context (a : Atom n) b) :
    OutputAction env U registry context (n := n + 1) (.pad a) (.pad b) := by
  induction action with
  | view view => exact .view (.pad view)
  | code action formed =>
    apply OutputAction.code
    · simpa only [Profile.pad_singleton] using SortableCodeAction.comp .unpad (.comp action .pad)
    · simpa only [Profile.pad_singleton] using formed.pad_sort
  | fn key child ih =>
    exact .comp (.view (.commutePadFn _ _))
      (.comp (.fn key.pad ih) (.view (.uncommutePadFn _ _)))
  | comp first second firstIH secondIH => exact .comp firstIH secondIH

noncomputable def AtomAction.outputs {n : Nat} {a b : Atom n} (action : AtomAction env U registry context a b) :
    OutputAction env U registry context a b :=
  match n, a, b, action with
  | _, _, _, .view v => .view v
  | _, _, _, .code action formed => .code action formed
  | _ + 1, _, _, .fn key child => .fn key child.outputs
  | _ + 1, _, _, .pad child => child.outputs.pad
  | _, _, _, .comp first second => .comp first.outputs second.outputs

theorem OutputAction.followAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx context (env.IsType U))
    (action : OutputAction env U registry context source output)
    (adapter : NormalAtomAdapter env U registry context raw source) :
    Nonempty (ActionAfterAdapter env U registry context raw output) := by
  induction action with
  | view view => exact AtomAction.followView henv hscoped formed adapter view
  | code action sorted => exact AtomAction.followCode henv adapter action sorted
  | fn key child ih => exact AtomAction.followFn henv adapter child.toAction (fun {_} next => ih next)
  | comp first second firstIH secondIH =>
    obtain ⟨middle⟩ := firstIH adapter
    obtain ⟨last⟩ := secondIH middle.adapter
    exact ⟨⟨last.actual, .comp middle.action last.action, last.adapter⟩⟩

theorem AtomAction.followAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx context (env.IsType U))
    (action : AtomAction env U registry context source output)
    (adapter : NormalAtomAdapter env U registry context raw source) :
    Nonempty (ActionAfterAdapter env U registry context raw output) :=
  action.outputs.followAdapter henv hscoped formed adapter

end Lean4Lean.AnchoredSemantics
