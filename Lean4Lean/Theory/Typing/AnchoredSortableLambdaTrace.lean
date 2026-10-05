import Lean4Lean.Theory.Typing.AnchoredSortableOutputPath
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableLambdaData
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaTrace

/-! A function query at an actual lambda retains a concrete lambda node.
Unused union branches may retain resources, so the selected node's footprint
is included in the original footprint rather than asserted equal to it. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def FunctionShape : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .fn _ _ => True
  | _ + 1, .pad atom => FunctionShape atom
  | _ + 1, _ => False

theorem AtomView.functionShape_iff {a b : Atom n}
    (view : AtomView env U registry Γ a b) : FunctionShape a ↔ FunctionShape b := by
  match n, a, b, view with
  | _, _, _, .refl _ => exact Iff.rfl
  | _ + 1, _, _, .reanchor _ => exact Iff.rfl
  | _ + 1, _, _, .domainRekey .. => exact Iff.rfl
  | _ + 1, _, _, .input .. => exact Iff.rfl
  | _ + 2, _, _, .commutePadFn .. => exact Iff.rfl
  | _ + 2, _, _, .uncommutePadFn .. => exact Iff.rfl
  | _ + 1, _, _, .fn .. => exact Iff.rfl
  | k + 1, _, _, .pad child =>
    simpa only [FunctionShape] using (AtomView.functionShape_iff (n := k) child)
  | _, _, _, .trans first second =>
    exact (AtomView.functionShape_iff first).trans (AtomView.functionShape_iff second)
termination_by sizeOf view
decreasing_by all_goals (simp_wf <;> omega)

theorem FunctionShape.not_sortable {atom : Atom n}
    (shape : FunctionShape atom)
    (formed : (Profile.singleton atom).HasType (.sort relevant)) : False := by
  induction n with
  | zero => exact shape
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | record => exact shape
    | fn key output =>
      obtain ⟨cover, member, typed⟩ := formed.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    | pad atom =>
      change (Profile.singleton atom).pad.HasType (.sort relevant) at formed
      have lower := formed.pad_inv
      simp only [Profile.down_sort] at lower
      exact ih shape lower

theorem AtomAction.functionShape_iff {a b : Atom n}
    (action : AtomAction env U registry Γ a b) : FunctionShape a ↔ FunctionShape b := by
  induction action with
  | view change => exact AtomView.functionShape_iff change
  | code action formed =>
    exact ⟨fun shape => False.elim (shape.not_sortable formed),
      fun shape => False.elim (shape.not_sortable (action.preservesSort formed))⟩
  | fn => exact Iff.rfl
  | pad child ih => exact ih
  | comp first second firstIH secondIH => exact firstIH.trans secondIH

noncomputable def CoveredLambda.toSortable
    (node : CoveredLambda env U registry Γ locals σ A body key output) :
    SortableCoveredLambda env U registry Γ locals σ A body key output where
  domainSupport := node.domainSupport
  domainFootprint := node.domainFootprint
  domain := .ofCode node.domain node.domain.formed
  guard := node.guard
  bodyFootprint := node.bodyFootprint
  bodyObservation := .legacy node.bodyObservation
  outside := node.outside
  packed := node.packed
  pack := node.pack
  covered := node.covered

structure SortableLamOrigin (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (A body : VExpr) where
  rank : Nat
  key : Key rank
  output : Atom rank
  node : SortableCoveredLambda env U registry Γ locals σ A body key output

theorem SortableObs.lambda_factorFunction {demand : Profile n}
    (observation : SortableObs env U registry Γ locals σ (.lam A body) demand footprint)
    (output : Atom n) (single : demand = .singleton output) (shape : FunctionShape output) :
    ∃ origin : SortableLamOrigin env U registry Γ locals σ A body,
      Nonempty (SortableOutputPath env U registry Γ (r := origin.rank + 1)
        (AtomData.fn origin.key origin.output) output) ∧
      List.Subset (origin.node.domainFootprint ++ origin.node.outside) footprint := by
  match n, demand, footprint, observation with
  | _, _, _, .legacy source =>
    obtain ⟨origin, ⟨path⟩, equal⟩ := source.lambda_factor output single
    exact ⟨⟨origin.rank, origin.key, origin.output, origin.node.toSortable⟩, ⟨.legacy path⟩,
      fun _ member => equal ▸ member⟩
  | _, _, _, .code _ certificate =>
    exact False.elim (shape.not_sortable (single ▸ certificate.formed))
  | _, _, _, .lam domain guard body pack covered =>
    cases List.singleton_inj.mp single
    exact ⟨⟨_, _, _, ⟨_, _, domain, guard, _, body, _, _, pack, covered⟩⟩,
      ⟨.refl⟩, fun _ member => member⟩
  | _, _, _, .union left right =>
    rcases List.append_eq_singleton_iff.mp single with hs | hs
    · obtain ⟨origin, path, included⟩ := right.lambda_factorFunction output hs.2 shape
      exact ⟨origin, path, fun _ member => List.mem_append_right _ (included member)⟩
    · obtain ⟨origin, path, included⟩ := left.lambda_factorFunction output hs.1 shape
      exact ⟨origin, path, fun _ member => List.mem_append_left _ (included member)⟩
  | _, _, _, .action source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included⟩ :=
      source.lambda_factorFunction _ rfl ((AtomAction.functionShape_iff change).mpr shape)
    exact ⟨origin, ⟨.action path change⟩, included⟩
  | _, _, _, .view source change =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included⟩ :=
      source.lambda_factorFunction _ rfl ((AtomView.functionShape_iff change).mpr shape)
    exact ⟨origin, ⟨.action path (.view change)⟩, included⟩
  | _, _, _, .pad source =>
    obtain ⟨first, equal, outputEq⟩ := List.map_eq_singleton_iff.mp single
    have firstShape : FunctionShape first := by simpa only [← outputEq, FunctionShape] using shape
    obtain ⟨origin, ⟨path⟩, included⟩ := source.lambda_factorFunction first equal firstShape
    exact ⟨origin, outputEq ▸ Nonempty.intro (SortableOutputPath.pad path), included⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩, included⟩ := source.lambda_factorFunction (.pad output)
      (by rw [single, Profile.pad_singleton]) shape
    exact ⟨origin, ⟨.unpad path⟩, included⟩
  | _, _, _, .rowShift source =>
    cases List.singleton_inj.mp single
    obtain ⟨origin, ⟨path⟩, included⟩ := source.lambda_factorFunction _ rfl True.intro
    exact ⟨origin, ⟨.rowShift path⟩, included⟩
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

end Lean4Lean.AnchoredSource.Adapted
