import Lean4Lean.Theory.Typing.AnchoredGeneralOutputPathFuture
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderApplicationReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFuture

/-! Future transport of the existing finite application seed ledger. All
original nodes and Located paths are retained literally; output programs,
actual child queries and computed capture requests move to the target world. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

namespace OriginalRecordSource
open OriginalEndpointFactor OriginalTail
variable {sourceEnv : VEnv} {U : Nat}
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}

noncomputable def RichAppOrigin.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (origin : RichAppOrigin root env registry Γ source locals σ f a) :
    RichAppOrigin root env registry Δ source locals (σ.lift_r ρ) f a where
  A := origin.A
  B := origin.B
  u := origin.u
  v := origin.v
  hu := origin.hu
  hv := origin.hv
  domain := origin.domain
  codomain := origin.codomain
  functionNode := origin.functionNode
  argumentNode := origin.argumentNode
  result := origin.result
  location := origin.location
  rank := origin.rank
  key := origin.key.rename ρ
  output := origin.output.rename ρ
  functionFootprint := Footprint.rename ρ origin.functionFootprint
  argumentFootprint := Footprint.rename ρ origin.argumentFootprint
  function := by
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] using origin.function.future henv W
  rawInput := origin.rawInput.rename ρ
  argument := origin.argument.future henv W
  arguments := GeneralNormalProfileAdapter.future henv W origin.arguments
  admitted := by simpa only [lift'_subst] using Admitted.future henv W origin.admitted

noncomputable def RichApplicationSeeds.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (seeds : RichApplicationSeeds root env registry Γ source locals σ f a footprint atoms) :
    RichApplicationSeeds root env registry Δ source locals (σ.lift_r ρ) f a
      (Footprint.rename ρ footprint) (atoms.map (Atom.rename ρ)) := by
  induction seeds with
  | nil => exact .nil
  | cons origin path included rest ih =>
    refine .cons (origin.future henv W) (path.future henv W) ?_ ih
    intro entry member
    change entry ∈ Footprint.rename ρ origin.functionFootprint ++
      Footprint.rename ρ origin.argumentFootprint at member
    rw [← Footprint.rename_append] at member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map_of_mem (included oldMember)

@[simp] theorem RichAppOrigin.functionNeed_future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (origin : RichAppOrigin root env registry Γ source locals σ f a) :
    (origin.future henv W).functionNeed = origin.functionNeed.rename ρ := by
  simp only [future, functionNeed, Need.rename, Profile.fn, Profile.rename_singleton, Atom.rename_fn]

@[simp] theorem RichAppOrigin.argumentNeed_future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (origin : RichAppOrigin root env registry Γ source locals σ f a) :
    (origin.future henv W).argumentNeed = origin.argumentNeed.rename ρ := rfl

@[simp] theorem RichApplicationSeeds.required_future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (seeds : RichApplicationSeeds root env registry Γ source locals σ f a footprint atoms)
    (functionIndex argumentIndex : Nat) :
    (seeds.future henv W).required functionIndex argumentIndex =
      Footprint.rename ρ (seeds.required functionIndex argumentIndex) := by
  induction seeds with
  | nil => rfl
  | cons origin path included rest ih =>
    change [(functionIndex, (origin.future henv W).functionNeed),
      (argumentIndex, (origin.future henv W).argumentNeed)] ++
      (rest.future henv W).required functionIndex argumentIndex = _
    rw [ih, RichAppOrigin.functionNeed_future, RichAppOrigin.argumentNeed_future]
    rfl

end OriginalRecordSource
end Lean4Lean.AnchoredSource.Adapted
