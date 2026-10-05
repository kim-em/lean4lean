import Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal

/-! Finite simultaneous capture traces. Every selected operand retains its
actual original location, the query before reflection, and the selected-input
closure bound. The capture index follows the reversed de Bruijn order of
`Subst.ofList`; footprint binder removal preserves these origins unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

def captureInsert (count depth index : Nat) : Nat :=
  if index < depth then index else index + count

theorem captureInsert_zero : captureInsert count (depth + 1) 0 = 0 := by
  simp [captureInsert]

theorem captureInsert_succ :
    captureInsert count (depth + 1) (index + 1) = captureInsert count depth index + 1 := by
  unfold captureInsert
  split <;> split <;> omega

inductive CaptureFootprint
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (arguments : List VExpr) (baseDepth depth : Nat)
    (budget : List Closure → Nat) : Footprint → Footprint → Type where
  | nil : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget [] []
  | keep (index : Nat) (need : Need)
      (tail : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before after) :
      CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget
        ((index, need) :: before) ((captureInsert arguments.length depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (index : Nat) (bound : index < arguments.length)
      (origin : OriginalEndpointFactor.CutOrigin root
        arguments[arguments.length - 1 - index] baseDepth)
      (observation : Obs env U registry Γ locals σ arguments[arguments.length - 1 - index] demand argumentFootprint)
      (whole : WholeCutQuery (env := env) origin registry Γ σ demand argumentFootprint)
      (bounded : ∀ initial, (Closure.close origin.view.origin
        (origin.location.environment initial)).cost ≤ budget initial)
      (tail : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before after) :
      CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget
        (shiftFootprint depth argumentFootprint ++ before) ((depth + index, ⟨n, demand⟩) :: after)

def CaptureFootprint.cost
    (trace : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before after)
    (initial : List Closure) : Nat :=
  match trace with
  | .nil => 0
  | .keep _ _ tail => tail.cost initial
  | .cut _ _ origin _ _ _ tail => max
      (Closure.close origin.view.origin (origin.location.environment initial)).cost
      (tail.cost initial)

theorem CaptureFootprint.cost_le
    (trace : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before after)
    (initial : List Closure) : trace.cost initial ≤ budget initial := by
  induction trace with
  | nil => exact Nat.zero_le _
  | keep _ _ _ ih => exact ih
  | cut _ _ _ _ _ bounded _ ih => exact Nat.max_le.mpr ⟨bounded initial, ih⟩

private theorem BinderPack.strip_external
    (pack : BinderPack n input (before.sourceLift (.skip .refl) ++ required) outside) :
    ∃ rest, BinderPack n input required rest ∧ outside = before ++ rest := by
  induction before generalizing outside with
  | nil => exact ⟨outside, pack, rfl⟩
  | cons entry tail ih =>
    obtain ⟨index, need⟩ := entry
    cases pack with
    | external _ _ rest =>
      obtain ⟨outside, normal, he⟩ := ih rest
      exact ⟨outside, normal, congrArg (List.cons (index, need)) he⟩

noncomputable def CaptureFootprint.weaken
    (trace : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before after)
    (bound : ∀ initial, budget initial ≤ larger initial) :
    CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth larger before after := by
  induction trace with
  | nil => exact .nil
  | keep index need _ ih => exact .keep index need ih
  | cut index captureBound origin observation whole bounded _ ih =>
    exact .cut index captureBound origin observation whole (fun initial => Nat.le_trans (bounded initial) (bound initial)) ih

noncomputable def CaptureFootprint.append
    (first : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before₁ after₁)
    (second : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget before₂ after₂) :
    CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need _ ih => exact .keep index need ih
  | cut index captureBound origin observation whole bounded _ ih =>
    simpa only [List.append_assoc, List.cons_append] using
      CaptureFootprint.cut index captureBound origin observation whole bounded ih

theorem CaptureFootprint.underBinder
    (factor : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth (depth + 1) budget before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth depth budget outside newOutside) := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, ⟨.nil⟩⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, factor⟩ := ih rest
        exact ⟨newOutside, by simpa only [captureInsert_zero] using BinderPack.local need bound normal,
          factor⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, ⟨factor⟩⟩ := ih rest
        exact ⟨(captureInsert arguments.length depth index, need) :: newOutside,
          by simpa only [captureInsert_succ] using BinderPack.external _ need normal,
          ⟨CaptureFootprint.keep index need factor⟩⟩
  | cut index captureBound origin observation whole bounded tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth + index, _) :: newOutside,
      by simpa only [Nat.add_right_comm depth 1 index] using
        BinderPack.external (depth + index) _ normal',
      ⟨CaptureFootprint.cut index captureBound origin observation whole bounded factor⟩⟩

/-- A requested capture entry selects an actual retained cut, with its
original typing location and unreflected query, rather than a synthesized
source typing of the operand. -/
structure SelectedCapture
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (locals : List Nat)
    (σ : Subst) (arguments : List VExpr) (baseDepth : Nat)
    (budget : List Closure → Nat) (before : Footprint)
    (index : Nat) (inBounds : index < arguments.length) (need : Need) where
  origin : OriginalEndpointFactor.CutOrigin root arguments[arguments.length - 1 - index] baseDepth
  footprint : Footprint
  observation : Obs env U registry Γ locals σ arguments[arguments.length - 1 - index]
    need.profile footprint
  whole : WholeCutQuery (env := env) origin registry Γ σ need.profile footprint
  included : ∀ entry ∈ footprint, entry ∈ before
  bounded : ∀ initial, (Closure.close origin.view.origin
    (origin.location.environment initial)).cost ≤ budget initial

theorem CaptureFootprint.capture
    (trace : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth 0 budget before after)
    (inBounds : index < arguments.length) (member : (index, need) ∈ after) :
    Nonempty (SelectedCapture (env := env) root registry Γ locals σ arguments baseDepth budget
      before index inBounds need) := by
  induction trace with
  | nil => cases member
  | keep original requested tail ih =>
    rcases List.mem_cons.mp member with same | member
    · have sameIndex := congrArg Prod.fst same
      simp only [captureInsert, Nat.not_lt_zero, ite_false] at sameIndex
      omega
    · obtain ⟨selected⟩ := ih member
      exact ⟨{ selected with included := fun entry present =>
          List.mem_cons_of_mem _ (selected.included entry present) }⟩
  | cut original originalBound origin observation whole bounded tail ih =>
    simp only [Nat.zero_add] at member
    rcases List.mem_cons.mp member with same | member
    · cases same
      exact ⟨⟨origin, _, observation, whole,
        (fun entry present => List.mem_append_left _ (by simpa [shiftFootprint] using present)), bounded⟩⟩
    · obtain ⟨selected⟩ := ih member
      exact ⟨{ selected with included := fun entry present =>
          List.mem_append_right _ (selected.included entry present) }⟩

theorem SelectedCapture.resources
    (selected : SelectedCapture (env := env) root registry Γ locals σ arguments baseDepth budget
      before index inBounds need)
    (available : before.Available valuation) : selected.footprint.Available valuation :=
  fun slot query member => available slot query (selected.included _ member)

/-- A footprint entry outside the capture prefix came from the original
external footprint; capture cuts cannot create it. -/
theorem CaptureFootprint.external
    (trace : CaptureFootprint (env := env) root registry Γ locals σ arguments baseDepth 0 budget before after)
    (member : (index + arguments.length, need) ∈ after) : (index, need) ∈ before := by
  induction trace with
  | nil => cases member
  | keep original requested tail ih =>
    rcases List.mem_cons.mp member with same | member
    · have sameIndex := congrArg Prod.fst same
      simp only [captureInsert, Nat.not_lt_zero, ite_false] at sameIndex
      have sameNeed : need = requested := congrArg Prod.snd same
      exact List.mem_cons.mpr (.inl (Prod.ext (by omega) sameNeed))
    · exact List.mem_cons_of_mem _ (ih member)
  | cut original originalBound origin observation whole bounded tail ih =>
    rcases List.mem_cons.mp member with same | member
    · have sameIndex := congrArg Prod.fst same
      simp only [Nat.zero_add] at sameIndex
      omega
    · exact List.mem_append_right _ (ih member)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
