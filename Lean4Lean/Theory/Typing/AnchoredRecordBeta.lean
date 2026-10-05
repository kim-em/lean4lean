import Lean4Lean.Theory.Typing.AnchoredHeadBeta
import Lean4Lean.Theory.Typing.AnchoredProjectionOriginReduction

/-! Record beta closure descends strictly through the finite observed fields.
Each raw projection equality uses its own retained literal typing origin. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}

theorem Arguments.mapEntries {α : Type} {entries : List α}
    {keys : α → DataRequest (Profile n)} {left right nextLeft nextRight : α → VExpr}
    (change : ∀ entry ∈ entries, RequestAdmission env U lower Γ (keys entry) (left entry) (right entry) →
      RequestAdmission env U lower Γ (keys entry) (nextLeft entry) (nextRight entry))
    (arguments : Arguments env U lower Γ (entries.map keys) (entries.map left) (entries.map right)) :
    Arguments env U lower Γ (entries.map keys) (entries.map nextLeft) (entries.map nextRight) := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih =>
    cases arguments with
    | cons head tail =>
      exact .cons (change entry (List.mem_cons_self ..) head)
        (ih (fun entry member => change entry (List.mem_cons_of_mem _ member)) tail)

def RecordWitness.headBeta (henv : env.Ordered)
    (beta : ∀ (Γ : List VExpr) (le re l r A : VExpr) (p d : Profile n),
      HeadBeta le l → HeadBeta re r → env.IsDefEq U Γ le l A → env.IsDefEq U Γ re r A →
      lower.term Γ l r A p d → lower.term Γ le re A p d)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (W : RecordWitness env U registry lower Γ left right type demand) :
    RecordWitness env U registry lower Γ leftExpanded rightExpanded type demand := by
  have cle := W.insertion.eq henv cl
  have cre := W.insertion.eq henv cr
  refine { W with
    leftType := cle.hasType.1
    rightType := cre.hasType.1
    leftOrigins := fun entry member => by
      obtain ⟨origin⟩ := W.leftOrigins entry member
      exact ⟨origin.replaceMajor (cle.symm)⟩
    rightOrigins := fun entry member => by
      obtain ⟨origin⟩ := W.rightOrigins entry member
      exact ⟨origin.replaceMajor (cre.symm)⟩
    fields := ?_ }
  apply Arguments.mapEntries (arguments := W.fields)
  intro entry member admitted
  obtain ⟨lo⟩ := W.leftOrigins entry member
  obtain ⟨ro⟩ := W.rightOrigins entry member
  have leq := (lo.congr cle.symm).symm
  have req := (ro.congr cre.symm).symm
  have lb : HeadBeta (.proj demand.family.name entry.1 (leftExpanded.lift' W.map))
      (.proj demand.family.name entry.1 (left.lift' W.map)) := .proj (hl.lift W.map)
  have rb : HeadBeta (.proj demand.family.name entry.1 (rightExpanded.lift' W.map))
      (.proj demand.family.name entry.1 (right.lift' W.map)) := .proj (hr.lift W.map)
  obtain ⟨anchorEq, pairEq, typed, proper, code, anchorTerm, pairTerm⟩ := admitted
  refine ⟨anchorEq.trans leq.symm,
    (leq.trans pairEq).trans req.symm,
    typed, proper, code, ?_, ?_⟩
  · exact beta W.context _ _ _ _ _ _ _ .refl lb anchorEq.hasType.1 leq anchorTerm
  · exact beta W.context _ _ _ _ _ _ _ lb rb leq req pairTerm

theorem RecordRelation.headBeta (henv : env.Ordered)
    (beta : ∀ (Γ : List VExpr) (le re l r A : VExpr) (p d : Profile n),
      HeadBeta le l → HeadBeta re r → env.IsDefEq U Γ le l A → env.IsDefEq U Γ re r A →
      lower.term Γ l r A p d → lower.term Γ le re A p d)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : RecordRelation env U registry lower Γ left right type demand) :
    RecordRelation env U registry lower Γ leftExpanded rightExpanded type demand := by
  intro Δ ρ future
  obtain ⟨W⟩ := H Δ ρ future
  exact ⟨W.headBeta henv beta (hl.lift ρ) (hr.lift ρ)
    (cl.weak' henv future.weakening) (cr.weak' henv future.weakening)⟩

def RecordWitness.contractHeadBeta (henv : env.Ordered)
    (beta : ∀ (Γ : List VExpr) (le re l r A : VExpr) (p d : Profile n),
      HeadBeta le l → HeadBeta re r → env.IsDefEq U Γ le l A → env.IsDefEq U Γ re r A →
      lower.term Γ le re A p d → lower.term Γ l r A p d)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (W : RecordWitness env U registry lower Γ leftExpanded rightExpanded type demand) :
    RecordWitness env U registry lower Γ left right type demand := by
  have cle := W.insertion.eq henv cl
  have cre := W.insertion.eq henv cr
  refine { W with
    leftType := cle.hasType.2
    rightType := cre.hasType.2
    leftOrigins := fun entry member => by
      obtain ⟨origin⟩ := W.leftOrigins entry member
      exact ⟨origin.replaceMajor (cle)⟩
    rightOrigins := fun entry member => by
      obtain ⟨origin⟩ := W.rightOrigins entry member
      exact ⟨origin.replaceMajor (cre)⟩
    fields := ?_ }
  apply Arguments.mapEntries (arguments := W.fields)
  intro entry member admitted
  obtain ⟨lo⟩ := W.leftOrigins entry member
  obtain ⟨ro⟩ := W.rightOrigins entry member
  have leq := lo.congr cle
  have req := ro.congr cre
  have lb : HeadBeta (.proj demand.family.name entry.1 (leftExpanded.lift' W.map))
      (.proj demand.family.name entry.1 (left.lift' W.map)) := .proj (hl.lift W.map)
  have rb : HeadBeta (.proj demand.family.name entry.1 (rightExpanded.lift' W.map))
      (.proj demand.family.name entry.1 (right.lift' W.map)) := .proj (hr.lift W.map)
  obtain ⟨anchorEq, pairEq, typed, proper, code, anchorTerm, pairTerm⟩ := admitted
  refine ⟨anchorEq.trans leq,
    (leq.symm.trans pairEq).trans req,
    typed, proper, code, ?_, ?_⟩
  · exact beta W.context _ _ _ _ _ _ _ .refl lb anchorEq.hasType.1 leq anchorTerm
  · exact beta W.context _ _ _ _ _ _ _ lb rb leq req pairTerm

theorem RecordRelation.contractHeadBeta (henv : env.Ordered)
    (beta : ∀ (Γ : List VExpr) (le re l r A : VExpr) (p d : Profile n),
      HeadBeta le l → HeadBeta re r → env.IsDefEq U Γ le l A → env.IsDefEq U Γ re r A →
      lower.term Γ le re A p d → lower.term Γ l r A p d)
    (hl : HeadBeta leftExpanded left) (hr : HeadBeta rightExpanded right)
    (cl : env.IsDefEq U Γ leftExpanded left type)
    (cr : env.IsDefEq U Γ rightExpanded right type)
    (H : RecordRelation env U registry lower Γ leftExpanded rightExpanded type demand) :
    RecordRelation env U registry lower Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨W⟩ := H Δ ρ future
  exact ⟨W.contractHeadBeta henv beta (hl.lift ρ) (hr.lift ρ)
    (cl.weak' henv future.weakening) (cr.weak' henv future.weakening)⟩

end Lean4Lean.AnchoredSemantics.RankedData
