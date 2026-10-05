import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Inductive.NativeRecursorData
import Batteries.Tactic.OpenPrivate

/-! Scope and term-renaming facts for the actual singleton reconstruction
program. These facts retain its selected index and proof-field programs. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
open private ProjectionData.step_closed scopes_append scopes_singleton
  from Lean4Lean.Theory.Inductive.ProjectionProgram

private theorem ProjectionData.indexSelector_closed {data : ProjectionData}
    (hdata : data.Scoped)
    (hi : index < data.indices.length) :
    (data.indexSelector domain target previous index).value.Closed := by
  have hindices := scopes_append hdata.indices (scopes_singleton hdata.major)
  have hdomains := scopes_append (n := 0) (left := data.params)
    (right := data.indices ++ [data.major]) (by simpa using hdata.params)
    (by simpa using hindices)
  rw [← List.append_assoc] at hdomains
  apply VExpr.ClosedN.wrapLams_closed hdomains
  change data.indices.length - index < _
  simp only [List.length_append, List.length_singleton]
  omega

theorem ProjectionData.reconstructionPrefix_closed {data : ProjectionData}
    {domains : List VExpr} {targets : List VLevel} {previous result : List ProjectionFunction}
    (hdata : data.Scoped)
    (hprevious : ∀ p ∈ previous, p.value.Closed)
    (hdomains : ∀ i (hi : i < domains.length),
      domains[i].ClosedN (data.params.length + previous.length + i))
    (hlen : previous.length + domains.length = data.fields.length)
    (hout : data.reconstructionPrefix block owner levels domains targets previous = some result) :
    ∀ p ∈ result, p.value.Closed := by
  induction targets generalizing domains previous with
  | nil => cases domains with
    | nil => cases hout; exact hprevious
    | cons d ds => cases hout
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      have cont (next : ProjectionFunction) (hclosed : next.value.Closed)
          (hout : data.reconstructionPrefix block owner levels domains targets
            (previous ++ [next]) = some result) :
          ∀ p ∈ result, p.value.Closed := by
        apply ih (previous := previous ++ [next]) (domains := domains) ?_ ?_ ?_ hout
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hprevious p hp
          · cases List.mem_singleton.mp hp; exact hclosed
        · intro i hi
          have hh := hdomains (i + 1) (by simp; omega)
          change domains[i].ClosedN (data.params.length + previous.length + (i + 1)) at hh
          simpa [Nat.add_assoc, Nat.add_comm 1] using hh
        · simpa [Nat.add_assoc, Nat.add_comm 1] using hlen
      simp only [ProjectionData.reconstructionPrefix] at hout
      split at hout
      · split at hout
        · exact cont _ (data.indexSelector_closed hdata ‹_›) hout
        · contradiction
      · cases target <;> try contradiction
        exact cont _ (ProjectionData.step_closed hdata (hdomains 0 (by simp)) hprevious
          (by simp at hlen; omega) (target := .zero)).1 hout

theorem ProjectionData.reconstructionPrefix_length {data : ProjectionData}
    {domains : List VExpr} {targets : List VLevel} {previous result : List ProjectionFunction}
    (hout : data.reconstructionPrefix block owner levels domains targets previous = some result) :
    result.length = previous.length + domains.length := by
  induction targets generalizing domains previous with
  | nil => cases domains with
    | nil => cases hout; simp
    | cons d ds => cases hout
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      have cont (next : ProjectionFunction)
          (h : data.reconstructionPrefix block owner levels domains targets
            (previous ++ [next]) = some result) :
          result.length = previous.length + (domain :: domains).length := by
        have hh := ih h
        simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hh ⊢
        omega
      simp only [ProjectionData.reconstructionPrefix] at hout
      split at hout
      · split at hout
        · exact cont _ hout
        · contradiction
      · cases target <;> try contradiction
        exact cont _ hout

/-- Closed declaration syntax commutes with renaming the simultaneous
occurrence arguments. It cannot retain any unrenamed free variable. -/
theorem instantiateParams_lift' {body : VExpr} {args : List VExpr}
    (hbody : body.ClosedN args.length) :
    (instantiateParams body args).lift' ρ =
      instantiateParams body (args.map (·.lift' ρ)) := by
  let σ : VExpr.Subst := fun i =>
    if hi : i < args.length then args[args.length - 1 - i] else .bvar (i - args.length)
  change (body.subst σ).lift' ρ = _
  rw [VExpr.lift'_subst]
  unfold instantiateParams
  dsimp only [σ]
  apply VExpr.subst_congr_closedN hbody
  intro i hi
  simp only [VExpr.Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

private theorem lift'_mkApps_reconstruction (fn : VExpr) (args : List VExpr) :
    (mkApps fn args).lift' ρ = mkApps (fn.lift' ρ) (args.map (·.lift' ρ)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih => exact ih (.app fn arg)

/-- Successful occurrence reconstruction commutes with a term renaming.
The field functions come from the checked telescope and are proved closed. -/
theorem singletonReconstructAt_lift' {schema : CaseSchema} {params : List VExpr}
    {owner : Fin schema.signature.families.size}
    (H : schema.singletonReconstructAt block owner U levels sorts params indices major = some ctor) :
    schema.singletonReconstructAt block owner U levels sorts
      (params.map (·.lift' ρ)) (indices.map (·.lift' ρ)) (major.lift' ρ) =
      some (ctor.lift' ρ) := by
  unfold singletonReconstructAt at H ⊢
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨data, hdata, H⟩ := H
  simp only [bind, hdata, Option.bind_some, List.length_map]
  split at H <;> try contradiction
  rename_i harity
  rw [if_neg harity]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨fields, hfields, hresult⟩ := H
  cases hresult
  simp only [hfields, Option.bind_some, Option.pure_def, Option.some.injEq]
  have hd := projectionData_scoped hdata
  have hclosed := data.reconstructionPrefix_closed hd (by simp)
    (by simpa using hd.fields) (by simp) hfields
  have hlen := data.reconstructionPrefix_length hfields
  simp only [List.length_nil, Nat.zero_add] at hlen
  have hp : params.length = data.params.length := by
    by_cases hp : params.length = data.params.length
    · exact hp
    · exact (harity (by simp [hp])).elim
  have hargs : data.constructor.ClosedN
      (params ++ fields.map (fun field => mkApps field.value (params ++ indices ++ [major]))).length := by
    simpa only [List.length_append, List.length_map, hp, hlen] using hd.constructor
  rw [instantiateParams_lift' hargs]
  congr 1
  simp only [List.map_append, List.map_map, Function.comp_def, lift'_mkApps_reconstruction,
    List.map_cons, List.map_nil]
  congr 1
  apply List.map_congr_left
  intro field hf
  rw [(hclosed field hf).lift'_eq Lift.Fixes.zero]

/-- Reconstruction control flow inspects argument arity, never the chosen
term witnesses. This includes failed restoration and selector generation. -/
theorem singletonReconstructAt_isSome {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {params params' indices indices' : List VExpr}
    (hp : params'.length = params.length) (hi : indices'.length = indices.length) :
    (schema.singletonReconstructAt block owner U levels sorts params' indices' major').isSome =
      (schema.singletonReconstructAt block owner U levels sorts params indices major).isSome := by
  unfold singletonReconstructAt
  split
  · rfl
  · cases hs : schema.projectionData owner levels with
    | none => rfl
    | some data =>
      simp only [bind, Option.bind_some, hp, hi]
      split
      · rfl
      · cases data.reconstructionPrefix block owner.val levels data.fields sorts [] <;> rfl

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

theorem reconstruct_lift' {data : NativeRecursorData} {args : List VExpr}
    (H : data.reconstruct U levels sorts args = some ctor) :
    data.reconstruct U levels sorts (args.map (·.lift' ρ)) = some (ctor.lift' ρ) := by
  unfold reconstruct at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨major, hmajor, H⟩ := H
  simp only [List.getElem?_map, hmajor, Option.map_some, bind, Option.bind_some,
    ← List.map_take, ← List.map_drop]
  exact singletonReconstructAt_lift' H

theorem reconstructCanonical_lift' {data : NativeRecursorData} {args : List VExpr}
    (H : data.reconstructCanonical U levels args = some ctor) :
    data.reconstructCanonical U levels (args.map (·.lift' ρ)) = some (ctor.lift' ρ) := by
  unfold reconstructCanonical at H ⊢
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨source, hsource, H⟩ := H
  simp only [bind, hsource, Option.bind_some]
  exact reconstruct_lift' H

theorem reconstruct_isSome {data : NativeRecursorData} {args args' : List VExpr}
    (ha : args'.length = args.length) :
    (data.reconstruct U levels sorts args').isSome = (data.reconstruct U levels sorts args).isSome := by
  unfold reconstruct
  simp only [ha]
  split
  · rfl
  · rename_i hguard
    have hlen : data.majorOffset < args.length := by
      by_cases hlen : args.length = data.majorOffset + 1
      · omega
      · exact (hguard (by simp [hlen])).elim
    simp only [List.getElem?_eq_getElem hlen,
      List.getElem?_eq_getElem (show data.majorOffset < args'.length by omega), bind, Option.bind_some]
    exact singletonReconstructAt_isSome (by simp [ha]) (by simp [ha])

theorem reconstructCanonical_isSome {data : NativeRecursorData} {args args' : List VExpr}
    (ha : args'.length = args.length) :
    (data.reconstructCanonical U levels args').isSome = (data.reconstructCanonical U levels args).isSome := by
  unfold reconstructCanonical
  cases data.schema.projectionData data.owner (data.sourceLevels levels) with
  | none => rfl
  | some source => exact reconstruct_isSome ha

theorem reconstructCanonical_rename (data : NativeRecursorData) (args : List VExpr) (ρ : Lift) :
    data.reconstructCanonical U levels (args.map (·.lift' ρ)) =
      (data.reconstructCanonical U levels args).map (·.lift' ρ) := by
  cases h : data.reconstructCanonical U levels args with
  | none =>
    have hh := reconstructCanonical_isSome (data := data) (U := U) (levels := levels)
      (args := args) (args' := args.map (·.lift' ρ)) (by simp)
    rw [h] at hh
    cases he : data.reconstructCanonical U levels (args.map (·.lift' ρ)) <;> simp_all
  | some ctor => exact reconstructCanonical_lift' h

end Lean4Lean.InductiveSignature.NativeRecursorData
