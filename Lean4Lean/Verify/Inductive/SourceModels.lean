import Lean4Lean.Verify.Inductive.SourceSignature
import Lean4Lean.Theory.Inductive.SourceModelNames

/-! Assemble one source model from the shared source-boundary selections. -/

namespace Lean4Lean.VerifyInductive
open InductiveSignature

/-- The ordered source family and constructor tables, together with each
field's actual checked classification, determine a full normalized model. -/
theorem sourceModelsOfTables {s : InductiveSignature} {decl : VInductDecl}
    (Hsource : decl.SourceWF env)
    (hadd : env.addConstVals decl.typeConstants = some envTypes)
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (Hfamilies : List.Forall₂ (fun f src =>
      f.name = src.name ∧ f.indices.length = src.numIndices ∧
      f.resultLevel = src.resultLevel ∧
      env.IsDefEqU decl.uvars []
        (VExpr.wrapForalls (s.params ++ f.indices) (.sort f.resultLevel)) src.type)
      s.families.toList decl.types)
    (Hctors : List.Forall₂ (fun ctor pair =>
      s.families[ctor.owner].name = pair.1.name ∧ ctor.name = pair.2.name ∧
      envTypes.IsDefEqU decl.uvars [] (s.constructorType ctor) pair.2.type)
      s.constructors.toList decl.ownedConstructors)
    (Hfields : ∀ ctor ∈ s.constructors.toList, ∀ i (hi : i < ctor.fields.length),
      SignatureFieldModel envTypes decl.uvars s
        (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i])
    (Harity : ∀ ctor ∈ s.constructors.toList,
      ctor.indices.length = s.families[ctor.owner].indices.length) :
    s.Models env decl := by
  have hnames : s.families.toList.map (·.name) = decl.types.map (·.name) := by
    have hr := Lean4Lean.List.Forall₂.imp (fun _ _ h => h.1) Hfamilies
    clear Hfamilies Hctors Hfields Hsource
    generalize s.families.toList = left at hr ⊢
    generalize decl.types = right at hr ⊢
    induction hr with
    | nil => rfl
    | cons h _ ih => simp [h, ih]
  have hfamilyNames := decl.typeNames_nodup Hsource.2.1
  let C : VConstVal → VConstVal → Prop := fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      envTypes.IsDefEqU decl.uvars [] normalized.type source.type
  have hctorFamilies (owner : Fin s.families.size) {family : VInductiveType}
      (hf : family ∈ decl.types) (hn : s.families[owner].name = family.name) :
      List.Forall₂ C (s.declarationFamily owner).ctors family.ctors := by
    apply Lean4Lean.List.Forall₂.imp (fun normalized source hc => ?_)
      (Lean4Lean.List.Forall₂.and_mem
        (constructor_model_in_family (R := fun ctor source => ctor.name = source.name ∧
          envTypes.IsDefEqU decl.uvars [] (s.constructorType ctor) source.type)
          hnames hfamilyNames Hctors owner hf hn))
    obtain ⟨⟨ctor, rfl, hname, htype⟩, _, hsourceMem⟩ := hc
    exact ⟨hname, huvars.trans (Hsource.2.2.2.1 source
      (List.mem_flatMap.mpr ⟨family, hf, hsourceMem⟩)).symm, htype⟩
  have hfull : List.Forall₂ (fun normalized source : VInductiveType =>
      normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
      normalized.numIndices = source.numIndices ∧
      normalized.resultLevel ≈ source.resultLevel ∧
      env.IsDefEqU decl.uvars [] normalized.type source.type ∧
      List.Forall₂ C normalized.ctors source.ctors) s.declaration.types decl.types := by
    apply Lean4Lean.List.forall₂_of_getElem (by simpa [declaration] using Lean4Lean.List.Forall₂.length_eq Hfamilies)
    intro i hi hi'
    have hsize : i < s.families.size := by simpa [declaration] using hi
    let owner : Fin s.families.size := ⟨i, hsize⟩
    have hget := Lean4Lean.List.forall₂_getElem Hfamilies i (by simpa using hsize) hi'
    have he : s.declaration.types[i] = s.declarationFamily owner := by
      simp [declaration, declarationFamily, owner]
    rw [he]
    refine ⟨hget.1, huvars.trans (Hsource.2.2.1 _ (List.getElem_mem hi')).symm,
      hget.2.1, ?_, hget.2.2.2, hctorFamilies owner (List.getElem_mem hi') hget.1⟩
    exact hget.2.2.1 ▸ rfl
  refine ⟨huvars, hparams, hsafety, ?_, ⟨envTypes, hadd, ?_⟩,
    ⟨envTypes, hadd, ?_⟩, ?_, ?_, Harity⟩
  · exact Lean4Lean.List.Forall₂.imp (fun _ _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        ctorNames_eq_of_forall₂ h.2.2.2.2.2 (fun _ _ hc => hc.1)⟩) hfull
  · change List.Forall₂ C (s.declaration.types.flatMap (·.ctors)) (decl.types.flatMap (·.ctors))
    clear Hfamilies Hctors Hfields hnames hfamilyNames hctorFamilies Hsource
    generalize s.declaration.types = left at hfull ⊢
    generalize decl.types = right at hfull ⊢
    induction hfull with
    | nil => exact .nil
    | cons h _ ih => exact h.2.2.2.2.2.append' ih
  · intro ctor hc i hi type r he
    have hfield := Hfields ctor hc i hi
    rw [he] at hfield
    exact hfield.1
  · by_cases hunsafe : s.isUnsafe = true
    · exact Or.inl hunsafe
    · refine Or.inr ⟨envTypes, hadd, ?_⟩
      intro ctor hc i hi type he
      have hfield := Hfields ctor hc i hi
      rw [he] at hfield
      exact hfield.resolve_left hunsafe
  · by_cases hunsafe : s.isUnsafe = true
    · exact Or.inl hunsafe
    · right
      intro ctor hc type r hm
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
      have hfield := Hfields ctor hc i hi
      rw [he] at hfield
      exact hfield.2.resolve_left hunsafe

end Lean4Lean.VerifyInductive
