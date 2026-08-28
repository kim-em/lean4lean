import Lean4Lean.Verify.Inductive.Run.Formation
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Literal expansion names which are not reserved by
`Kernel.Environment.primitives`.  Unlike the other four literal names, these
cannot be excluded solely from a successful ordinary `checkName`. -/
def checkPositivityStep.unreservedLiteralConstructorNames : List Name :=
  [``Char, ``List.nil, ``List.cons]

/-- The exact residual literal-name condition left after successful ordinary
header installation has excluded every primitive-reserved name. -/
def checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
    (names : List Name) : Prop :=
  ∀ name ∈ unreservedLiteralConstructorNames, names.contains name = false

/-- Once string-literal support is present, `HasPrimitives` and orderedness
recover all three non-reserved constants used by literal expansion. -/
theorem unreservedLiteralConstructorsOfStringOfList
    {env : VEnv}
    (H : env.HasPrimitives) (hwf : env.Ordered)
    (hstring : env.contains ``String.ofList) :
    ∀ name ∈ checkPositivityStep.unreservedLiteralConstructorNames,
      env.contains name := by
  intro name hname
  simp only [checkPositivityStep.unreservedLiteralConstructorNames,
    List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl
  · have HlistChar :=
      (TrExprS.listChar hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ _ Hchar := HlistChar
    let .const hlookup _ _ := Hchar
    exact ⟨_, hlookup⟩
  · have Hnil :=
      (TrExprS.listCharNil hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ HnilConst _ := Hnil
    let .const hlookup _ _ := HnilConst
    exact ⟨_, hlookup⟩
  · have Hcons :=
      (TrExprS.listCharCons hwf H hstring (Us := []) (Δ := [])).1
    let .app _ _ HconsConst _ := Hcons
    let .const hlookup _ _ := HconsConst
    exact ⟨_, hlookup⟩

/-- The already-checked raw header installation excludes the three
unreserved literal names whenever they are present in its source model.  This
form is available before the executable production header fold runs. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.unreservedLiteralNamesDisjointOfSourceContains
    (H : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe decl
      envTypes)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      sourceEnv.contains name) :
    checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  have hfresh := (VEnv.addConstVals_names_fresh H.typesAdded).2
  intro name hname
  have hnotMem : name ∉ decl.types.map (·.name) := by
    intro hmem
    rcases hpresent name hname with ⟨ci, hlookup⟩
    rcases List.mem_map.mp hmem with ⟨type, htype, htypeName⟩
    have hconstant : type.toVConstVal ∈ decl.typeConstants :=
      List.mem_map.mpr ⟨type, htype, rfl⟩
    have habsent := hfresh type.toVConstVal hconstant
    rw [show type.toVConstVal.name = name by simpa using htypeName,
      hlookup] at habsent
    contradiction
  simpa using hnotMem

/-- Any constant already present in the source model is excluded from the
fresh family names by the checked abstract header installation. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.familyNamesExcludeSourceContains
    (H : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe decl
      envTypes)
    (hpresent : sourceEnv.contains name) :
    name ∉ decl.types.map (·.name) := by
  intro hmem
  rcases hpresent with ⟨ci, hlookup⟩
  rcases List.mem_map.mp hmem with ⟨type, htype, htypeName⟩
  have hconstant : type.toVConstVal ∈ decl.typeConstants :=
    List.mem_map.mpr ⟨type, htype, rfl⟩
  have habsent := (VEnv.addConstVals_names_fresh H.typesAdded).2
    type.toVConstVal hconstant
  rw [show type.toVConstVal.name = name by simpa using htypeName,
    hlookup] at habsent
  contradiction

/-- Before production header installation, the already-checked abstract
header fold supplies the exact environment-indexed literal condition.  This
also covers `Char` bootstrap: string literals are not supported in that
source environment, while natural literals expand only through pre-existing
natural constructors. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.materializedAvailableLiteralDisjoint
    (H : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe decl
      envTypes)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      sourceEnv lparams Delta stats decl depth)
    (hprimitives : sourceEnv.HasPrimitives) (hwf : sourceEnv.Ordered) :
    checkPositivityStep.AvailableLiteralDisjoint
      sourceEnv stats.indConsts := by
  intro literal havailable
  cases literal with
  | natVal n =>
      have hnat := hprimitives.nat havailable
      exact Hmaterialized.natLiteralDisjoint
        (H.familyNamesExcludeSourceContains hnat.1)
        (H.familyNamesExcludeSourceContains hnat.2) n
  | strVal s =>
      have hnat : sourceEnv.contains ``Nat :=
        hprimitives.nat_of_charOfNat hwf havailable.1
      have hnatCtors := hprimitives.nat hnat
      have hunreserved := unreservedLiteralConstructorsOfStringOfList
        hprimitives hwf havailable.2
      apply Hmaterialized.literalDisjoint
      intro name hname
      have hpresent : sourceEnv.contains name := by
        simp only [checkPositivityStep.literalConstructorNames,
          List.mem_cons, List.not_mem_nil, or_false] at hname
        rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hnatCtors.1
        · exact hnatCtors.2
        · exact havailable.2
        · exact hunreserved ``Char (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · exact hunreserved ``List.nil (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · exact hunreserved ``List.cons (by
            simp [checkPositivityStep.unreservedLiteralConstructorNames])
        · exact havailable.1
      simpa using H.familyNamesExcludeSourceContains hpresent

/-- Once string support is visible in the source model, a checked raw header
translation has no remaining literal-name premise. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.unreservedLiteralNamesDisjointOfStringOfList
    (H : TrInductDeclHeaders sourceEnv lparams nparams types isUnsafe decl
      envTypes)
    (hprimitives : sourceEnv.HasPrimitives) (hwf : sourceEnv.Ordered)
    (hstring : sourceEnv.contains ``String.ofList) :
    checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) :=
  H.unreservedLiteralNamesDisjointOfSourceContains
    (unreservedLiteralConstructorsOfStringOfList hprimitives hwf hstring)

/-- An ordinary installed family cannot use a production-reserved primitive
name.  This is the exact reusable consequence of successful `checkName` for
the materialized family-name list. -/
theorem DeclaredHeadersResult.familyNamesExcludePrimitive
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name) :
    name ∉ decl.types.map (·.name) := by
  intro hmem
  have hvalue : name ∈
      (H.entries.map Prod.snd).map VConstVal.name := by
    rw [H.values]
    simpa [VInductDecl.typeConstants, VInductiveType.toVConstVal,
      Function.comp_def] using hmem
  exact H.installed.valueNamesNonprimitive name hvalue hprimitive

/-- Successful ordinary header installation excludes every literal expansion
name except the three names not reserved by the kernel. -/
theorem DeclaredHeadersResult.literalNamesDisjointOfUnreserved
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hunreserved :
      checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
        (decl.types.map (·.name))) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  intro name hliteral
  simp only [checkPositivityStep.literalConstructorNames, List.mem_cons,
    List.not_mem_nil, or_false] at hliteral
  rcases hliteral with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact excludePrimitive (by native_decide)
  · exact excludePrimitive (by native_decide)
  · exact excludePrimitive (by native_decide)
  · exact hunreserved ``Char (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact hunreserved ``List.nil (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact hunreserved ``List.cons (by
      simp [checkPositivityStep.unreservedLiteralConstructorNames])
  · exact excludePrimitive (by native_decide)
  where
    excludePrimitive {name : Name}
        (hprimitive : Kernel.Environment.primitives.contains name) :
        (decl.types.map (·.name)).contains name = false := by
      simpa using H.familyNamesExcludePrimitive hprimitive

/-- If the three unreserved expansion names already exist in the abstract
source environment, successful fresh header installation discharges the
residual condition too. -/
theorem DeclaredHeadersResult.unreservedLiteralNamesDisjointOfSourceContains
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      sourceEnv.contains name) :
    checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  have hfresh := (VEnv.addConstVals_names_fresh H.installed.abstract).2
  intro name hname
  have hnotMem : name ∉ decl.types.map (·.name) := by
    intro hmem
    rcases hpresent name hname with ⟨ci, hlookup⟩
    have hconstant : ∃ value ∈ decl.typeConstants,
        value.name = name := by
      rcases List.mem_map.mp hmem with ⟨type, htype, htypeName⟩
      refine ⟨type.toVConstVal, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨type, htype, rfl⟩
      · simpa using htypeName
    rcases hconstant with ⟨value, hvalue, hvalueName⟩
    have hentryValue : value ∈ H.entries.map Prod.snd := by
      rw [H.values]
      exact hvalue
    have habsent := hfresh value hentryValue
    rw [hvalueName, hlookup] at habsent
    contradiction
  simpa using hnotMem

/-- In an environment where the unreserved literal constants are already
present, ordinary header installation supplies the original global condition
without any caller premise. -/
theorem DeclaredHeadersResult.literalNamesDisjointOfSourceContains
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hpresent : ∀ name ∈
      checkPositivityStep.unreservedLiteralConstructorNames,
      sourceEnv.contains name) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) :=
  H.literalNamesDisjointOfUnreserved
    (H.unreservedLiteralNamesDisjointOfSourceContains hpresent)

/-- After string-literal support has been installed, the existing checking
context supplies the residual source-presence evidence automatically. -/
theorem DeclaredHeadersResult.literalNamesDisjointOfStringOfList
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hstring : sourceEnv.contains ``String.ofList) :
    checkPositivityStep.LiteralConstructorNamesDisjoint
      (decl.types.map (·.name)) := by
  apply H.literalNamesDisjointOfSourceContains
  rw [← H.sourceContextVEnv] at hstring ⊢
  exact unreservedLiteralConstructorsOfStringOfList
    H.sourceContext.checking.hasPrimitives
    H.sourceContext.checking.tr.wf hstring

/-- A primitive lookup visible after ordinary header installation was already
present in the source environment: all newly installed header values have
non-primitive names. -/
theorem DeclaredHeadersResult.sourceContainsOfTargetContainsPrimitive
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hprimitive : Kernel.Environment.primitives.contains name)
    (htarget : H.context.venv.contains name) :
    sourceEnv.contains name := by
  rcases htarget with ⟨ci, hlookup⟩
  refine ⟨ci, ?_⟩
  rw [VEnv.addConstVals_constants_of_forall_ne H.installed.abstract ?_] at hlookup
  · exact hlookup
  · intro value hvalue hname
    apply H.installed.valueNamesNonprimitive value.name
      (List.mem_map.mpr ⟨value, hvalue, rfl⟩)
    simpa [hname] using hprimitive

/-- Materialized family constants inherit literal disjointness from the exact
ordinary header installation that produced them. -/
theorem DeclaredHeadersResult.materializedLiteralDisjoint
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv)
    (hunreserved :
      checkPositivityStep.UnreservedLiteralConstructorNamesDisjoint
        (decl.types.map (·.name))) :
    checkPositivityStep.LiteralDisjoint stats.indConsts :=
  H.materialized.literalDisjoint
    (H.literalNamesDisjointOfUnreserved hunreserved)

/-- The actual literal premise needed by positivity is automatic for every
ordinary declaration, including the `Char` bootstrap declaration.  Natural
literals only expose reserved natural constructors.  A supported string
literal implies that the reserved `String.ofList` lookup predates this
ordinary header batch; `HasPrimitives`, orderedness, and source freshness then
exclude the remaining `Char`/`List` expansion names. -/
theorem DeclaredHeadersResult.materializedAvailableLiteralDisjoint
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) :
    checkPositivityStep.AvailableLiteralDisjoint
      H.context.venv stats.indConsts := by
  intro literal havailable
  cases literal with
  | natVal n =>
      exact H.materialized.natLiteralDisjoint
        (H.familyNamesExcludePrimitive (by native_decide))
        (H.familyNamesExcludePrimitive (by native_decide)) n
  | strVal s =>
      have hsourceString : sourceEnv.contains ``String.ofList :=
        H.sourceContainsOfTargetContainsPrimitive (by native_decide)
          havailable.2
      exact H.materialized.literalDisjoint
        (H.literalNamesDisjointOfStringOfList hsourceString) (.strVal s)

end VerifyInductive
end Lean4Lean
