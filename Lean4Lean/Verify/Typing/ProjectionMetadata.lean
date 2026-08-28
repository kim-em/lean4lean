import Lean4Lean.Verify.Typing.ProjectionRelation
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

open Lean

namespace ProjectionMetadata

/-- A successful abstract batch installation exposes every member at the
final environment.  This local form keeps projection metadata independent of
the much larger executable inductive-verification import graph. -/
theorem addConstVals_lookup
    {base out : VEnv} {constants : List VConstVal}
    {constant : VConstVal}
    (H : base.addConstVals constants = some out)
    (hmember : constant ∈ constants) :
    out.constants constant.name = some constant.toVConstant := by
  induction constants generalizing base with
  | nil => simp at hmember
  | cons head tail ih =>
      simp only [VEnv.addConstVals] at H
      cases hadd : base.addConst head.name head.toVConstant with
      | none => simp [hadd] at H
      | some next =>
          rw [hadd] at H
          rcases List.mem_cons.mp hmember with rfl | htail
          · exact (VEnv.addConstVals_le H).constants
              (VEnv.addConst_self hadd)
          · exact ih H htail

/-- Every source family in a finitely installed inductive declaration has an
actual installed primary recursor with the independently specified nested
recursor shape.  Ordinary recursors enter through the zero-auxiliary
specialization; restored nested declarations expose their primary prefix.

This is the first environment-derived input to canonical projection
expansion: no structure-information callback or semantic provider is
accepted. -/
theorem installedInductCertificate_primaryRecursor
    (H : VEnv.InstalledInductCertificate env decl)
    (howner : owner ∈ decl.types) :
    ∃ recursor : VConstVal,
      env.constants recursor.name = some recursor.toVConstant ∧
      Nonempty (decl.NestedRecursorShape owner recursor) := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have installed_eq : installed = envRecursors.addDefEqRules block.rules := by
      apply Option.some.inj
      calc
        some installed = VInductBlock.install base block := Hinstall.symm
        _ = some (envRecursors.addDefEqRules block.rules) := by
          simp [VInductBlock.install, htypes, hctors, hrecursors]
    have recursor_lookup
        (recursor : VConstVal) (hrecursor : recursor ∈ block.recursors) :
        env.constants recursor.name = some recursor.toVConstant := by
      have hlookup := addConstVals_lookup hrecursors hrecursor
      have hinstalled : installed.constants recursor.name =
          some recursor.toVConstant := by
        rw [installed_eq]
        exact VEnv.addDefEqRules_le.constants hlookup
      exact hle.constants hinstalled
    cases Hcompile with
    | ordinary Hordinary =>
        rcases Lean4Lean.List.Forall₂.forall_exists_l
            Hordinary.recursors owner howner with
          ⟨recursor, hrecursor, Hshape⟩
        let ⟨shape⟩ := Hshape
        exact ⟨recursor, recursor_lookup recursor hrecursor,
          ⟨shape.toNested⟩⟩
    | nested Hnested =>
        rcases Lean4Lean.List.Forall₂.forall_exists_l
            Hnested.primary_recursors owner howner with
          ⟨recursor, hprimary, Hshape⟩
        have hrecursor : recursor ∈ block.recursors := by
          rw [Hnested.recursors_eq]
          exact List.mem_append_left _ hprimary
        exact ⟨recursor, recursor_lookup recursor hrecursor, Hshape⟩

/-- The derived primary recursor lookup uses Lean's canonical `.rec` name. -/
theorem installedInductCertificate_recNameLookup
    (H : VEnv.InstalledInductCertificate env decl)
    (howner : owner ∈ decl.types) :
    ∃ recursor : VConstVal,
      recursor.name = mkRecName owner.name ∧
      env.constants (mkRecName owner.name) = some recursor.toVConstant ∧
      Nonempty (decl.NestedRecursorShape owner recursor) := by
  rcases installedInductCertificate_primaryRecursor H howner with
    ⟨recursor, hlookup, Hshape⟩
  let ⟨shape⟩ := Hshape
  have hname : recursor.name = mkRecName owner.name := shape.name
  exact ⟨recursor, hname, by simpa [← hname] using hlookup, ⟨shape⟩⟩

/-- Every source family retained by an installed declaration has its exact
abstract header constant at the final environment. -/
theorem installedInductCertificate_ownerLookup
    (H : VEnv.InstalledInductCertificate env decl)
    (howner : owner ∈ decl.types) :
    env.constants owner.name = some owner.toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : owner.toVConstVal ∈ block.types := by
      rw [Hcompile.types]
      simp only [VInductDecl.typeConstants, List.mem_map]
      exact ⟨owner, howner, rfl⟩
    have hlookup := addConstVals_lookup htypes hmember
    have hctorLookup : envCtors.constants owner.name =
        some owner.toVConstant :=
      (VEnv.addConstVals_le hctors).constants hlookup
    have hrecursorLookup : envRecursors.constants owner.name =
        some owner.toVConstant :=
      (VEnv.addConstVals_le hrecursors).constants hctorLookup
    have installed_eq :
        installed = envRecursors.addDefEqRules block.rules := by
      apply Option.some.inj
      calc
        some installed = VInductBlock.install base block := Hinstall.symm
        _ = some (envRecursors.addDefEqRules block.rules) := by
          simp [VInductBlock.install, htypes, hctors, hrecursors]
    apply hle.constants
    rw [installed_eq]
    exact VEnv.addDefEqRules_le.constants hrecursorLookup

/-- Every source constructor retained by an installed declaration has its
exact abstract constant at the final environment.  Projection inference uses
this lookup together with `CheckingEnv.find?_uniq` to translate the concrete
`ConstructorVal.type`; no constructor-type observation is added to the
projection relation. -/
theorem installedInductCertificate_constructorLookup
    (H : VEnv.InstalledInductCertificate env decl)
    (howner : owner ∈ decl.types) (hctor : ctor ∈ owner.ctors) :
    env.constants ctor.name = some ctor.toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : ctor ∈ block.ctors := by
      rw [Hcompile.ctors]
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨owner, howner, hctor⟩
    have hlookup := addConstVals_lookup hctors hmember
    have hrecursorLookup : envRecursors.constants ctor.name =
        some ctor.toVConstant :=
      (VEnv.addConstVals_le hrecursors).constants hlookup
    have installed_eq :
        installed = envRecursors.addDefEqRules block.rules := by
      apply Option.some.inj
      calc
        some installed = VInductBlock.install base block := Hinstall.symm
        _ = some (envRecursors.addDefEqRules block.rules) := by
          simp [VInductBlock.install, htypes, hctors, hrecursors]
    apply hle.constants
    rw [installed_eq]
    exact VEnv.addDefEqRules_le.constants hrecursorLookup

end ProjectionMetadata

end Lean4Lean
