import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstruction

/-! Translation facts of the recursive shapes of the consumed generation.

`H.consumedGeneration` is the explicit witness `consumedGenerationOf`, whose
signature is `H.consumedSignature H.argumentUniverses`.  The recursive shapes
of its constructors were read off the checked recursor type and returned to
the declaration's universes; the facts retained by that construction
(`MinorShapeSpec`, `RecursiveShapeSources`) are exported here against the
retained blueprint calls `B.recursiveCalls[j]!` from which
`RecRuleBlueprint.build` produces the installed rules.

The sources are stated in one closed form:
* the `i`-th explicit binder source is the `i`-th literal domain of the call's
  argument telescope `C.lctx.mkForall C.args (.sort .zero)` (`Expr.forallDomainList`,
  so its loose variables `0, …, i - 1` are the earlier arguments), closed over the
  fields before `pos` at depth `i` and over the parameters at depth `pos + i`;
* the index sources are `C.targetIndices`, closed over the call arguments by
  `abstractN (ExprArrayFVarIds C.args)`, then over the fields before `pos` and
  the parameters at depths `C.args.size` and `pos + C.args.size`. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The recursive shapes of a consumed constructor, for any universe support. -/
theorem CompletedRecursorConstruction.consumedSignature_shapeTranslations
    (H : CompletedRecursorConstruction R) (HU : H.ArgumentUniverses)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hk : recursorMinorOffset indTypes owner + localIndex <
      (H.consumedSignature HU).constructors.size) :
    let s := H.consumedSignature HU
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let B := H.recInfos[owner]!.ruleBlueprints[localIndex]!
    let ctor := s.constructors[recursorMinorOffset indTypes owner + localIndex]
    let rf := InductiveSignature.Instance.recursiveFields (s := s) ctor
    s.fieldTypes ctor = H.sourceFields owner howner localIndex hlocal ∧
    rf.length = S.hypotheses.size ∧
    ∀ j (hj : j < rf.length),
      let pos := rf[j].1
      let r := rf[j].2
      let C := B.recursiveCalls[j]!
      j < B.recursiveCalls.size ∧
      ∃ hpos : pos < S.fields_bound.fvars.length,
        S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) ∧
        r.target.val = C.targetTypeIdx ∧
        r.binders.length = C.args.size ∧
        C.major = S.recursiveFields[j]! ∧
        C.template = C.lctx.mkLambda C.args
          ((mkAppN (.bvar C.args.size) C.targetIndices).app (mkAppN C.major C.args)) ∧
        (∀ i (hi : i < r.binders.length),
          TrExprS R.context.venv c.lparams
            (abstractForallContext (R.parameterScope.toCtx.reverse ++
              (s.fieldTypes ctor).take pos ++ r.binders.take i) [])
            (((Expr.forallDomainList C.args.size
                (C.lctx.mkForall C.args (.sort .zero)))[i]!.abstractList
              (S.fields_bound.fvars.take pos) i).abstractList H.params.fvars (pos + i))
            (r.binders[i]'hi)) ∧
        List.Forall₂
          (TrExprS R.context.venv c.lparams
            (abstractForallContext (R.parameterScope.toCtx.reverse ++
              (s.fieldTypes ctor).take pos ++ r.binders) []))
          (C.targetIndices.toList.map fun e =>
            ((e.abstractN (ExprArrayFVarIds C.args)).abstractList
              (S.fields_bound.fvars.take pos) C.args.size).abstractList H.params.fvars
                (pos + C.args.size))
          r.indices := by
  intro s S B ctor rf
  have hctor : ctor = H.consumedConstructorAt HU owner howner localIndex hlocal :=
    H.consumedSignature_constructor HU owner howner localIndex hlocal hk
  have hft : s.fieldTypes ctor = H.sourceFields owner howner localIndex hlocal := by
    rw [hctor]; exact H.consumedConstructorAt_fieldTypes HU owner howner localIndex hlocal
  have hrec : rf = H.consumedShapes HU owner howner localIndex hlocal := by
    simp only [rf]
    rw [hctor]
    exact H.consumedConstructorAt_recursiveFields HU owner howner localIndex hlocal
  have hspec := H.consumedShapes_spec HU owner howner localIndex hlocal
  refine ⟨hft, by rw [hrec]; exact hspec.2.1, ?_⟩
  intro j hj
  have hj' : j < (H.consumedShapes HU owner howner localIndex hlocal).length := by
    rw [hrec] at hj; exact hj
  have hx : rf[j] = (H.consumedShapes HU owner howner localIndex hlocal)[j] :=
    List.getElem_of_eq hrec hj
  obtain ⟨hpos, hfield, hsrc⟩ := hspec.2.2.2.2 j hj'
  dsimp only [CompletedRecursorConstruction.RecursiveShapeSources] at hsrc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hsrc
  dsimp only
  rw [hx, hft]
  exact ⟨h1, hpos, hfield, h2, h3, h4, h5, h6, h7⟩

/-- The recursive shapes of the consumed generation's constructor for minor
`(owner, localIndex)`: for every induction hypothesis `j`, the retained
blueprint call `C := B.recursiveCalls[j]!` is the call of this hypothesis
(same target, arity, major and template), and the shape's binders and indices
are the declaration-universe translations, in the small context
`parameters ++ fields.take pos ++ binders`, of `C`'s argument domains and
target indices closed over the earlier fields and the parameters. -/
theorem CompletedRecursorConstruction.consumedGeneration_shapeTranslations
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let G := H.consumedGeneration
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let k := recursorMinorOffset indTypes owner + localIndex
    let B := H.recInfos[owner]!.ruleBlueprints[localIndex]!
    ∃ hk : k < G.signature.constructors.size,
      let ctor := G.signature.constructors[k]
      let rf := InductiveSignature.Instance.recursiveFields (s := G.signature) ctor
      G.signature.fieldTypes ctor = H.sourceFields owner howner localIndex hlocal ∧
      rf.length = S.hypotheses.size ∧
      ∀ j (hj : j < rf.length),
        let pos := rf[j].1
        let r := rf[j].2
        let C := B.recursiveCalls[j]!
        j < B.recursiveCalls.size ∧
        ∃ hpos : pos < S.fields_bound.fvars.length,
          S.recursiveFields[j]! = .fvar (S.fields_bound.fvars[pos]'hpos) ∧
          r.target.val = C.targetTypeIdx ∧
          r.binders.length = C.args.size ∧
          C.major = S.recursiveFields[j]! ∧
          C.template = C.lctx.mkLambda C.args
            ((mkAppN (.bvar C.args.size) C.targetIndices).app (mkAppN C.major C.args)) ∧
          (∀ i (hi : i < r.binders.length),
            TrExprS R.context.venv c.lparams
              (abstractForallContext (R.parameterScope.toCtx.reverse ++
                (G.signature.fieldTypes ctor).take pos ++ r.binders.take i) [])
              (((Expr.forallDomainList C.args.size
                  (C.lctx.mkForall C.args (.sort .zero)))[i]!.abstractList
                (S.fields_bound.fvars.take pos) i).abstractList H.params.fvars (pos + i))
              (r.binders[i]'hi)) ∧
          List.Forall₂
            (TrExprS R.context.venv c.lparams
              (abstractForallContext (R.parameterScope.toCtx.reverse ++
                (G.signature.fieldTypes ctor).take pos ++ r.binders) []))
            (C.targetIndices.toList.map fun e =>
              ((e.abstractN (ExprArrayFVarIds C.args)).abstractList
                (S.fields_bound.fvars.take pos) C.args.size).abstractList H.params.fvars
                  (pos + C.args.size))
            r.indices := by
  intro G S k B
  have hk : k < (H.consumedSignature H.argumentUniverses).constructors.size := by
    simp only [CompletedRecursorConstruction.consumedSignature, Array.size_ofFn]
    exact H.sourceMinorOffsetBound owner howner localIndex hlocal
  exact ⟨hk, H.consumedSignature_shapeTranslations H.argumentUniverses owner howner localIndex
    hlocal hk⟩

end Lean4Lean.VerifyInductive
