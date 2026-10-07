import Lean4Lean.Theory.Typing.ProjectionCornerWalk
import Lean4Lean.Theory.Typing.TelescopeTransport
import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Inductive.SingletonCompilation
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.CanonicalChoice

/-!
# An inhabitant of a field type of a non-eliminable structure field

At a typed major `e : S params` of a registered structure `S`, the binder type `D` that the
projection walk reaches for a field whose projection fails the universe guard is inhabited,
when the environment has canonical choice and `S` can be eliminated into `Prop`: the recursor of
`S` with the constant motive `fun _ => Nonempty D` and the minor premise
`fun fields => Nonempty.intro field` gives `Nonempty D`, and `Classical.choice` gives a term of
`D`. The minor premise is typed because every projection used by `D` is a proof field
(`VProjectionInfo.field_of_walk`).
-/

namespace Lean4Lean
open VExpr VEnv InductiveSignature

namespace InductiveSignature.NativeRecursorData
variable {env : VEnv} {data : NativeRecursorData}

/-- The recursor of an ordinary (one-family) declaration is installed with its generated type,
and the declaration's constructor is, in the empty context, definitionally the installed
constructor. -/
theorem NativeRecursorRegistered.ordinary (H : NativeRecursorRegistered env data)
    (hfam : data.schema.signature.families.size = 1)
    (hcs : data.schema.signature.constructors.size = 1)
    (i : Fin data.schema.signature.constructors.size)
    {ctorName : Name} {ctor : VConstant}
    (hname : data.schema.signature.constructors[i].name = ctorName)
    (hctor : env.constants ctorName = some ctor) :
    env.constants data.name =
      some ⟨data.uvars, data.nativeInstance.recursorType data.owner⟩ ∧
    ctor.uvars = data.schema.signature.uvars ∧
    ∃ envTypes, envTypes ≤ env ∧ envTypes.IsDefEqU data.schema.signature.uvars []
      (data.schema.signature.constructorType data.schema.signature.constructors[i]) ctor.type := by
  have Hcopy := H
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, hbase, hr, _, hu, hl, ht, hi, he⟩ := H
  have hrest : data.schema.restoration = {} := hr.trans (hdata.restoration_of_singleton hfam)
  have haux := hdata.noAuxiliaries_of_singleton hfam
  subst haux
  refine ⟨?_, ?_⟩
  · have hgen : data.recursorType = some (data.nativeInstance.recursorType data.owner) := by
      simp [recursorType, hrest]
    exact Hcopy.recursorType hgen
  -- the correspondence of the normalized and source declarations
  obtain ⟨envTypes, direct, hadd, hdirect, _, hcorr⟩ := hdata.correspondence
  have hdir : direct = [] := by
    simpa using hdirect.symm
  subst hdir
  simp only [List.append_nil] at hcorr
  have hrest' : compilationRestoration source [] = {} := hdata.restoration_of_singleton hfam
  rw [hrest'] at hcorr
  -- the single family and constructor of the signature
  have hfams : data.schema.signature.families.toList = [data.schema.signature.families[0]'(by omega)] :=
    Instance.toList_of_size_one _ hfam ⟨0, by omega⟩
  have hctors : data.schema.signature.constructors.toList = [data.schema.signature.constructors[i]] :=
    Instance.toList_of_size_one _ hcs i
  have hown : (data.schema.signature.constructors[i]).owner.val = 0 := by
    have := (data.schema.signature.constructors[i]).owner.isLt; omega
  simp only [declaration, hfams, hctors, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
    List.map_nil, List.filterMap_cons, List.filterMap_nil, hown, if_true] at hcorr
  obtain ⟨srcS, hsrcS⟩ : ∃ srcS, source.types = [srcS] := by
    have h := hcorr
    generalize source.types = st at h
    cases h with
    | cons _ t => cases t; exact ⟨_, rfl⟩
  rw [hsrcS] at hcorr
  have hRF := (List.forall₂_cons.1 hcorr).1
  obtain ⟨srcC, hsrcC⟩ : ∃ srcC, srcS.ctors = [srcC] := by
    have h := hRF.constructors
    generalize srcS.ctors = sc at h
    cases h with
    | cons _ t => cases t; exact ⟨_, rfl⟩
  have hCC := hRF.constructors
  rw [hsrcC] at hCC
  obtain ⟨hcn, hcu, restored, hres, hdef⟩ := (List.forall₂_cons.1 hCC).1
  simp only [Restoration.expr_empty, Option.some.injEq] at hres
  subst hres
  -- the source constructor is the installed constructor
  have hinstC : env.constants srcC.name = some srcC.toVConstant := by
    refine he.constants (VInductBlock.install_ctor_lookup hi ?_)
    rw [hdata.ctors, VInductDecl.constructorConstants, hsrcS]
    simp [hsrcC]
  have hsame : srcC.name = ctorName := by rw [← hcn, ← hname]
  rw [hsame, hctor] at hinstC
  cases Option.some.inj hinstC
  refine ⟨by simpa using hcu.symm, envTypes, ?_, ?_⟩
  · -- the checked headers are installed
    have hinst := hi
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinst
    obtain ⟨e1, he1, e2, he2, e3, he3, rfl⟩ := hinst
    have hle1 : e1 ≤ env := (VEnv.addConstVals_le he2).trans
      (VEnv.addProjections_le.trans ((VEnv.addConstVals_le he3).trans
        (VEnv.addDefEqRules_le.trans he)))
    rw [hdata.types] at he1
    exact (VEnv.addConstVals_mono hbase hadd he1).trans hle1
  · have huv : srcS.uvars = data.schema.signature.uvars := by
      rw [← hRF.universes]
    have : source.uvars = data.schema.signature.uvars := by
      rw [← hdata.uvars, hdata.model.uvars]
    rw [← this]
    simpa using hdef

end InductiveSignature.NativeRecursorData
end Lean4Lean
