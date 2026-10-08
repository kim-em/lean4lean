import Lean4Lean.Verify.TypeChecker.FrameWHNF

/-!
# Frame lemma: definitional equality
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {G : FVarId → Prop}

theorem RecM.Framed.orM {x y : RecM Bool} (hx : RecM.Framed G x fun _ => True)
    (hy : RecM.Framed G y fun _ => True) : RecM.Framed G (x <||> y) fun _ => True := by
  unfold _root_.orM
  refine hx.bind fun b _ => ?_
  split
  · exact .pure trivial
  · exact hy

theorem RecM.Framed.toLBoolM {x : RecM Bool} (hx : RecM.Framed G x fun _ => True) :
    RecM.Framed G (toLBoolM x) fun _ => True := by
  unfold Lean.toLBoolM
  exact hx.bind fun _ _ => .pure trivial

theorem Inner.OGF.get! {o : Option Expr} (h : Inner.OGF G o) : GF G o.get! := by
  cases o with
  | none => simp only [Option.get!]; exact GF.panic
  | some e => exact h rfl

/-- The expressions carried by a reduction status are ghost-free. -/
def RSGF (G : FVarId → Prop) : ReductionStatus → Prop
  | .continue tn sn | .unknown tn sn | .false tn sn => GF G tn ∧ GF G sn
  | .true => True

namespace Inner

theorem isDefEqLambda.framed : ∀ {t s : Expr} {subst : Array Expr}, GF G t → GF G s →
    FVArr G subst → RecM.Framed G (isDefEqLambda t s subst) fun _ => True
  | t, s, subst, ht, hs, hsub => by
    unfold isDefEqLambda
    split
    · rename_i tDom tBody _ name sDom sBody bi
      have hsT : GF G (sDom.instantiateRev subst) := hs.1.instantiateRev hsub.gfArr
      have k : ∀ o : Option Expr, OGF G o → RecM.Framed G
          (withLocalDecl name bi (o.getD (sDom.instantiateRev subst)) fun fv =>
            isDefEqLambda tBody sBody (subst.push fv)) fun _ => True := by
        intro o ho
        refine .withLocalDecl ?_ fun id hid => isDefEqLambda.framed ht.2 hs.2 (hsub.push hid)
        cases o with
        | none => exact hsT
        | some x => exact ho rfl
      split
      · exact (RecM.Framed.pure OGF.none).bind k
      · refine (RecM.Framed.isDefEq (ht.1.instantiateRev hsub.gfArr) hsT).bind fun _ _ => ?_
        split
        · exact .pure trivial
        · exact (RecM.Framed.pure (OGF.some hsT)).bind k
    · exact RecM.Framed.isDefEq (ht.instantiateRev hsub.gfArr) (hs.instantiateRev hsub.gfArr)

theorem isDefEqForall.framed : ∀ {t s : Expr} {subst : Array Expr}, GF G t → GF G s →
    FVArr G subst → RecM.Framed G (isDefEqForall t s subst) fun _ => True
  | t, s, subst, ht, hs, hsub => by
    unfold isDefEqForall
    split
    · rename_i tDom tBody _ name sDom sBody bi
      have hsT : GF G (sDom.instantiateRev subst) := hs.1.instantiateRev hsub.gfArr
      have k : ∀ o : Option Expr, OGF G o → RecM.Framed G
          (withLocalDecl name bi (o.getD (sDom.instantiateRev subst)) fun fv =>
            isDefEqForall tBody sBody (subst.push fv)) fun _ => True := by
        intro o ho
        refine .withLocalDecl ?_ fun id hid => isDefEqForall.framed ht.2 hs.2 (hsub.push hid)
        cases o with
        | none => exact hsT
        | some x => exact ho rfl
      split
      · exact (RecM.Framed.pure OGF.none).bind k
      · refine (RecM.Framed.isDefEq (ht.1.instantiateRev hsub.gfArr) hsT).bind fun _ _ => ?_
        split
        · exact .pure trivial
        · exact (RecM.Framed.pure (OGF.some hsT)).bind k
    · exact RecM.Framed.isDefEq (ht.instantiateRev hsub.gfArr) (hs.instantiateRev hsub.gfArr)

theorem quickIsDefEq.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (quickIsDefEq t s useHash) fun _ => True := by
  unfold quickIsDefEq
  refine RecM.Framed.bind (RecM.Framed.modifyGet ?_) fun b _ => ?_
  · intro st hst
    obtain ⟨⟩ := st
    exact ⟨⟨hst.1, hst.2, hst.3, hst.4, hst.5, hst.6⟩, .rfl⟩
  split
  · exact .pure trivial
  split
  · exact .toLBoolM (isDefEqLambda.framed ht hs FVArr.empty)
  · exact .toLBoolM (isDefEqForall.framed ht hs FVArr.empty)
  · exact .pure trivial
  · exact .toLBoolM (RecM.Framed.isDefEq ht hs)
  · exact .panic trivial
  · exact .pure trivial
  · exact .pure trivial

theorem isDefEqArgs.framed : ∀ {t s : Expr}, GF G t → GF G s →
    RecM.Framed G (isDefEqArgs t s) fun _ => True
  | t, s, ht, hs => by
    unfold isDefEqArgs
    split
    · rename_i tf ta sf sa
      refine (RecM.Framed.isDefEq ht.2 hs.2).bind fun _ _ => ?_
      split
      · exact .pure trivial
      · exact isDefEqArgs.framed (t := tf) (s := sf) ht.1 hs.1
    all_goals exact .pure trivial

theorem tryEtaExpansionCore.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (tryEtaExpansionCore t s) fun _ => True := by
  unfold tryEtaExpansionCore
  split
  · refine (RecM.Framed.inferType hs).bind fun _ h => (RecM.Framed.whnf h).bind fun _ h => ?_
    split
    · exact RecM.Framed.isDefEq ht ⟨h.1, hs, trivial⟩
    · exact .pure trivial
  · exact .pure trivial

theorem tryEtaExpansion.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (tryEtaExpansion t s) fun _ => True :=
  .orM (tryEtaExpansionCore.framed ht hs) (tryEtaExpansionCore.framed hs ht)

theorem tryEtaStructCore.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (tryEtaStructCore t s) fun _ => True := by
  unfold tryEtaStructCore
  split <;> try exact .pure trivial
  refine RecM.Framed.getEnv.bind fun env _ => ?_
  refine (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  rename_i fInfo
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  refine (RecM.Framed.inferType ht).bind fun tType htT => ?_
  refine (RecM.Framed.inferType hs).bind fun _ hsT => ?_
  refine (RecM.Framed.isDefEq htT hsT).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  refine (RecM.Framed.inferType htT).bind fun _ h => (RecM.Framed.whnf h).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  have hargs := hs.getAppArgs
  dsimp only
  generalize fInfo.numParams = i
  induction i using tryEtaStructCore.loop.induct (args := s.getAppArgs) with
  | case1 i h ih =>
    unfold tryEtaStructCore.loop; rw [dif_pos h]
    refine (RecM.Framed.isDefEq (t := .proj _ _ t) ht (hargs.getElem h)).bind fun _ _ => ?_
    split <;> first | exact .pure trivial | exact ih
  | case2 i h => unfold tryEtaStructCore.loop; rw [dif_neg h]; exact .pure trivial

theorem tryEtaStruct.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (tryEtaStruct t s) fun _ => True :=
  .orM (tryEtaStructCore.framed ht hs) (tryEtaStructCore.framed hs ht)

theorem isDefEqApp.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (isDefEqApp t s) fun _ => True := by
  unfold isDefEqApp
  split <;> try exact .pure trivial
  rw [Expr.withApp_eq, Expr.withApp_eq]
  have htA := ht.getAppArgs
  have hsA := hs.getAppArgs
  split <;> try exact .pure trivial
  rename_i hsz
  refine (RecM.Framed.isDefEq ht.getAppFn hs.getAppFn).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  generalize 0 = i
  induction i using isDefEqApp.loop.induct (tArgs := t.getAppArgs) (sArgs := s.getAppArgs) (_h := hsz) with
  | case1 i h ih =>
    unfold isDefEqApp.loop; rw [dif_pos h]
    refine (RecM.Framed.isDefEq (htA.getElem h) (hsA.getElem (hsz ▸ h))).bind fun _ _ => ?_
    split <;> first | exact .pure trivial | exact ih
  | case2 i h => unfold isDefEqApp.loop; rw [dif_neg h]; exact .pure trivial

theorem isDefEqProofIrrel.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (isDefEqProofIrrel t s) fun _ => True := by
  unfold isDefEqProofIrrel
  refine (RecM.Framed.inferType ht).bind fun _ htT => (isProp.framed htT).bind fun _ _ => ?_
  split <;> first
    | exact .pure trivial
    | exact (RecM.Framed.inferType hs).bind fun _ h => .toLBoolM (RecM.Framed.isDefEq htT h)

theorem cacheFailure.framed : M.Framed G (cacheFailure t s) fun _ => True := by
  unfold cacheFailure
  refine M.Framed.modify fun st hst => ⟨⟨hst.1, hst.2, hst.3, hst.4, hst.5, hst.6⟩, .rfl⟩

theorem tryUnfoldProjApp.framed (he : GF G e) :
    RecM.Framed G (tryUnfoldProjApp e) (OGF G) := by
  unfold tryUnfoldProjApp; dsimp only
  split
  · exact .pure OGF.none
  · refine (RecM.Framed.whnfCore he).bind fun _ h => .pure ?_
    split
    · exact OGF.some h
    · exact OGF.none

theorem lazyDeltaReductionStep.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (lazyDeltaReductionStep t s) (RSGF G) := by
  unfold lazyDeltaReductionStep
  refine RecM.Framed.getEnv.bind fun env _ => ?_
  extract_lets delta cont
  have hdelta : ∀ e, GF G e → RecM.Framed G (delta e) (GF G) := fun e he =>
    (unfoldDefinition.framed he).bind fun _ h => RecM.Framed.whnfCore h.get!
  have hcont : ∀ tn sn, GF G tn → GF G sn → RecM.Framed G (cont tn sn) (RSGF G) :=
    fun tn sn htn hsn => (quickIsDefEq.framed htn hsn).bind fun _ _ => .pure (by
      split
      · exact ⟨htn, hsn⟩
      · trivial
      · exact ⟨htn, hsn⟩)
  split
  · exact .pure ⟨ht, hs⟩
  · refine (tryUnfoldProjApp.framed hs).bind fun o ho => ?_
    split
    · exact hcont _ _ ht (ho rfl)
    · exact (hdelta _ ht).bind fun _ h => hcont _ _ h hs
  · refine (tryUnfoldProjApp.framed ht).bind fun o ho => ?_
    split
    · exact hcont _ _ (ho rfl) hs
    · exact (hdelta _ hs).bind fun _ h => hcont _ _ ht h
  · extract_lets hts hss
    split
    · exact (hdelta _ hs).bind fun _ h => hcont _ _ ht h
    split
    · exact (hdelta _ ht).bind fun _ h => hcont _ _ h hs
    refine RecM.Framed.get.bind fun _ _ => ?_
    have hjp := (hdelta _ ht).bind fun _ h1 => (hdelta _ hs).bind fun _ h2 => hcont _ _ h1 h2
    have hjp' := (RecM.Framed.lift (cacheFailure.framed (G := G) (t := t) (s := s))).bind
      fun _ _ => hjp
    split
    · split
      · refine (isDefEqArgs.framed ht hs).bind fun _ _ => ?_
        split <;> first | exact .pure trivial | exact hjp'
      · exact hjp'
    · exact hjp

theorem isDefEqOffset.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (isDefEqOffset t s) fun _ => True := by
  unfold isDefEqOffset
  split
  · exact .pure trivial
  split
  · rename_i t' s' h1 h2
    have gf : ∀ {e e' : Expr}, GF G e → isNatSuccOf? e = some e' → GF G e' := by
      intro e e' he h
      unfold isNatSuccOf? at h
      split at h
      · cases h; trivial
      · cases h; exact he.2
      · cases h
    exact .toLBoolM (RecM.Framed.isDefEqCore (gf ht h1) (gf hs h2))
  · exact .pure trivial

theorem _root_.Lean4Lean.TypeChecker.RSGF.bool (ht : GF G t) (hs : GF G s) :
    RSGF G (ReductionStatus.bool t s b) := by
  cases b
  · exact ⟨ht, hs⟩
  · trivial

theorem lazyDeltaReduction.loop.framed : ∀ (fuel : Nat) {t s : Expr}, GF G t → GF G s →
    RecM.Framed G (lazyDeltaReduction.loop t s fuel) (RSGF G) := by
  intro fuel
  induction fuel with
  | zero => intro t s _ _; unfold lazyDeltaReduction.loop; exact .throw
  | succ fuel ih =>
    intro t s ht hs
    unfold lazyDeltaReduction.loop
    refine (isDefEqOffset.framed ht hs).bind fun r _ => ?_
    split
    · exact .pure (.bool ht hs)
    refine RecM.Framed.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.1]) fun _ _ _ => ?_
    have hjp : RecM.Framed G (do
        let env ← liftM getEnv
        let __do_lift ← liftM (reduceNative env t)
        match __do_lift with
          | some tn' => do
            let __do_lift ← isDefEqCore tn' s
            pure (ReductionStatus.bool tn' s __do_lift)
          | x => do
            let __do_lift ← liftM (reduceNative env s)
            match __do_lift with
              | some sn' => do
                let __do_lift ← isDefEqCore t sn'
                pure (ReductionStatus.bool t sn' __do_lift)
              | x => do
                let __do_lift ← lazyDeltaReductionStep t s
                match __do_lift with
                  | ReductionStatus.continue tn sn => lazyDeltaReduction.loop tn sn fuel
                  | r => pure r) (RSGF G) := by
      refine RecM.Framed.getEnv.bind fun env _ => ?_
      refine (RecM.Framed.liftExcept (reduceNative_gf (G := G))).bind fun o ho => ?_
      split
      · exact (RecM.Framed.isDefEqCore (ho rfl) hs).bind fun _ _ => .pure (.bool (ho rfl) hs)
      refine (RecM.Framed.liftExcept (reduceNative_gf (G := G))).bind fun o ho => ?_
      split
      · exact (RecM.Framed.isDefEqCore ht (ho rfl)).bind fun _ _ => .pure (.bool ht (ho rfl))
      refine (lazyDeltaReductionStep.framed ht hs).bind fun r hr => ?_
      split
      · exact ih hr.1 hr.2
      · exact .pure hr
    split
    · refine (reduceNat.framed ht).bind fun o ho => ?_
      split
      · exact (RecM.Framed.isDefEqCore (ho rfl) hs).bind fun _ _ => .pure (.bool (ho rfl) hs)
      refine (reduceNat.framed hs).bind fun o ho => ?_
      split
      · exact (RecM.Framed.isDefEqCore ht (ho rfl)).bind fun _ _ => .pure (.bool ht (ho rfl))
      · exact hjp
    · exact hjp

theorem lazyDeltaReduction.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (lazyDeltaReduction t s) (RSGF G) := by
  unfold lazyDeltaReduction
  exact RecM.Framed.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.2.2]) fun _ _ _ =>
    lazyDeltaReduction.loop.framed _ ht hs

theorem lazyDeltaProjReduction.finish.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (lazyDeltaProjReduction.finish structName idx t s) fun _ => True := by
  unfold lazyDeltaProjReduction.finish
  refine (reduceProjCore.framed ht).bind fun o ho => ?_
  have k := RecM.Framed.isDefEqCore (G := G) ht hs
  split
  · refine (reduceProjCore.framed hs).bind fun o' ho' => ?_
    split
    · exact RecM.Framed.isDefEqCore (ho rfl) (ho' rfl)
    · exact k
  · exact k

theorem lazyDeltaProjReduction.loop.framed : ∀ (fuel : Nat) {t s : Expr}, GF G t → GF G s →
    RecM.Framed G (lazyDeltaProjReduction.loop structName idx t s fuel) fun _ => True := by
  intro fuel
  induction fuel with
  | zero => intro t s _ _; unfold lazyDeltaProjReduction.loop; exact .throw
  | succ fuel ih =>
    intro t s ht hs
    unfold lazyDeltaProjReduction.loop
    refine (lazyDeltaReductionStep.framed ht hs).bind fun r hr => ?_
    split
    · exact ih hr.1 hr.2
    · exact .pure trivial
    · exact finish.framed hr.1 hr.2
    · exact finish.framed hr.1 hr.2

theorem lazyDeltaProjReduction.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (lazyDeltaProjReduction structName t s idx) fun _ => True := by
  unfold lazyDeltaProjReduction
  exact RecM.Framed.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.2.2]) fun _ _ _ =>
    lazyDeltaProjReduction.loop.framed _ ht hs

theorem tryStringLitExpansionCore.framed (hs : GF G s) :
    RecM.Framed G (tryStringLitExpansionCore t s) fun _ => True := by
  unfold tryStringLitExpansionCore
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  exact .toLBoolM (RecM.Framed.isDefEqCore FVarsIn.strLitToConstructor hs)

theorem tryStringLitExpansion.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (tryStringLitExpansion t s) fun _ => True := by
  unfold tryStringLitExpansion
  refine (tryStringLitExpansionCore.framed hs).bind fun _ _ => ?_
  split
  · exact tryStringLitExpansionCore.framed ht
  · exact .pure trivial

theorem isDefEqUnitLike.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (isDefEqUnitLike t s) fun _ => True := by
  unfold isDefEqUnitLike
  refine (RecM.Framed.inferType ht).bind fun _ h => (RecM.Framed.whnf h).bind fun tType htT => ?_
  split <;> try exact .pure trivial
  refine RecM.Framed.getEnv.bind fun env _ => ?_
  refine (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  refine (RecM.Framed.liftExcept (R := fun _ => True) fun _ _ => trivial).bind fun _ _ => ?_
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  split <;> try exact .pure trivial
  exact (RecM.Framed.inferType hs).bind fun _ h => RecM.Framed.isDefEqCore htT h

theorem isDefEqCore'.framed (ht : GF G t) (hs : GF G s) :
    RecM.Framed G (isDefEqCore' t s) fun _ => True := by
  unfold isDefEqCore'
  refine (quickIsDefEq.framed ht hs).bind fun _ _ => ?_
  split
  · exact .pure trivial
  refine RecM.Framed.read (fun c₁ c₂ h => by simp only [h.ctx_eq.2.2.1]) fun _ _ _ => ?_
  extract_lets jp1
  have hjp1 : RecM.Framed G (jp1 ()) fun _ => True := by
    dsimp (config := {zeta := false}) only [jp1]
    refine (RecM.Framed.whnfCore ht).bind fun tn htn =>
      (RecM.Framed.whnfCore hs).bind fun sn hsn => ?_
    extract_lets jp2
    have hjp2 : RecM.Framed G (jp2 ()) fun _ => True := by
      dsimp (config := {zeta := false}) only [jp2]
      refine (isDefEqProofIrrel.framed htn hsn).bind fun _ _ => ?_
      split
      · exact .pure trivial
      refine (lazyDeltaReduction.framed htn hsn).bind fun r hr => ?_
      split
      · exact .panic trivial
      · exact .pure trivial
      · exact .pure trivial
      rename_i tn sn
      have htn : GF G tn := hr.1
      have hsn : GF G sn := hr.2
      extract_lets jp3
      have hjp3 : RecM.Framed G (jp3 ()) fun _ => True := by
        dsimp (config := {zeta := false}) only [jp3]
        refine (RecM.Framed.whnfCore htn).bind fun _ htnn =>
          (RecM.Framed.whnfCore hsn).bind fun _ hsnn => ?_
        split
        · exact RecM.Framed.isDefEqCore htnn hsnn
        refine (isDefEqApp.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryEtaExpansion.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryEtaStruct.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (tryStringLitExpansion.framed htn hsn).bind fun _ _ => ?_
        split; · exact .pure trivial
        refine (isDefEqUnitLike.framed htn hsn).bind fun _ _ => ?_
        split <;> exact .pure trivial
      split
      · split
        · exact .pure trivial
        · exact hjp3
      · split
        · exact .pure trivial
        · exact hjp3
      · split
        · rename_i _ _ te _ _ se _
          refine (lazyDeltaProjReduction.framed (t := te) (s := se) htn hsn).bind fun _ _ => ?_
          split
          · exact .pure trivial
          · exact hjp3
        · exact hjp3
      · exact hjp3
    split
    · refine (quickIsDefEq.framed htn hsn).bind fun _ _ => ?_
      split
      · exact .pure trivial
      · exact hjp2
    · exact hjp2
  split
  · refine (RecM.Framed.whnf ht).bind fun _ _ => ?_
    split
    · exact .pure trivial
    · exact hjp1
  · exact hjp1

end Inner
end Lean4Lean.TypeChecker
