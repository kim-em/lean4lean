import Lean4Lean.Theory.Typing.SingletonExtraction
import Lean4Lean.Theory.Inductive.InstanceSpecialize
import Lean4Lean.Theory.Inductive.HypothesisTyping

/-! # Typing of a singleton family's telescopes, read off its recursor

The syntactic field and index telescopes of a normalized signature are only related to
the declared headers up to definitional equality in larger contexts, so their typing in
their own contexts cannot be read off the family and constructor headers (context
strengthening). The generated recursor type is typed syntactically: its motive is formed
over the index telescope, and its minor premise over the field telescope and the
induction hypotheses, beneath the motive. With elimination into `Prop` the motive is
instantiated at the constant family of the proposition `∀ p : Prop, p → p`, every
induction hypothesis is then inhabited, and instantiating the minor premise's context at
these inhabitants yields the field telescope's own typing, together with the typing of
the constructor's result indices along the index telescope. -/

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open VExpr

namespace VExpr

/-- The proposition `∀ p : Prop, p → p`. -/
def trueTy : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))

/-- Its proof `fun p x => x`. -/
def truePf : VExpr := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

theorem trueTy_closed : trueTy.ClosedN 0 := by simp [trueTy, ClosedN]
theorem truePf_closed : truePf.ClosedN 0 := by simp [truePf, ClosedN]

/-- Instantiating the outer variables of a term lifted past some of them skips those. -/
theorem liftN_instOuter_drop {e : VExpr} {X Y Z : List VExpr}
    (he : e.ClosedN (X.length + Z.length)) :
    (e.liftN Y.length Z.length).instOuter (X ++ Y ++ Z) = e.instOuter (X ++ Z) := by
  rw [VExpr.instOuter_eq_subst, VExpr.instOuter_eq_subst, VExpr.liftN_subst]
  apply VExpr.subst_congr_closedN he
  intro i hi
  simp only [VExpr.Subst.lift_l, Lift.liftVar_consN_skipN]
  have hX : (X ++ Z).length = X.length + Z.length := by simp
  have hXYZ : (X ++ Y ++ Z).length = X.length + Y.length + Z.length := by simp; omega
  by_cases hik : i < Z.length
  · rw [liftVar_lt hik, VExpr.Subst.ofList_lt _ (by omega), VExpr.Subst.ofList_lt _ (by omega)]
    rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
    congr 1; simp; omega
  · rw [liftVar_le (Nat.le_of_not_gt hik), VExpr.Subst.ofList_lt _ (by omega),
      VExpr.Subst.ofList_lt _ (by omega)]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by omega)]
    congr 1; omega

end VExpr

namespace VEnv
variable {env : VEnv} {U : Nat}

theorem HasType.trueTy :
    env.HasType U Γ VExpr.trueTy (.sort .zero) := by
  have h0 : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by simp [VLevel.WF])
  have h1 : env.HasType U (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : env.HasType U (.bvar 0 :: .sort .zero :: Γ) (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have h := HasType.forallE h0 (HasType.forallE h1 h2)
  exact .defeqDF (.sortDF (by simp [VLevel.WF]) (by simp [VLevel.WF])
    (by funext; simp [VLevel.eval, Lean.Nat.imax])) h

theorem HasType.truePf :
    env.HasType U Γ VExpr.truePf VExpr.trueTy := by
  have h0 : env.HasType U Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by simp [VLevel.WF])
  have h1 : env.HasType U (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : env.HasType U (.bvar 0 :: .sort .zero :: Γ) (.bvar 0) (.bvar 1) := .bvar .zero
  exact HasType.lam h0 (HasType.lam h1 h2)

/-- A Pi-type ending in an application of the constant family `fun ds => trueTy` is
inhabited. -/
theorem HasType.inhabit_trueFamily (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {B xs D : List VExpr}
    (hH : env.HasType U (B.reverse ++ Γ) (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hT : env.IsType U Γ (VExpr.wrapForalls B (VExpr.mkApps (VExpr.wrapLams D VExpr.trueTy) xs))) :
    env.HasType U Γ (VExpr.wrapLams B VExpr.truePf)
      (VExpr.wrapForalls B (VExpr.mkApps (VExpr.wrapLams D VExpr.trueTy) xs)) := by
  obtain ⟨hctx, u, hb⟩ := IsType.wrapForalls_inv henv hΓ hT
  have hlen := HasType.mkApps_sort_arity henv hctx hH hb
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hctx hH ⟨_, hb⟩ hlen
  have hβ := IsDefEq.mkApps_wrapLams henv hctx hH hlen hargs
  rw [instOuter_closed0 VExpr.trueTy_closed, instOuter_closed0 (by simp [VExpr.ClosedN])] at hβ
  exact HasType.wrapLams_of hctx (.defeqDF hβ.symm HasType.truePf)

end VEnv
namespace InductiveSignature.Instance
variable {s : InductiveSignature} (g : Instance s)

/-- The index telescope at the instance's universes. -/
def sIndices (owner : Fin s.families.size) : List VExpr :=
  s.families[owner].indices.map (·.instL g.levels)

/-- The family applied to its parameter and index variables. -/
def sMajor (owner : Fin s.families.size) : VExpr :=
  VExpr.mkApps (.const s.families[owner].name g.levels)
    (vars s.params.length s.families[owner].indices.length ++
      vars s.families[owner].indices.length 0)

/-- The field telescope at the instance's universes. -/
def sFields (c : Constructor s.families.size) : List VExpr :=
  (s.fieldTypes c).map (·.instL g.levels)

/-- The constructor's result indices at the instance's universes. -/
def sCtorIndices (c : Constructor s.families.size) : List VExpr :=
  c.indices.map (·.instL g.levels)

/-- The induction hypotheses of the first minor premise. -/
def sHyps (c : Constructor s.families.size) : List VExpr :=
  (recursiveFields c).zipIdx.map fun ((field, r), i) => g.hypothesis c 0 i field r

@[simp] theorem length_insertBinders (l : List VExpr) (n : Nat) :
    (insertBinders l n).length = l.length := by simp [insertBinders]

theorem insertBinders_zero (l : List VExpr) : insertBinders l 0 = l := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i h1 h2; simp [insertBinders, VExpr.liftN_zero]

theorem motive_shape (owner : Fin s.families.size) (htarget : g.targetLevel = .zero) :
    g.motive s.families[owner] 0 =
      VExpr.wrapForalls (g.sIndices owner ++ [g.sMajor owner]) (.sort .zero) := by
  simp only [motive, insertBinders_zero, htarget, sIndices, sMajor, List.length_map, Nat.zero_add]

theorem minor_shape (hfam : s.families.size = 1) (c : Constructor s.families.size)
    (hown : c.owner.val = 0) :
    g.minor c 0 =
      VExpr.wrapForalls (insertBinders (g.sFields c) 1 ++ g.sHyps c)
        (VExpr.mkApps (.bvar ((g.sFields c).length + (g.sHyps c).length))
          ((g.sCtorIndices c).map (fun e => (e.liftN (g.sHyps c).length).liftN 1
              ((g.sFields c).length + (g.sHyps c).length)) ++
            [g.constructorApp c 1 (g.sHyps c).length])) := by
  have hnf : (g.sFields c).length = c.fields.length := by simp [sFields, fieldTypes]
  simp only [minor, hfam, hown, Nat.add_zero, Nat.sub_self, sFields, sHyps, sCtorIndices,
    List.length_map, List.length_zipIdx, List.map_map, Function.comp_def]
  have : (s.fieldTypes c).length = c.fields.length := by simp [fieldTypes]
  rw [this]

theorem toList_of_size_one {α} (a : Array α) (h : a.size = 1) (i : Fin a.size) :
    a.toList = [a[i]] := by
  have hi : i.val = 0 := by have := i.isLt; omega
  match a, h with
  | ⟨[x]⟩, _ => simp [hi]

theorem recursorType_shape (hfam : s.families.size = 1) (hcs : s.constructors.size = 1)
    (owner : Fin s.families.size) (index : Fin s.constructors.size) :
    g.recursorType owner =
      VExpr.wrapForalls (g.params ++ [g.motive s.families[owner] 0] ++
          [g.minor s.constructors[index] 0] ++ insertBinders (g.sIndices owner) 2 ++
          [g.familyApp owner (vars s.params.length (2 + (g.sIndices owner).length))
            (vars (g.sIndices owner).length 0)])
        (VExpr.mkApps (.bvar ((g.sIndices owner).length + 2))
          (vars (g.sIndices owner).length 1 ++ [.bvar 0])) := by
  have ho : owner.val = 0 := by have := owner.isLt; omega
  have hi : index.val = 0 := by have := index.isLt; omega
  have hm : g.motives = [g.motive s.families[owner] 0] := by
    simp [motives, toList_of_size_one s.families hfam owner, ho]
  have hn : g.minors = [g.minor s.constructors[index] 0] := by
    simp [minors, toList_of_size_one s.constructors hcs index, hi]
  simp only [recursorType, hm, hn, hfam, hcs, ho, sIndices, List.length_map, Nat.sub_self,
    Nat.add_zero, length_insertBinders]

end InductiveSignature.Instance

namespace VEnv
open InductiveSignature
variable {env : VEnv} {U : Nat}

theorem OnCtx.closed_reverse (henv : env.Ordered) {doms : List VExpr}
    (h : OnCtx doms.reverse (env.IsType U)) :
    ∀ j (hj : j < doms.length), (doms[j]).ClosedN j := by
  intro j hj
  have hc : OnCtx (doms.reverse ++ []) (fun Γ A => A.ClosedN Γ.length) := by
    rw [List.append_nil]; exact CtxWF.closed henv h
  have := OnCtx.getElem_reverse_append hc j hj
  simpa [Nat.min_eq_left (Nat.le_of_lt hj)] using this.2

theorem getElem_insertBinders {l : List VExpr} {n i : Nat} (h : i < (insertBinders l n).length) :
    (insertBinders l n)[i] = (l[i]'(by simpa using h)).liftN n i := by
  simp [insertBinders]

/-- The minor premise's field context, with the motive instantiated: the field telescope is
well formed in its own context, and the context of the minor premise is instantiated at the
field variables. -/
theorem minorFields_inst (henv : env.WF) {P F : List VExpr} {Mot M0 : VExpr}
    (hP : OnCtx P.reverse (env.IsType U)) (hM0 : env.HasType U P.reverse M0 Mot)
    (hF : OnCtx ((insertBinders F 1).reverse ++ Mot :: P.reverse) (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i)) :
    ∀ i, i ≤ F.length → OnCtx (P ++ F.take i).reverse (env.IsType U) ∧
      TelInst env U (P ++ F.take i).reverse (P ++ [Mot] ++ (insertBinders F 1).take i)
        (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i) := by
  have hall : OnCtx (P ++ [Mot] ++ insertBinders F 1).reverse (env.IsType U) := by
    simpa using hF
  have hcl := OnCtx.closed_reverse henv.ordered hall
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simpa using hP, ?_⟩
    have hPcl : ∀ j (h : j < P.length), (P[j]).ClosedN j := fun j h => by
      have := hcl j (by simp; omega)
      rwa [List.getElem_append_left (by simp; omega), List.getElem_append_left h] at this
    have hI := TelInst.ident (env := env) (U := U) [] hPcl
    have hMotcl : Mot.ClosedN P.length := by
      have := hcl P.length (by simp)
      rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)] at this
      simpa using this
    have hM : env.HasType U P.reverse (M0.liftN 0) (Mot.instOuter (bvarRange P.length P.length)) := by
      rw [VExpr.instOuter_range_bvar' _ _ _ hMotcl (Nat.le_refl _), Nat.sub_self,
        VExpr.liftN_zero, VExpr.liftN_zero]
      exact hM0
    have := TelInst.append_one (by simpa using hI) hM
    simpa [bvarRange_zero] using this
  | succ i ih =>
    intro hi
    obtain ⟨hctx, ht⟩ := ih (Nat.le_of_succ_le hi)
    have hilt : i < F.length := hi
    have hFi := OnCtx.getElem_reverse_append (L := P ++ [Mot] ++ insertBinders F 1) (Γ := [])
      (by rw [List.append_nil]; exact hall) (P.length + 1 + i) (by simp; omega)
    have hdom : (P ++ [Mot] ++ insertBinders F 1)[P.length + 1 + i]'(by simp; omega) =
        (F[i]).liftN 1 i := by
      rw [List.getElem_append_right (by simp), getElem_insertBinders (by simp; omega)]
      simp
    have htake : (P ++ [Mot] ++ insertBinders F 1).take (P.length + 1 + i) =
        P ++ [Mot] ++ (insertBinders F 1).take i := by
      rw [List.take_append, List.take_of_length_le (by simp)]
      simp
    rw [hdom, htake, List.append_nil] at hFi
    obtain ⟨hΔ, u, hu⟩ := hFi
    have hinst := IsDefEq.closed_instOuter_congr henv hctx hΔ hu ht.1 ht.1
      (fun j hj _ hd => ht.2 j hj hd)
    have hFicl := hFcl i hilt
    have hdrop : ((F[i]).liftN 1 i).instOuter
        (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i) = F[i] := by
      have := VExpr.liftN_instOuter_drop (e := F[i]) (X := bvarRange P.length (P.length + i))
        (Y := [M0.liftN i]) (Z := bvarRange i i) (by simpa using hFicl)
      simp only [List.length_singleton, bvarRange_length] at this
      rw [this, ← CastSpec.bvarRange_split, VExpr.instOuter_range_bvar' _ _ _ hFicl (Nat.le_refl _),
        Nat.sub_self, VExpr.liftN_zero]
    rw [hdrop] at hinst
    simp only [VExpr.instOuter_sort] at hinst
    have hctx' : OnCtx (P ++ F.take (i + 1)).reverse (env.IsType U) := by
      rw [List.take_succ_eq_append_getElem hilt, ← List.append_assoc, List.reverse_append]
      exact ⟨hctx, _, hinst⟩
    refine ⟨hctx', ?_⟩
    have hDcl : ∀ j (h : j < (P ++ [Mot] ++ (insertBinders F 1).take i).length),
        ((P ++ [Mot] ++ (insertBinders F 1).take i)[j]).ClosedN j := by
      intro j h
      have := hcl j (by simp at h ⊢; omega)
      have key : ∀ (l1 l2 : List VExpr), l1 = l2 → ∀ (h1 : j < l1.length) (h2 : j < l2.length),
          l1[j] = l2[j] := by intro _ _ e; subst e; intros; rfl
      rw [key _ _ htake.symm h (by simp at h ⊢; omega), List.getElem_take]
      exact this
    have hw := TelInst.weak henv.ordered [F[i]] hDcl ht
    have hmap : (bvarRange P.length (P.length + i) ++ [M0.liftN i] ++ bvarRange i i).map
        (fun x : VExpr => x.liftN [F[i]].length) =
        bvarRange P.length (P.length + (i + 1)) ++ [M0.liftN (i + 1)] ++ bvarRange i (i + 1) := by
      simp only [List.length_singleton, List.map_append, List.map_cons, List.map_nil]
      rw [bvarRange_map_liftN _ _ _ (by omega), bvarRange_map_liftN _ _ _ (by omega),
        VExpr.liftN_liftN]
      simp only [Nat.add_assoc]
    rw [hmap] at hw
    have hb : env.HasType U (F[i] :: (P ++ F.take i).reverse) (.bvar 0)
        (((F[i]).liftN 1 i).instOuter
          (bvarRange P.length (P.length + (i + 1)) ++ [M0.liftN (i + 1)] ++
            bvarRange i (i + 1))) := by
      have := VExpr.liftN_instOuter_drop (e := F[i]) (X := bvarRange P.length (P.length + (i + 1)))
        (Y := [M0.liftN (i + 1)]) (Z := bvarRange i (i + 1)) (by simpa using hFicl)
      simp only [List.length_singleton, bvarRange_length] at this
      rw [this]
      have hsplit : bvarRange P.length (P.length + (i + 1)) ++ bvarRange i (i + 1) =
          bvarRange (P.length + i) (P.length + i + 1) := by
        rw [CastSpec.bvarRange_append _ _ _ (by omega)]
        congr 2 <;> omega
      rw [hsplit, VExpr.instOuter_range_bvar' _ _ _ hFicl (by omega)]
      simp only [show P.length + i + 1 - (P.length + i) = 1 by omega]
      exact .bvar .zero
    have := TelInst.append_one hw hb
    rw [List.take_succ_eq_append_getElem (l := insertBinders F 1) (by simpa using hilt),
      getElem_insertBinders]
    have hsnoc : bvarRange (i + 1) (i + 1) = bvarRange i (i + 1) ++ [.bvar 0] := by
      rw [CastSpec.bvarRange_append i 1 (i + 1) (by omega)]
      simp [bvarRange]
    have hctxeq : (P ++ F.take (i + 1)).reverse = F[i] :: (P ++ F.take i).reverse := by
      rw [List.take_succ_eq_append_getElem (l := F) hilt, ← List.append_assoc,
        List.reverse_append]; rfl
    rw [hctxeq, hsnoc]
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this

/-- The minor premise's full context, with the motive instantiated at the constant family
of `trueTy`: every induction hypothesis is then inhabited. -/
theorem minorHyps_inst (henv : env.WF) {P F Hs D : List VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hM0 : env.HasType U P.reverse (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hall : OnCtx (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i))
    (hshape : ∀ j (hj : j < Hs.length) (args : List VExpr),
      args.length = P.length + 1 + F.length + j →
      args[P.length]? = some ((VExpr.wrapLams D VExpr.trueTy).liftN F.length) →
      ∃ B xs, (Hs[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams D VExpr.trueTy).liftN (F.length + B.length)) xs)) :
    OnCtx (P ++ F).reverse (env.IsType U) ∧
    ∃ inh : List VExpr, inh.length = Hs.length ∧
      TelInst env U (P ++ F).reverse
        (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs)
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) := by
  have hF : OnCtx ((insertBinders F 1).reverse ++ VExpr.wrapForalls D (.sort .zero) :: P.reverse)
      (env.IsType U) := by
    have := OnCtx.of_append (Γ' := Hs.reverse) (by simpa [List.append_assoc] using hall)
    simpa using this
  obtain ⟨hctx, htel⟩ := minorFields_inst henv hP hM0 hF hFcl F.length (Nat.le_refl _)
  rw [List.take_of_length_le (Nat.le_refl _)] at hctx htel
  rw [List.take_of_length_le (by simp)] at htel
  refine ⟨hctx, ?_⟩
  suffices ∀ j, j ≤ Hs.length → ∃ inh : List VExpr, inh.length = j ∧
      TelInst env U (P ++ F).reverse
        (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs.take j)
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) by
    obtain ⟨inh, hl, h⟩ := this Hs.length (Nat.le_refl _)
    exact ⟨inh, hl, by rwa [List.take_of_length_le (Nat.le_refl _)] at h⟩
  intro j
  induction j with
  | zero => intro _; exact ⟨[], rfl, by simpa using htel⟩
  | succ j ih =>
    intro hj
    obtain ⟨inh, hl, ht⟩ := ih (Nat.le_of_succ_le hj)
    have hjlt : j < Hs.length := hj
    have hHj := OnCtx.getElem_reverse_append
      (L := P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs) (Γ := [])
      (by rw [List.append_nil]; exact hall) (P.length + 1 + F.length + j) (by simp; omega)
    have hdom : (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs)[
        P.length + 1 + F.length + j]'(by simp; omega) = Hs[j] := by
      rw [List.getElem_append_right (by simp; omega)]
      simp; congr 1; omega
    have htake : (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).take
        (P.length + 1 + F.length + j) =
        P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs.take j := by
      rw [List.take_append, List.take_of_length_le (by simp; omega)]
      simp; omega
    rw [hdom, htake, List.append_nil] at hHj
    obtain ⟨hΔ, u, hu⟩ := hHj
    have hinst := IsDefEq.closed_instOuter_congr henv hctx hΔ hu ht.1 ht.1
      (fun j hj _ hd => ht.2 j hj hd)
    simp only [VExpr.instOuter_sort] at hinst
    obtain ⟨B, xs, hBx⟩ := hshape j hjlt (bvarRange P.length (P.length + F.length) ++
        [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)
      (by simp [hl]; omega)
      (by rw [List.getElem?_append_left (by simp)]; simp)
    rw [hBx] at hinst
    have hW : Ctx.LiftN (F.length + B.length) 0 P.reverse (B.reverse ++ (P ++ F).reverse) := by
      have := Ctx.LiftN.zero (B.reverse ++ F.reverse) (Γ := P.reverse)
      simpa [Nat.add_comm] using this
    have hH := hM0.weakN henv.ordered hW
    have e := liftN_wrapLams D VExpr.trueTy (F.length + B.length)
    rw [VExpr.trueTy_closed.liftN_eq (Nat.zero_le _)] at e
    rw [e, liftN_wrapForalls] at hH
    simp only [VExpr.liftN] at hH
    rw [e] at hinst
    have ha := HasType.inhabit_trueFamily henv hctx hH ⟨_, hinst⟩
    rw [← e, ← hBx] at ha
    refine ⟨inh ++ [VExpr.wrapLams B VExpr.truePf], by simp [hl], ?_⟩
    rw [List.take_succ_eq_append_getElem hjlt, ← List.append_assoc, ← List.append_assoc]
    exact TelInst.append_one ht ha

theorem lifted_instOuter {e : VExpr} {X Y inh : List VExpr} {M : VExpr}
    (he : e.ClosedN (X.length + Y.length)) :
    ((e.liftN inh.length).liftN 1 (Y.length + inh.length)).instOuter (X ++ [M] ++ Y ++ inh) =
      e.instOuter (X ++ Y) := by
  have h1 := VExpr.liftN_instOuter_drop (e := e.liftN inh.length) (X := X) (Y := [M])
    (Z := Y ++ inh) (by
      have := he.liftN (n := inh.length) (j := 0)
      simpa [Nat.add_assoc] using this)
  simp only [List.length_singleton, List.length_append, List.append_assoc] at h1 ⊢
  rw [h1]
  have h2 := VExpr.liftN_instOuter_drop (e := e) (X := X ++ Y) (Y := inh) (Z := []) (by simpa using he)
  simpa using h2

/-- The minor premise's conclusion, with the motive instantiated and the induction
hypotheses inhabited: the constructor's result indices and the constructor application
instantiate the motive's telescope over the parameter and field variables. -/
theorem minorBody_inst (henv : env.WF) {P F Hs D CI : List VExpr} {ctorApp : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hM0 : env.HasType U P.reverse (VExpr.wrapLams D VExpr.trueTy)
      (VExpr.wrapForalls D (.sort .zero)))
    (hall : OnCtx (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (env.IsType U))
    (hFcl : ∀ i (h : i < F.length), (F[i]).ClosedN (P.length + i))
    (hshape : ∀ j (hj : j < Hs.length) (args : List VExpr),
      args.length = P.length + 1 + F.length + j →
      args[P.length]? = some ((VExpr.wrapLams D VExpr.trueTy).liftN F.length) →
      ∃ B xs, (Hs[j]).instOuter args =
        VExpr.wrapForalls B (VExpr.mkApps
          ((VExpr.wrapLams D VExpr.trueTy).liftN (F.length + B.length)) xs))
    (hbody : env.IsType U (P ++ [VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs).reverse
      (VExpr.mkApps (.bvar (F.length + Hs.length))
        (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
          [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)])))
    (hCIcl : ∀ e ∈ CI, e.ClosedN (P.length + F.length))
    (hccl : ctorApp.ClosedN (P.length + F.length)) :
    OnCtx (P ++ F).reverse (env.IsType U) ∧
    TelInst env U (P ++ F).reverse (P ++ D)
      (bvarRange P.length (P.length + F.length) ++ CI ++ [ctorApp]) := by
  obtain ⟨hctx, inh, hl, htel⟩ := minorHyps_inst henv hP hM0 hall hFcl hshape
  refine ⟨hctx, ?_⟩
  obtain ⟨u, hb⟩ := hbody
  have hinst := IsDefEq.closed_instOuter_congr henv hctx hall hb htel.1 htel.1
    (fun j hj _ hd => htel.2 j hj hd)
  simp only [VExpr.instOuter_sort, VExpr.instOuter_mkApps, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_def] at hinst
  have hlen : (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh).length =
      P.length + 1 + F.length + Hs.length := by simp [hl]; omega
  rw [VExpr.instOuter_bvar _ (by omega)] at hinst
  have hhead : (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)[
        (bvarRange P.length (P.length + F.length) ++
      [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh).length
        - 1 - (F.length + Hs.length)]'(by omega) = (VExpr.wrapLams D VExpr.trueTy).liftN F.length := by
    simp only [hlen]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
      List.getElem_append_right (by simp; omega)]
    simp
  rw [hhead] at hinst
  have hlift : ∀ e : VExpr, e.ClosedN (P.length + F.length) →
      ((e.liftN Hs.length).liftN 1 (F.length + Hs.length)).instOuter
        (bvarRange P.length (P.length + F.length) ++
          [(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh) = e := by
    intro e he
    have := lifted_instOuter (e := e) (X := bvarRange P.length (P.length + F.length))
      (Y := bvarRange F.length F.length) (inh := inh)
      (M := (VExpr.wrapLams D VExpr.trueTy).liftN F.length) (by simpa using he)
    simp only [bvarRange_length, hl] at this
    rw [this, ← CastSpec.bvarRange_split, VExpr.instOuter_range_bvar' _ _ _ he (Nat.le_refl _),
      Nat.sub_self, VExpr.liftN_zero]
  rw [hlift _ hccl, List.map_congr_left (fun e he => hlift e (hCIcl e he)), List.map_id'] at hinst
  -- the instantiated motive's type
  have hMotcl : ∀ j (h : j < (P ++ D).length), ((P ++ D)[j]).ClosedN j := by
    have h := (IsType.wrapForalls_inv henv hP (hM0.isType henv.ordered hP)).1
    exact OnCtx.closed_reverse henv.ordered (by simpa using h)
  have hW : Ctx.LiftN F.length 0 P.reverse (P ++ F).reverse := by
    simpa using Ctx.LiftN.zero (n := F.length) F.reverse (Γ := P.reverse) (by simp)
  have hM := hM0.weakN henv.ordered hW
  rw [liftN_wrapForalls] at hM
  simp only [VExpr.liftN] at hM
  have harity := HasType.mkApps_sort_arity henv hctx hM hinst
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hctx hM ⟨_, hinst⟩ harity
  rw [List.append_assoc]
  refine TelInst.append ?_ (by simpa using harity) ?_
  · have h' : TelInst env U (P ++ F).reverse
        (P ++ ([VExpr.wrapForalls D (.sort .zero)] ++ insertBinders F 1 ++ Hs))
        (bvarRange P.length (P.length + F.length) ++
          ([(VExpr.wrapLams D VExpr.trueTy).liftN F.length] ++ bvarRange F.length F.length ++ inh)) := by
      simpa only [List.append_assoc] using htel
    have := TelInst.take h'
    rwa [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)] at this
  · intro j hj
    have hlenD : (CI ++ [ctorApp]).length = D.length := by simpa using harity
    have hj' : j < (CI ++ [ctorApp]).length := by omega
    have hjm : j < (D.mapIdx fun l d => d.liftN F.length l).length := by simpa using hj
    have := hargs j hj' hjm
    rw [List.getElem_mapIdx] at this
    have hDcl : (D[j]).ClosedN (P.length + j) := by
      have := hMotcl (P.length + j) (by simp; omega)
      rw [List.getElem_append_right (by simp)] at this
      simpa only [Nat.add_sub_cancel_left] using this
    have htl : ((CI ++ [ctorApp]).take j).length = j := by
      rw [List.length_take]; omega
    have e := liftN_instOuter_params (P := P.length) (X := D[j])
      (args := (CI ++ [ctorApp]).take j) (by rw [htl]; exact hDcl) F.length
    rw [htl] at e
    rw [e] at this
    rw [getD_of_lt hj', getD_of_lt hj]
    exact this

theorem instDomains_append (A B : List VExpr) (a : VExpr) (k : Nat) :
    VExpr.instDomains (A ++ B) a k = VExpr.instDomains A a k ++ VExpr.instDomains B a (k + A.length) := by
  induction A generalizing k with
  | nil => simp [VExpr.instDomains]
  | cons d ds ih => simp [VExpr.instDomains, ih, Nat.add_assoc, Nat.add_comm 1]

theorem instDomains_insertBinders (F : List VExpr) (a : VExpr) :
    VExpr.instDomains (insertBinders F 1) a 0 = F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [VExpr.instDomains_getElem _ _ _ _ (by simpa using h2), getElem_insertBinders (by simpa using h2)]
    simpa using VExpr.inst_liftN (k := i) F[i] a

/-- The minor premise built from a branch over the fields: the induction hypotheses are
abstracted and unused. -/
theorem HasType.minorOf (henv : env.WF) {P F Hs CI : List VExpr} {Mot ctorApp M b : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hMin : env.IsType U (Mot :: P.reverse)
      (VExpr.wrapForalls (insertBinders F 1 ++ Hs)
        (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)]))))
    (hM : env.HasType U P.reverse M Mot)
    (hb : env.HasType U (P ++ F).reverse b (VExpr.mkApps (M.liftN F.length) (CI ++ [ctorApp]))) :
    env.HasType U P.reverse
      (VExpr.wrapLams (VExpr.instDomains (insertBinders F 1 ++ Hs) M 0) (b.liftN Hs.length))
      ((VExpr.wrapForalls (insertBinders F 1 ++ Hs)
        (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)]))).inst M 0) := by
  have h1 := IsType.instN henv.ordered .zero hMin hM
  rw [VExpr.wrapForalls_inst] at h1 ⊢
  obtain ⟨hctx, _⟩ := IsType.wrapForalls_inv henv hP h1
  apply HasType.wrapLams_of hctx
  have hbody : (VExpr.mkApps (.bvar (F.length + Hs.length))
          (CI.map (fun e => (e.liftN Hs.length).liftN 1 (F.length + Hs.length)) ++
            [(ctorApp.liftN Hs.length).liftN 1 (F.length + Hs.length)])).inst M
        (0 + (insertBinders F 1 ++ Hs).length) =
      (VExpr.mkApps (M.liftN F.length) (CI ++ [ctorApp])).liftN Hs.length := by
    simp only [VExpr.inst_mkApps, VExpr.liftN_mkApps, List.length_append, InductiveSignature.Instance.length_insertBinders,
      Nat.zero_add, List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      VExpr.inst_liftN]
    congr 1
    simp [VExpr.inst, VExpr.instVar, VExpr.liftN_liftN, Nat.add_comm]
  rw [hbody]
  rw [instDomains_append, instDomains_insertBinders] at hctx ⊢
  have hW : Ctx.LiftN Hs.length 0 (P ++ F).reverse
      ((VExpr.instDomains Hs M (0 + (insertBinders F 1).length)).reverse ++ (F.reverse ++ P.reverse)) := by
    have := Ctx.LiftN.zero (n := Hs.length) (VExpr.instDomains Hs M (0 + (insertBinders F 1).length)).reverse
      (Γ := (P ++ F).reverse) (by simp)
    simpa using this
  have := hb.weakN henv.ordered hW
  simpa [List.reverse_append, List.append_assoc] using this

theorem vars_eq_bvarRange (count below : Nat) :
    vars count below = bvarRange count (count + below) := by
  apply List.ext_getElem
  · simp [vars, bvarRange]
  · intro i hi hi'
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range]
    rw [bvarRange_getElem count (count + below) i (by simpa [vars] using hi)]
    simp only [List.length_range]
    have : i < count := by simpa [vars] using hi
    congr 1
    omega

theorem insertBinders_eq_mapIdx (l : List VExpr) (n : Nat) :
    insertBinders l n = l.mapIdx fun k d => d.liftN n k := by
  apply List.ext_getElem
  · simp [insertBinders]
  · intro i h1 h2; simp [insertBinders]

/-- Instantiating the parameters and the motive of a term over both at the parameter
variables, beneath `r` binders. -/
theorem instOuter_vars_snoc {X M : VExpr} {n : Nat} (hX : X.ClosedN (n + 1)) (r : Nat) :
    X.instOuter (bvarRange n (n + r) ++ [M.liftN r]) = (X.inst M 0).liftN r := by
  rw [VExpr.instOuter_eq_subst, VExpr.liftN_eq_subst (X.inst M 0), VExpr.inst_eq,
    VExpr.subst_subst]
  apply VExpr.subst_congr_closedN hX
  intro i hi
  cases i with
  | zero =>
    rw [VExpr.Subst.ofList_lt _ (by simp)]
    simp [VExpr.Subst.comp, VExpr.Subst.cons, VExpr.liftN_eq_subst]
  | succ j =>
    rw [VExpr.Subst.ofList_lt _ (by simp; omega)]
    rw [List.getElem_append_left (by simp; omega), bvarRange_getElem _ _ _ (by simp; omega)]
    simp only [VExpr.Subst.comp, VExpr.Subst.cons, VExpr.Subst.id, VExpr.subst_bvar,
      VExpr.Subst.shift]
    congr 1; simp; omega

/-- Inserting two arguments, at two inserted binders, into a telescope instance. -/
theorem TelInst.insert2 {A B a b : List VExpr} {X Y x y : VExpr}
    (H : TelInst env U Γ (A ++ B) (a ++ b)) (ha : a.length = A.length)
    (hBcl : ∀ k (h : k < B.length), (B[k]).ClosedN (A.length + k))
    (hx : env.HasType U Γ x (X.instOuter a)) (hy : env.HasType U Γ y (Y.instOuter (a ++ [x]))) :
    TelInst env U Γ (A ++ [X] ++ [Y] ++ B.mapIdx fun k d => d.liftN 2 k)
      (a ++ [x] ++ [y] ++ b) := by
  have hb : b.length = B.length := by have := H.1; simp at this; omega
  have hA : TelInst env U Γ A a := by
    have := H.take
    rwa [List.take_left' ha] at this
  refine TelInst.append (TelInst.append_one (TelInst.append_one hA hx) hy) (by simp [hb]) ?_
  intro k hk
  have hk' : k < B.length := by simpa using hk
  have hkb : k < b.length := by omega
  have := H.2 (A.length + k) (by simp; omega) (by simp; omega)
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by simp)] at this
  rw [List.take_append, List.take_of_length_le (by omega)] at this
  simp only [ha, Nat.add_sub_cancel_left] at this
  rw [getD_of_lt hkb, getD_of_lt hk, List.getElem_mapIdx]
  have htk : (b.take k).length = k := by simp; omega
  have e := VExpr.liftN_instOuter_drop (e := B[k]) (X := a) (Y := [x, y]) (Z := b.take k)
    (by rw [htk, ha]; exact hBcl k hk')
  simp only [List.length_cons, List.length_nil, htk] at e
  have e' : a ++ [x] ++ [y] ++ b.take k = a ++ [x, y] ++ b.take k := by simp
  rw [e', e]
  have hidx : A.length + k - a.length = k := by omega
  simpa [hidx] using this

/-- The recursor applied at the generic motive's providers, with a motive into `Prop` and a
minor premise. -/
theorem HasType.elimApp (henv : env.WF) {P I : List VExpr} {Maj Min h M m : VExpr}
    (hP : OnCtx P.reverse (env.IsType U))
    (hidx : OnCtx (P ++ I ++ [Maj]).reverse (env.IsType U))
    (hMin : env.IsType U (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero) :: P.reverse) Min)
    (hhead : env.HasType U [] h
      (VExpr.wrapForalls (P ++ [VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)] ++ [Min] ++
          insertBinders I 2 ++ [Maj.liftN 2 I.length])
        (VExpr.mkApps (.bvar (I.length + 2)) (vars I.length 1 ++ [.bvar 0]))))
    (hM : env.HasType U P.reverse M (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)))
    (hm : env.HasType U P.reverse m (Min.inst M 0)) :
    env.HasType U (Maj :: (P ++ I).reverse)
      (VExpr.mkApps h (bvarRange P.length (P.length + I.length + 1) ++
        [M.liftN (I.length + 1), m.liftN (I.length + 1)] ++
        bvarRange (I.length + 1) (I.length + 1)))
      (VExpr.mkApps (M.liftN (I.length + 1)) (bvarRange (I.length + 1) (I.length + 1))) := by
  have hΓe : OnCtx (Maj :: (P ++ I).reverse) (env.IsType U) := by simpa using hidx
  have hcl := OnCtx.closed_reverse henv.ordered hidx
  have hId := TelInst.ident (env := env) (U := U) [] hcl
  have hN : (P ++ I ++ [Maj]).length = P.length + (I.length + 1) := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hN, CastSpec.bvarRange_append P.length (I.length + 1) _ (by omega),
    show P.length + (I.length + 1) - P.length = I.length + 1 by omega,
    ← Nat.add_assoc] at hId
  simp only [List.append_nil] at hId
  have hId' : TelInst env U (Maj :: (P ++ I).reverse) (P ++ (I ++ [Maj]))
      (bvarRange P.length (P.length + I.length + 1) ++ bvarRange (I.length + 1) (I.length + 1)) := by
    simpa [List.append_assoc] using hId
  have hctxP := CtxWF.closed henv.ordered hP
  have hMotcl : (VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).ClosedN P.length := by
    obtain ⟨_, hu⟩ := hM.isType henv.ordered hP
    simpa using hu.closedN henv.ordered hctxP
  have hW : Ctx.LiftN (I.length + 1) 0 P.reverse (Maj :: (P ++ I).reverse) := by
    have := Ctx.LiftN.zero (n := I.length + 1) (Maj :: I.reverse) (Γ := P.reverse) (by simp)
    simpa using this
  have hx : env.HasType U (Maj :: (P ++ I).reverse) (M.liftN (I.length + 1))
      ((VExpr.wrapForalls (I ++ [Maj]) (.sort .zero)).instOuter
        (bvarRange P.length (P.length + I.length + 1))) := by
    rw [VExpr.instOuter_range_bvar' _ _ _ hMotcl (by omega),
      show P.length + I.length + 1 - P.length = I.length + 1 by omega]
    exact hM.weakN henv.ordered hW
  have hMincl : Min.ClosedN (P.length + 1) := by
    obtain ⟨_, hu⟩ := hMin
    have := hu.closedN henv.ordered (CtxWF.closed henv.ordered
      ⟨hP, hM.isType henv.ordered hP⟩)
    simpa using this
  have hy : env.HasType U (Maj :: (P ++ I).reverse) (m.liftN (I.length + 1))
      (Min.instOuter (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)])) := by
    rw [show P.length + I.length + 1 = P.length + (I.length + 1) by omega,
      instOuter_vars_snoc hMincl]
    exact hm.weakN henv.ordered hW
  have hBcl : ∀ k (hk : k < (I ++ [Maj]).length), ((I ++ [Maj])[k]).ClosedN (P.length + k) := by
    intro k hk
    have := hcl (P.length + k) (by simp at hk ⊢; omega)
    simp only [List.append_assoc] at this
    rw [List.getElem_append_right (by simp)] at this
    simpa using this
  have htel := TelInst.insert2 hId' (by simp) hBcl hx hy
  have hins : insertBinders (I ++ [Maj]) 2 = insertBinders I 2 ++ [Maj.liftN 2 I.length] := by
    simp [insertBinders, List.zipIdx_append]
  rw [← insertBinders_eq_mapIdx, hins] at htel
  rw [← List.append_assoc] at htel
  have happ := HasType.mkApps_of_tel henv hΓe (hhead.weak0 henv.ordered) htel
  have hargs : (bvarRange P.length (P.length + I.length + 1) ++
      [M.liftN (I.length + 1), m.liftN (I.length + 1)] ++
      bvarRange (I.length + 1) (I.length + 1)) =
      bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
        [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1) := by simp
  rw [hargs]
  refine (congrArg _ ?_).mp happ
  simp only [VExpr.instOuter_mkApps]
  have hlen : (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1)).length =
      P.length + I.length + 3 := by simp; omega
  rw [VExpr.instOuter_bvar _ (by omega)]
  have hhd : (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1))[
        (bvarRange P.length (P.length + I.length + 1) ++ [M.liftN (I.length + 1)] ++
      [m.liftN (I.length + 1)] ++ bvarRange (I.length + 1) (I.length + 1)).length - 1 -
        (I.length + 2)]'(by omega) = M.liftN (I.length + 1) := by
    simp only [hlen]
    simp only [show P.length + I.length + 3 - 1 - (I.length + 2) = P.length by omega]
    rw [List.getElem_append_left (by simp), List.getElem_append_left (by simp),
      List.getElem_append_right (by simp)]
    simp
  have hv : vars I.length 1 ++ [VExpr.bvar 0] = bvarRange (I.length + 1) (I.length + 1) := by
    rw [vars_eq_bvarRange, CastSpec.bvarRange_append I.length 1 _ (by omega)]
    simp [bvarRange]
  rw [hhd, hv, instOuter_bvarRange _ _ _ (Nat.le_refl _) (by omega), hlen,
    show P.length + I.length + 3 - (I.length + 1) = P.length + 2 by omega,
    List.drop_left' (by simp), List.take_of_length_le (by simp)]

theorem vars_map_liftN_hi (count below n k : Nat) (h : k ≤ below) :
    (vars count below).map (fun e => e.liftN n k) = vars count (below + n) := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  simp only [VExpr.liftN, liftVar]
  rw [if_neg (by omega)]
  congr 1; omega

theorem vars_map_liftN_lo (count below n k : Nat) (h : below + count ≤ k) :
    (vars count below).map (fun e => e.liftN n k) = vars count below := by
  simp only [vars, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_reverse, List.mem_range] at hi
  simp only [VExpr.liftN, liftVar]
  rw [if_pos (by omega)]

/-- The family applied to its parameters and indices, at arguments. -/
theorem instOuter_bvarRange_apps {f : VExpr} (hf : f.ClosedN 0) (args : List VExpr) :
    (VExpr.mkApps f (bvarRange args.length args.length)).instOuter args = VExpr.mkApps f args := by
  rw [VExpr.instOuter_mkApps, instOuter_closed0 hf,
    instOuter_bvarRange _ _ _ (Nat.le_refl _) (Nat.le_refl _)]
  simp

theorem sort_agree (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) {A B : VExpr} {a b : VLevel}
    (hA : env.HasType U Γ A (.sort a)) (hB : env.HasType U Γ B (.sort b))
    (hAB : env.IsDefEqU U Γ A B) : a ≈ b := by
  obtain ⟨T, hT⟩ := hAB
  have h1 := IsDefEq.uniqU henv hΓ hA hT
  have h2 := IsDefEq.uniqU henv hΓ hT hB
  exact IsDefEqU.sort_inv henv hΓ (h1.trans henv hΓ h2)

end VEnv

end Lean4Lean
