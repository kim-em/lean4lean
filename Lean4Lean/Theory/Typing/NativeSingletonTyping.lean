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

end VEnv

end Lean4Lean
