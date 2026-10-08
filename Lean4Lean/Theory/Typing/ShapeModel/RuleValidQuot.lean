import Lean4Lean.Theory.Typing.ShapeModel.RuleValidSig

/-!
# Validity of the quotient rule
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

/-- The binder domains of the quotient rule at universe levels `u, v`. -/
def quotDs (u v : VLevel) : List VExpr :=
  [.sort u, .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .sort v,
    .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [v]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .bvar 4]

theorem quot_lhs_instL (u v : VLevel) : quotDefEq.lhs.instL [u, v] = VExpr.wrapLams (quotDs u v)
    (VExpr.mkApps ((Head.const ``Quot.lift).toExpr [u, v])
      (vars 5 1 ++ ([] : List VExpr) ++
        [VExpr.mkApps (.const ``Quot.mk [u]) ([.bvar 5, .bvar 4] ++ vars 1 0)])) := rfl

theorem quot_rhs_instL (u v : VLevel) : quotDefEq.rhs.instL [u, v] =
    VExpr.wrapLams (quotDs u v) ((VExpr.app (.bvar 2) (.bvar 0)).instL [u, v]) := rfl

theorem quot_fieldIndex (lo : Nat) :
    fieldIndexOf (vars 5 1 ++ ([] : List VExpr)) 5 1 lo = [none] := by
  simp only [fieldIndexOf, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  have h1 : List.findIdx? (fun a => decide (a = VExpr.bvar (1 - 1 - 0))) (vars 5 1 ++ []) = none := by
    decide
  rw [h1]; simp [vars]

/-- The quotient rule is valid in the shape model of a well-formed environment. -/
theorem quot_extraValid (H : env.WF) (hqt : (envTables env).quot = true) :
    letI := envSig env; ExtraValid env quotDefEq := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  have hcl : ConstClosed env := fun h => H.ordered.closedC h
  obtain ⟨hQI, hfam, hctor, hdefs, hnat, -⟩ := (envTables_inv H).quot hqt
  intro ls w hls _ hL hR
  obtain ⟨u, v, rfl⟩ : ∃ u v, ls = [u, v] := by
    match ls, hls with
    | [u, v], _ => exact ⟨u, v, rfl⟩
  -- the rule
  have hl : quotDefEq.lhs = VExpr.wrapLams (quotDs (.param 0) (.param 1))
      (VExpr.mkApps (.const ``Quot.lift (VLevel.params 2))
        (vars 5 1 ++ ([] : List VExpr) ++
          [VExpr.mkApps (.const ``Quot.mk [.param 0]) ([.bvar 5, .bvar 4] ++ vars 1 0)])) := rfl
  have hr : quotDefEq.rhs = VExpr.wrapLams (quotDs (.param 0) (.param 1))
      (.app (.bvar 2) (.bvar 0)) := rfl
  obtain ⟨r, hrdef⟩ : ∃ r, r = majorRule (structNp env) (.const ``Quot.lift) 2 quotDefEq 1 :=
    ⟨_, rfl⟩
  have heq := majorRule_eq (np := structNp env) (h := .const ``Quot.lift) (u := 2) rfl
    (by intros; simp) hl hr
  have hrule : EnvRule env r := .inr (.inl ⟨hQI.equation, hqt, hrdef⟩)
  rw [← hrdef] at heq
  have hnbr : r.nbind = 5 + 1 := by rw [heq]; rfl
  have hrv : r.vars = (vars 5 1 ++ ([] : List VExpr)).map argVar := by rw [heq]
  have hmaj : r.major = some ⟨``Quot.mk, [.param 0], (List.range 1).reverse⟩ := by rw [heq]
  have hrhs : r.rhs = .app (.bvar 2) (.bvar 0) := by rw [heq]
  have hfi : r.fieldIndex = [none] := by rw [heq]; exact quot_fieldIndex _
  -- the major constructor
  have hctorOf : ctorOf env ``Quot.mk = some quotCtor := hctor
  have hci : sigCtor env ``Quot.mk =
      some ⟨``Quot, structNp env ``Quot.mk, 3 - structNp env ``Quot.mk⟩ := by
    rw [sigCtor_of_shape (c := ``Quot.mk) (.inl (by rw [hctorOf]; simp))
      (ctorOf_shape' H hctorOf)]; rfl
  have hnp : structNp env ``Quot.mk ≤ 2 := by
    rcases structNp_eq H ``Quot.mk with h | ⟨s, info, hp, hcn, h⟩
    · omega
    · have := ctorOf_projection H hp
      rw [hcn, hctorOf] at this
      simp only [quotCtor, Option.some.injEq, CtorData.mk.injEq] at this
      omega
  have hfamd : famOf env ``Quot = some quotFam := hfam
  have hstr : ∀ {s info}, env.projections s info → info.ctorName = ``Quot.mk →
      FamTypeSem env s info := by
    intro s info hp hcn
    have h1 := ctorOf_projection H hp
    rw [hcn, hctorOf] at h1
    simp only [quotCtor, Option.some.injEq, CtorData.mk.injEq] at h1
    obtain ⟨rfl, -, -, -⟩ := h1
    have h2 := famOf_projection H hp
    rw [hfamd] at h2
    simp only [quotFam, Option.some.injEq, FamData.mk.injEq] at h2
    obtain ⟨-, hnp2, hni, hrl, -⟩ := h2
    refine famTypeSem_of_famSem H hp ?_
    rw [← hnp2, ← hni, ← hrl]
    exact quot_famSem hQI
  refine (quot_lhs_instL u v).symm ▸ (quot_rhs_instL u v).symm ▸ ?_
  rw [quot_lhs_instL] at hL
  rw [quot_rhs_instL] at hR
  refine majorRule_sound (Γ := []) hcl hrule (h := .const ``Quot.lift) (by rw [heq])
    (by rw [heq]; rfl) hnbr hrv hmaj hrhs (by rw [hfi]; rfl) hci rfl
    (by simp [VExpr.instL, VExpr.ClosedN]) hL hR ?_
  intro σ B₁ B₂ K W h₁ h₂ hB hTb
  right
  refine ⟨?_, fun hfp => ?_, fun hfp => ⟨?_, ?_⟩⟩
  · intro i hi j hj
    rw [hfi] at hj
    obtain rfl : i = 0 := by omega
    simp at hj
  · -- mode AB: realize the major
    rw [VExpr.mkApps_append_singleton] at h₁
    obtain ⟨_, hcore, -⟩ := h₁
    obtain ⟨A, Bf, -, hM, -⟩ := hcore.app_inv
    have hxs : List.Forall₂ (fun x A => Interp env σ x A) [TShape.bot, TShape.bot, σ 0]
        ([.bvar 5, .bvar 4] ++ vars 1 0) :=
      .cons .bot (.cons .bot (.cons .bvar' .nil))
    obtain ⟨n, fs, hfl, hI, hfx⟩ := realize_sig H W hci hfamd (quot_famSem hQI) hstr hM
      (by simp [vars]; omega) hxs hfp
    have hnfq : SemSig.nfields ``Quot.mk = 3 - structNp env ``Quot.mk := by
      show (match sigCtor env ``Quot.mk with | some ci => ci.nfields | none => 0) = _
      rw [hci]
    refine ⟨n, fs, by rw [hfl, hnfq], hI, fun i hi => ?_⟩
    obtain rfl : i = 0 := by omega
    simp only at hfl
    have hfl1 : 1 ≤ fs.length := by rw [hfl]; omega
    refine ⟨fun _ => ?_, fun h => by omega⟩
    have hk : fs.length - 1 < fs.length := by omega
    have := forall₂_getElem hfx (i := fs.length - 1) (by rw [hfx.length_eq]; exact hk)
    simp only [List.getElem_drop] at this
    rw [show 0 + fs.length - 1 = fs.length - 1 by omega, List.getD_of_lt' hk]
    have h2 : structNp env ``Quot.mk + (fs.length - 1) = 2 := by omega
    simp only [h2] at this
    exact this
  · intro r' hr'
    rcases hr' with ⟨v', -, hd, rfl⟩ | ⟨-, -, rfl⟩ | ⟨df, -, data, hd, -, -, -, rfl⟩ |
      ⟨k, sc, -, o, -, -, -, -, rfl⟩ <;> intro hh'
    · simp only [defRule_head, Head.const.injEq] at hh'
      rw [hh', hdefs] at hd; cases hd
    · show Option.map _ (majorRule (structNp env) (.const ``Quot.lift) 2 quotDefEq 1).major = _
      rw [← hrdef, hmaj]; rfl
    · simp only [majorRule_head, Head.const.injEq] at hh'
      rw [hh', hnat] at hd; cases hd
    · simp at hh'
  · intro i hi _
    obtain rfl : i = 0 := by omega
    have hz : SLvl.IsZero u.eval := by
      have hfl : SemSig.famLevel ``Quot = some (.param 0) := by
        show sigFamLevel env ``Quot = _; simp [sigFamLevel, hfamd, quotFam]
      have := hfp
      simp only [SemSig.famProp, hfl, decide_eq_true_eq] at this
      intro ns; have := this ns
      simpa [RuleMajor.lvls, VLevel.eval, VLevel.inst] using this
    obtain ⟨a₀, h0, i0⟩ := K.lookup' 0 (by simp [quotDs])
    obtain ⟨a₅, h5, i5⟩ := K.lookup' 5 (by simp [quotDs])
    simp only [quotDs, List.length_cons, List.length_nil] at h0 i0 h5 i5
    have hle0 : a₀ ≤ TShape.sort u.eval := i0.le_sort
    have i5' : Interp env (fun j => σ (j + 1)) a₅ (.bvar 4) := by simpa using i5
    have hle5 : a₅ ≤ σ 5 := Interp.bvar_iff (ρ := fun j => σ (j + 1)) |>.1 i5'
    have hs5 : (σ 5).HasType (TShape.sort u.eval) := TShape.HasType.mono_r hle0 .sort h0
    have hs0 : (σ 0).HasType (σ 5) := TShape.HasType.mono_r hle5 hs5 h5
    exact TShape.HasType.proofIrrel hz hs5 hs0

end

end Lean4Lean.ShapeModel
