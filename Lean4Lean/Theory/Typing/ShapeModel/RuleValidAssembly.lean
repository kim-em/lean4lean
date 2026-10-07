import Lean4Lean.Theory.Typing.ShapeModel.RuleValidLeftover

/-!
# Validity of a rule with a constructor major in the signature of a well-formed environment

`rule_instance_valid`: the instance-level validity of a rule of `envSig env` whose left body is
`h (vars npre nf ++ idx) (c lv (ps ++ vars nf 0))`, from

* the syntax of the rule and of the head's type (a telescope whose major domain is a rigid family
  applied to parameter expressions and the index variables);
* the semantic header of the major constructor's family, and the structure facts of the
  constructor if it is a structure constructor;
* in mode C (the major's family is a proposition at the levels): either the rule's motive
  eliminates into the zero sort (both bodies are then bottom, `body_bot_of_motive`), or every rule
  of the head has this major constructor and every field not read from an index has a bottom
  key.

The alignment of the major (`ctor_not_over`, `ctor_not_under`), the realization of the major as a
constructor shape (`realize_sig`), and the reads of leftover parameter fields (`leftover_reads`)
are discharged here.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

/-- The syntactic telescope of a constructor of the signature. -/
theorem sigCtor_shape (H : env.WF) (hci : sigCtor env c = some ci) :
    ∃ cv doms args, env.constants c = some cv ∧
      cv.type = VExpr.wrapForalls doms (VExpr.mkApps (.const ci.family (VLevel.params cv.uvars)) args) ∧
      doms.length = ci.nparams + ci.nfields := by
  obtain ⟨hic, cv, hcv, hF, hnp, hnf⟩ := sigCtor_spec hci
  obtain ⟨k, cv', doms, idx, hcv', huv, ht, hdl⟩ := hic.shape H
  cases hcv.symm.trans hcv'
  rw [ht, familyOfType_shape, Option.some.injEq] at hF
  have har : cv.type.forallArity = doms.length := by rw [ht, forallArity_shape]
  have hle : structNp env c ≤ doms.length := by
    rcases structNp_eq H c with h0 | ⟨s, info, hp, hcn, hnpi⟩
    · omega
    · subst hcn
      obtain ⟨Ds, idx', hDs, -, hct⟩ := sig_ctorType H hp
      have hcv2 := sig_ctorConst H hp
      have hcvt : cv = ⟨info.uvars, info.ctorType⟩ := Option.some.inj (hcv.symm.trans hcv2)
      have : cv.type.forallArity = Ds.length := by
        rw [hcvt]
        change info.ctorType.forallArity = _
        rw [hct]; exact forallArity_shape _ _ _ _
      omega
  refine ⟨cv, doms, vars k.nparams k.nfields ++ idx, hcv, ?_, ?_⟩
  · rw [ht, huv, hF]
  · rw [hnp, hnf, har]; omega

/-- The arguments of the major of a rule have exactly the constructor's telescope length. -/
theorem major_aligned (H : env.WF) (W : letI := envSig env; Valuation.Fits env Γ₀ Γ σ) {h : Head}
    {pre margs doms₀ pargs : List VExpr} {TbH : VExpr}
    (hTy : letI := envSig env; StrongSound env Γ (VExpr.mkApps (h.toExpr ls)
      (pre ++ [VExpr.mkApps (.const c lv) margs])) B)
    (hTh : letI := envSig env; HeadType env h ls Th)
    (hThs : Th = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const F lvF) pargs]) TbH)
    (hlen0 : doms₀.length = pre.length) (hnrF : ∀ r, EnvRule env r → r.head ≠ .const F)
    (hci : sigCtor env c = some ci) : margs.length = ci.nparams + ci.nfields := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  obtain ⟨cv, doms, args, hcv, hct, hdl⟩ := sigCtor_shape H hci
  have hnr : ∀ r, SemSig.rules r → r.head ≠ .const ci.family := fun r hr =>
    (envSig_ctorType H hci hcv).1 r hr
  obtain ⟨A, Bf, hf, hM⟩ := StrongSound.app_last hTy
  rcases Nat.lt_trichotomy margs.length doms.length with hlt | heq | hgt
  · exact (ctor_not_under W hTh (rest := []) (by simpa using hThs) hlen0 hnrF hTy hcv
      hct hlt).elim
  · omega
  · exact (ctor_not_over W hcv hct hnr hM hgt).elim

theorem fieldIndexOf_isSome {pre : List VExpr} (hi : i < nf) (hlo : i < lo)
    (hp : npre + i < pre.length) : ∃ j, (fieldIndexOf pre npre nf lo)[i]? = some (some j) := by
  simp only [fieldIndexOf, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨npre + i, by rw [if_pos ⟨hlo, hp⟩]⟩

/-- Instance-level validity of a rule of the signature with a constructor major. -/
theorem rule_instance_valid (H : env.WF) {r : Rule} (hr : EnvRule env r) {h : Head}
    (hh : r.head = h) {ls : List VLevel} (huv : ls.length = r.uvars)
    {npre nf : Nat} {idx ps : List VExpr} {c : Name} {lv : List VLevel} {R : VExpr}
    (hnb : r.nbind = npre + nf) (hrv : r.vars = (vars npre nf ++ idx).map argVar)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) (hrhs : r.rhs = R)
    (hfi : r.fieldIndex = fieldIndexOf (vars npre nf ++ idx) npre nf (structNp env c - ps.length))
    {Ds : List VExpr} (hDs : Ds.length = npre + nf) (hRcl : (R.instL ls).ClosedN (npre + nf))
    {Γ : List VExpr} {T : VExpr}
    (hL : letI := envSig env; StrongSound env Γ (VExpr.wrapLams Ds (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx.map (·.instL ls) ++
        [VExpr.mkApps (.const c (lv.map (·.inst ls))) (ps.map (·.instL ls) ++ vars nf 0)]))) T)
    (hR : letI := envSig env; StrongSound env Γ (VExpr.wrapLams Ds (R.instL ls)) T)
    {Th TbH : VExpr} {doms₀ pargs : List VExpr} {F : Name} {lvF : List VLevel}
    (hTh : letI := envSig env; HeadType env h ls Th)
    (hThs : Th = VExpr.wrapForalls
      (doms₀ ++ [VExpr.mkApps (.const F lvF) (pargs ++ vars idx.length 0)]) TbH)
    (hlen0 : doms₀.length = npre + idx.length) (hpl : ps.length = pargs.length)
    (hncF : sigCtor env F = none) (hnrF : ∀ r, EnvRule env r → r.head ≠ .const F)
    {ci : CtorInfo} {d : FamData} {n : Nat} (hci : sigCtor env c = some ci)
    (hfamd : famOf env ci.family = some d)
    (hsem : letI := envSig env; FamSem env ci.family d.resultLevel n)
    (hstr : ∀ {s info}, env.projections s info → info.ctorName = c → FamTypeSem env s info)
    {Tb : VExpr} {Es : List VExpr} {tgt : VLevel} {iM : Nat}
    (hT : letI := envSig env;
      ∀ m, Interp env .nil m T ↔ Interp env .nil m (VExpr.wrapForalls Ds Tb))
    (hTb : Tb = VExpr.mkApps (.bvar (Ds.length - 1 - iM)) (idx.map (·.instL ls) ++
      [VExpr.mkApps (.const c (lv.map (·.inst ls))) (ps.map (·.instL ls) ++ vars nf 0)]))
    (hiM : iM < Ds.length) (hmot : Ds[iM] = VExpr.wrapForalls Es (.sort tgt))
    (hEs : Es.length = idx.length + 1)
    (hC : letI := envSig env;
      SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) = true →
      SLvl.IsZero tgt.eval ∨
      ((∀ r', EnvRule env r' → r'.head = h → r'.major.map (·.ctor) = some c) ∧
        ∀ σ, KeysFit env .nil Ds σ → Valuation.Fits env Γ (Ds.reverse ++ Γ) σ →
          ∀ i < nf, r.fieldIndex[i]? = some none → σ (nf - 1 - i) ≤ .bot)) :
    letI := envSig env
    SoundEq env [] (VExpr.wrapLams Ds (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx.map (·.instL ls) ++
        [VExpr.mkApps (.const c (lv.map (·.inst ls))) (ps.map (·.instL ls) ++ vars nf 0)])))
      (VExpr.wrapLams Ds (R.instL ls)) := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  have hcl : ConstClosed env := fun h => H.ordered.closedC h
  have hfil : r.fieldIndex.length = nf := by rw [hfi]; exact fieldIndexOf_length
  have hnrF' : ∀ r, SemSig.rules r → r.head ≠ .const F := hnrF
  have hncF' : SemSig.ctor F = none := hncF
  refine majorRule_sound hcl hr hh huv hnb hrv hmaj hrhs hfil hci (by simp) hRcl hL hR ?_
  intro σ B₁ B₂ K W h₁ h₂ hB hTbB
  -- the type of the left body is the motive applied
  have hB₁ := hTbB Tb hT
  -- field reads
  have hreads : FieldReads env σ r (vars npre nf ++ idx.map (·.instL ls)) nf := by
    intro i hi j hj
    rw [hfi] at hj
    rcases fieldIndexOf_some hi hj with ⟨hjl, hjv, -⟩ | ⟨-, hlo, rfl, hjl⟩
    · refine ⟨by simpa using hjl, fun t => ?_⟩
      have : (vars npre nf ++ idx.map (·.instL ls)).getD j (.sort .zero) = .bvar (nf - 1 - i) := by
        rw [List.getD_of_lt' (by simpa using hjl)]
        by_cases hjn : j < (vars npre nf).length
        · rw [List.getElem_append_left hjn]
          rw [List.getElem_append_left hjn] at hjv; exact hjv
        · rw [List.getElem_append_right (by omega)]
          rw [List.getElem_append_right (by omega)] at hjv
          simp only [List.getElem_map, hjv]; rfl
      rw [this]; exact Interp.bvar_iff
    · obtain ⟨s, info, hp, hcn, hnp, -⟩ := leftover_struct H (c := c) (p := ps.length) (by omega)
      have hF := envSig_structFacts_of_wf H hp (hstr hp hcn)
      have hal := major_aligned H W h₁ hTh (pre := vars npre nf ++ idx.map (·.instL ls)) hThs
        (by simp [hlen0, vars_length']) hnrF hci
      rw [← hcn, sig_ctor_proj H hp, Option.some.injEq] at hci
      subst hci
      have hThs' : Th = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const F lvF)
          (pargs ++ vars (idx.map (·.instL ls)).length 0)]) TbH := by simpa using hThs
      obtain ⟨hidx, hiff⟩ := leftover_reads (pre₀ := vars npre nf) hcl W h₁ hTh hThs'
        (by simp [hlen0, vars_length']) hncF' hnrF' hF hcn (by simp [hpl])
        (by simpa [vars_length'] using hal) (by simp; omega) hi
      have hidx' : i < idx.length := by simpa using hidx
      refine ⟨by simp [vars_length']; omega, fun t => ?_⟩
      rw [List.getD_of_lt' (by simp [vars_length']; omega),
        List.getElem_append_right (by simp [vars_length'])]
      simp only [vars_length', Nat.add_sub_cancel_left]
      exact hiff t
  -- the leftover fields have index positions
  have hleft : ∀ i < nf, i < structNp env c - ps.length → i < idx.length := by
    intro i hi hlo
    obtain ⟨s, info, hp, hcn, hnp, -⟩ := leftover_struct H (c := c) (p := ps.length) (by omega)
    have hF := envSig_structFacts_of_wf H hp (hstr hp hcn)
    have hal := major_aligned H W h₁ hTh (pre := vars npre nf ++ idx.map (·.instL ls)) hThs
      (by simp [hlen0, vars_length']) hnrF hci
    have hci' := hci
    rw [← hcn, sig_ctor_proj H hp, Option.some.injEq] at hci'
    subst hci'
    have hThs' : Th = VExpr.wrapForalls (doms₀ ++ [VExpr.mkApps (.const F lvF)
        (pargs ++ vars (idx.map (·.instL ls)).length 0)]) TbH := by simpa using hThs
    obtain ⟨hidx, -⟩ := leftover_reads (pre₀ := vars npre nf) hcl W h₁ hTh hThs'
      (by simp [hlen0, vars_length']) hncF' hnrF' hF hcn (by simp [hpl])
      (by simpa [vars_length'] using hal) (by simp; omega) hi
    simpa using hidx
  cases hfp : SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) with
  | true =>
    rcases hC hfp with hz | ⟨hD7, hunread⟩
    · left
      obtain ⟨a, hka, hia⟩ := K.lookup' iM hiM
      rw [hmot] at hia
      have hlenE : (idx.map (·.instL ls) ++ [VExpr.mkApps (.const c (lv.map (·.inst ls)))
          (ps.map (·.instL ls) ++ vars nf 0)]).length = Es.length := by simp [hEs]
      refine ⟨body_bot_of_motive W h₁ (fun m hm => by rw [← hTb]; exact (hB₁ m).1 hm) hka hia hz
        hlenE, body_bot_of_motive W h₂ (fun m hm => by rw [← hTb]; exact (hB₁ m).1 ((hB m).2 hm))
        hka hia hz hlenE⟩
    · exact .inr ⟨hreads, fun h => by simp at h, fun _ => ⟨hD7, fun i hi hn => hunread σ K W i hi hn⟩⟩
  | false =>
    refine .inr ⟨hreads, fun _ => ?_, fun h => by simp at h⟩
    obtain ⟨A, Bf, hf, hM⟩ := StrongSound.app_last h₁
    have hal := major_aligned H W h₁ hTh (pre := vars npre nf ++ idx.map (·.instL ls)) hThs
      (by simp [hlen0, vars_length']) hnrF hci
    obtain ⟨-, -, -, -, hnp, -⟩ := sigCtor_spec hci
    let xs : List TShape := (ps.map (·.instL ls)).map (fun _ => TShape.bot) ++
      (List.range nf).reverse.map (fun j => σ j)
    have hxs : List.Forall₂ (fun x A => Interp env σ x A) xs (ps.map (·.instL ls) ++ vars nf 0) := by
      refine (List.Forall₂.append_of_left (by simp)).2 ⟨?_, ?_⟩
      · refine List.forall₂_of_getElem (by simp) fun j _ _ => ?_
        simp only [List.getElem_map]; exact .bot
      · refine List.forall₂_of_getElem (by simp [vars_length']) fun j h1 h2 => ?_
        rw [vars_getElem]
        have hj : j < nf := by simpa using h1
        have e : ((List.range nf).reverse.map (fun j => σ j))[j]'(by simpa using hj) =
            σ (nf - 1 - j) := by simp [List.getElem_reverse]
        rw [e, show 0 + (nf - 1 - j) = nf - 1 - j by omega]; exact .bvar'
    have hfp' : SemSig.famProp ci.family ((lv.map (·.inst ls)).map (·.eval)) = false := by
      rw [← hfp]; simp [RuleMajor.lvls, List.map_map, Function.comp_def]
    obtain ⟨n', fs, hfl, hI, hfx⟩ := realize_sig H W hci hfamd hsem hstr hM hal hxs hfp'
    have hnfc : SemSig.nfields c = ci.nfields := by
      show (match sigCtor env c with | some ci => ci.nfields | none => 0) = _
      rw [hci]
    refine ⟨n', fs, by rw [hfl, hnfc], hI, fun i hi => ⟨fun hal' => ?_, fun hun => ?_⟩⟩
    · have hk : i + fs.length - nf < fs.length := by omega
      rw [List.getD_of_lt' hk]
      have := forall₂_getElem hfx (i := i + fs.length - nf) (by rw [hfx.length_eq]; exact hk)
      simp only [List.getElem_drop] at this
      have hal2 : (ps.map (·.instL ls)).length + nf = ci.nparams + ci.nfields := by
        simpa only [List.length_append, vars_length'] using hal
      have hpos : ci.nparams + (i + fs.length - nf) = (ps.map (·.instL ls)).length + i := by
        omega
      have e : xs[ci.nparams + (i + fs.length - nf)]'(by
          simp only [xs, List.length_append, List.length_map, List.length_reverse,
            List.length_range]; simp only [List.length_map] at hal2; omega) =
          σ (nf - 1 - i) := by
        simp only [xs, hpos]
        rw [List.getElem_append_right (by simp)]
        simp [List.getElem_reverse]
      rw [e] at this
      exact this
    · left
      rw [hfi]
      have hlo : i < structNp env c - ps.length := by
        rw [← hnp]; simp [vars_length'] at hal; omega
      exact fieldIndexOf_isSome hi hlo (by simp [vars_length']; have := hleft i hi hlo; omega)

end

end Lean4Lean.ShapeModel
