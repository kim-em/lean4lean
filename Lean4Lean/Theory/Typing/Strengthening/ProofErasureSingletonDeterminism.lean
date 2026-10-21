import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment

/-! # Exact determinism of singleton roots

Different valid singleton codes for the same registered constant instance and
supplied arity are identical. Their telescopes and outputs therefore agree,
independently of which comparison relation certifies their family guards.
This resolves singleton/singleton root overlaps, not nested computations or
overlaps with ordinary delta, projection or template roots.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
variable [Params]

/-- Registration, universe instance and supplied arity determine every field
of a valid singleton prefix code. Generation and guard witnesses introduce no
choice of computational output. -/
theorem SingletonPrefixCode.Valid.unique
    {C C' : SingletonPrefixCode}
    (V : C.Valid) (W : C'.Valid) (hname : C.data.name = C'.data.name)
    (hlevels : C.levels = C'.levels) (harity : C.arity = C'.arity) : C = C' := by
  have hw := W.lookup
  rw [← hname] at hw
  have hd := Option.some.inj (V.lookup.symm.trans hw)
  cases C with
  | mk data levels arity recType equation body layout elim =>
    cases C' with
    | mk data' levels' arity' recType' equation' body' layout' elim' =>
      cases hd
      cases hlevels
      cases harity
      have hr := Option.some.inj (V.recType_eq.symm.trans W.recType_eq)
      cases hr
      have he := Option.some.inj (V.equation_eq.symm.trans W.equation_eq)
      cases he
      have hb := Option.some.inj (V.body_eq.symm.trans W.body_eq)
      cases hb
      have hl := Option.some.inj (V.layout_eq.symm.trans W.layout_eq)
      cases hl
      have he := Option.some.inj (V.elim_eq.symm.trans W.elim_eq)
      cases he
      rfl

/-- Two singleton primitives at the same raw source have the same literal
output, even when their guards use different comparators. No source typing,
canonical Eq, beta transport or computational confluence is assumed. -/
theorem ProofShape.SingletonPrimitiveWith.deterministic
    (H : SingletonPrimitiveWith Cmp Δ source out)
    (H' : SingletonPrimitiveWith Cmp' Δ source out') : out = out' := by
  cases H with
  | @intro C args domains result V ha hcalc HG =>
    generalize E : mkApps (.const C.data.name C.levels) args = source at H'
    cases H' with
    | @intro C' args' domains' result' V' ha' hcalc' HG' =>
      obtain ⟨hname, hlevels, rfl⟩ := const_spine_inj E
      have EC := V.unique V' hname hlevels (ha.symm.trans ha')
      cases EC
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hcalc.symm.trans hcalc'))
      rfl

end Lean4Lean.VEnv.Strengthening
