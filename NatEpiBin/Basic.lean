import NatEpiBin.Abstractions.FTypeCheck

import NatEpiBin.Languages.Glue
import NatEpiBin.Languages.Unary

instance unaryExpr : FExpr Unary.Expr where
  var := Unary.Expr.var

instance unaryJudgment : FJudgment unaryExpr Unary.Proposition Unary.Judgment where
  makeJudgment e A := Unary.Judgment.tytrue e A

instance unaryCtxt : FCtxt unaryJudgment Unary.Ctxt where
  empty := Unary.Ctxt.ø
  extend Gamma J := Unary.Ctxt.extend Gamma J

-- instance unaryTypeCheck : FTypeCheck unaryJudgment unaryCtxt where


-- example type check
-- typecheck a boxed natural number
private def natCheck : Unary.TypeCheck
  Unary.Ctxt.ø
  (Unary.Judgment.tytrue Unary.Expr.zero Unary.Proposition.Nat)
  := Unary.TypeCheck.zeroI

-- ·;· ⊢ boxᵤ 0 : □ᵤℕ
private def exampleTypeCheck1 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.ø, Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (Epistemic.CtxtMap.empty)
      (Unary.TypeCheck.zeroI)
  )

-- u ::ᵤ ℕ ;· ⊢ boxᵤ 0 : □ᵤℕ
-- Should have to keep u in the epistemic context since the target agent is U
private def exampleCheck2 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.extend
    Epistemic.Ctxt.ø
    (Epistemic.Judgment.tyknows "U"
      (Epistemic.Expr.var "u")
      (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)),
   Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (Epistemic.CtxtMap.keep (Epistemic.CtxtMap.empty))
      (Unary.TypeCheck.zeroI)
  )

-- u ::ₐ ℕ ;· ⊢ boxᵤ 0 : □ᵤℕ
-- Should have to drop u from the epistemic context since the target agent is not U
private def exampleCheck3 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.extend
    Epistemic.Ctxt.ø
    (Epistemic.Judgment.tyknows "A"
      (Epistemic.Expr.var "u")
      (Epistemic.Proposition.Ftype "A" Unary.Proposition.Nat)),
   Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (
        Epistemic.CtxtMap.drop
        (Epistemic.CtxtMap.empty)
        (by grind)
      )
      (Unary.TypeCheck.zeroI)
  )
