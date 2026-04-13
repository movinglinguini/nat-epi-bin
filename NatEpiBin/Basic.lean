import NatEpiBin.Abstractions.FTypeCheck

-- import NatEpiBin.Languages.Glue
import NatEpiBin.Languages.Unary

instance unaryJudgment : FJudgment Unary.Expr Unary.Proposition Unary.Judgment where
  makeJudgment e A := Unary.Judgment.tytrue e A

instance unaryCtxt : FCtxt unaryJudgment Unary.Ctxt where
  empty := Unary.Ctxt.ø
  extend Gamma J := Unary.Ctxt.extend Gamma J

instance : FTypeCheck unaryJudgment unaryCtxt where
  typeCheck := Unary.TypeCheck

-- def exampleExpr : Epistemic.Expr :=
--   Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero))

-- def exampleTypeCheck : Epistemic.TypeCheck
--   ⟨Epistemic.Ctxt.ø, Epistemic.Ctxt.ø⟩
--   (Epistemic.Judgment.tytrue exampleExpr (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" (Unary.Proposition.Nat)))) :=
--   Epistemic.TypeCheck.boxI
--     (Epistemic.CtxtMap.empty)
--     ()
