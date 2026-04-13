import NatEpiBin.Languages.Glue
import NatEpiBin.Languages.Unary

def exampleExpr : Epistemic.Expr :=
  Epistemic.Expr.fexpr "U" (Unary.Expr.var "x")

def exampleType : Epistemic.Proposition :=
  Epistemic.Proposition.Ftype "U" (Unary.Proposition.Nat)
