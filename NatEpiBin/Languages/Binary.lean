namespace Binary

inductive Proposition : Type where
  | Bin : Proposition
  | Lam : Proposition -> Proposition -> Proposition

inductive Expr : Type where
  | var : String -> Expr
  | lam : String -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | bin : Expr
  | one : Expr -> Expr
  | zero : Expr -> Expr

-- 01
private def exampleBinaryNumber : Expr
 := Expr.one (Expr.zero Expr.bin)

inductive Judgment : Type
  | tytrue : Expr -> Proposition -> Judgment

inductive Ctxt : Type where
  | ø : Ctxt
  | extend : Ctxt -> Judgment -> Ctxt

inductive Lookup : Ctxt -> Judgment -> Type where
  | here : Lookup (Ctxt.extend Gamma J) J
  | there : Lookup Gamma J
    -> Lookup (Ctxt.extend Gamma G) J

inductive TypeCheck : Ctxt -> Judgment -> Type where
  | hyp :
    Lookup Gamma (Judgment.tytrue (Expr.var x) A)
    -> TypeCheck Gamma (Judgment.tytrue (Expr.var x) A)
  | lambdaI :
      TypeCheck (Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)) (Judgment.tytrue e B)
      -> TypeCheck Delta (Judgment.tytrue (Expr.lam x e) (Proposition.Lam A B))
  | lambdaE :
      TypeCheck Delta (Judgment.tytrue e1 (Proposition.Lam A B))
      -> TypeCheck Delta (Judgment.tytrue e2 A)
      -> TypeCheck Delta (Judgment.tytrue (Expr.app e1 e2) B)
  | binZeroBase :
    TypeCheck Gamma (Judgment.tytrue (Expr.zero Expr.bin) Proposition.Bin)
  | binOneBase :
    TypeCheck Gamma (Judgment.tytrue (Expr.one Expr.bin) Proposition.Bin)
  | binZeroInduct :
    TypeCheck Gamma (Judgment.tytrue B Proposition.Bin)
    -> TypeCheck Gamma (Judgment.tytrue (Expr.zero B) Proposition.Bin)
  | binOneInduct :
    TypeCheck Gamma (Judgment.tytrue B Proposition.Bin)
    -> TypeCheck Gamma (Judgment.tytrue (Expr.one B) Proposition.Bin)
