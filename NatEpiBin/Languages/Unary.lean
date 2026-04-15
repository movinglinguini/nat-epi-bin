/-
  Unary number language that has natural numbers and lambdas
-/
namespace Unary

inductive Proposition : Type
  | Nat : Proposition
  | Lam : Proposition -> Proposition -> Proposition

inductive Expr : Type
  | var : String -> Expr
  | lam : String -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | plus : Expr -> Expr -> Expr
  | zero : Expr
  | succ : Expr -> Expr

inductive Judgment : Type
  | tytrue : Expr -> Proposition -> Judgment

inductive Ctxt : Type
  | ø : Ctxt
  | extend (Gamma : Ctxt) (ty : Judgment) : Ctxt

inductive Lookup : Ctxt -> Judgment -> Type
  | here : Lookup (Ctxt.extend Gamma j) j
  | there : Lookup Gamma j -> Lookup (Ctxt.extend Gamma eB) j

inductive TypeCheck : Ctxt -> Judgment -> Type
  | hyp :
      Lookup Delta (Judgment.tytrue (Expr.var x) A)
      -> TypeCheck Delta (Judgment.tytrue (Expr.var x) A)
  | lambdaI :
      TypeCheck (Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)) (Judgment.tytrue e B)
      -> TypeCheck Delta (Judgment.tytrue (Expr.lam x e) (Proposition.Lam A B))
  | lambdaE :
      TypeCheck Delta (Judgment.tytrue e1 (Proposition.Lam A B))
      -> TypeCheck Delta (Judgment.tytrue e2 A)
      -> TypeCheck Delta (Judgment.tytrue (Expr.app e1 e2) B)
  | plus :
    TypeCheck Delta (Judgment.tytrue n1 Proposition.Nat)
    -> TypeCheck Delta (Judgment.tytrue n2 Proposition.Nat)
    -> TypeCheck Delta (Judgment.tytrue (Expr.plus n1 n2) Proposition.Nat)
  | zeroI : TypeCheck Delta (Judgment.tytrue Expr.zero Proposition.Nat)
  | succI :
      TypeCheck Delta (Judgment.tytrue e Proposition.Nat)
      -> TypeCheck Delta (Judgment.tytrue (Expr.succ e) Proposition.Nat)
