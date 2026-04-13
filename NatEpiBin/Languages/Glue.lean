/-
  Author : Luis Garcia
  Definition : Types for an epistemic S4
-/
-- We'll make agents strings for now.
-- In actuality, they should be elements of a
-- universe of agents.
import NatEpiBin.Entities.Pair
import NatEpiBin.Entities.FExpr
import NatEpiBin.Entities.FType

import NatEpiBin.Abstractions.FTypeCheck


namespace Epistemic

-- Agent identifiers are just strings.
def Agent := String
instance : DecidableEq Agent := inferInstanceAs (DecidableEq String)

-- TODO: Extend typeclass that allows printing to string
inductive Proposition : Type 1
 | Atom : String -> Proposition
 | Lam : Proposition -> Proposition -> Proposition
 | Box : Agent -> Proposition -> Proposition
 | Ftype : Agent -> ForeignType -> Proposition

-- TODO: Extend typeclass that allows printing to string
inductive Expr : Type 1
  | var : String -> Expr
  | lambda : String -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | box : Agent -> Expr -> Expr
  | letbox : Agent -> String -> Expr -> Expr -> Expr
  | fexpr : Agent -> ForeignExpression -> Expr

inductive Judgment : Type 1
  | tytrue : Expr -> Proposition -> Judgment
  | tyknows : Agent -> Expr -> Proposition -> Judgment

inductive Ctxt : Type 1
  | ø : Ctxt
  | extend (Gamma : Ctxt) (ty : Judgment) : Ctxt

inductive Lookup : Ctxt -> Judgment -> Type 1
  | here : Lookup (Ctxt.extend Gamma j) j
  | there : Lookup Gamma j -> Lookup (Ctxt.extend Gamma eB) j

inductive CtxtMap (Judgments : FJudgment FExprs FTypes) : Ctxt -> Agent -> FCtxt Judgments -> Type 1
  | empty : CtxtMap Judgments Ctxt.ø k FCtxt.ø
  | keep : CtxtMap Judgments Gamma k Gamma'
    -> CtxtMap Judgments (Ctxt.extend Gamma (Judgment.tyknows k e J)) k (FCtxt.extend Gamma' (Judgments.makeJudgment f τ))
  | drop : CtxtMap Judgments Gamma k Gamma' -> ¬ (l = k)
    -> CtxtMap Judgments (Ctxt.extend Gamma (Judgment.tyknows l e J)) k Gamma'

-- Class that captures the notion of type-mapping
class TypeMap (A : Proposition) (B : FType τ) where
  typeMap : τ -> TypeMap A B
  foreignType : τ

-- Example expressions
private def exampleId : Expr :=
  Expr.lambda "x" (Expr.var "x")

-- Type-checking judgment
inductive TypeCheck : (Pair Ctxt Ctxt) -> Judgment -> Type 1
  | hyp :
      Lookup Delta (Judgment.tytrue (Expr.var x) A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.var x) A)
  | hypstar [typeMap : TypeMap A B] :
      Lookup Delta (Judgment.tyknows k (Expr.var x) (Proposition.Ftype k B))
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.var x) A)
  | lambdaI :
      TypeCheck ⟨Gamma, Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)⟩ (Judgment.tytrue e B)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.lambda x e) (Proposition.Lam A B))
  | lambdaE :
      TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e1 (Proposition.Lam A B))
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e2 A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.app e1 e2) B)
  -- | boxI
  --   [fJudgments : FJudgment FExprs FTypes]
  --   (FGamma : FCtxt fJudgments)
  --   [fTypeChecker : FTypeCheck TypeCheckProp fGamma]
  --   [fExpr : FExpr f]
  --   :
  --     CtxtMap fJudgments Gamma k FGamma
  --     -> TypeCheckProp
  --     -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.box k (Expr.fexpr k f)) (Proposition.Box k (Proposition.Ftype k τ)))
  | boxE :
    TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e1 (Proposition.Box k (Proposition.Ftype k τ)))
    -> TypeCheck ⟨Ctxt.extend Gamma (Judgment.tyknows k (Expr.var u) (Proposition.Ftype k τ)) , Delta⟩
                  (Judgment.tytrue e2 C)
    -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.letbox k u e1 e2) C)
