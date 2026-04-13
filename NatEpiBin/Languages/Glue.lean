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
 | Ftype {ForeignProps : Type} : Agent -> ForeignProps -> Proposition

-- TODO: Extend typeclass that allows printing to string
inductive Expr : Type 1
  | var : String -> Expr
  | lambda : String -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | box : Agent -> Expr -> Expr
  | letbox : Agent -> String -> Expr -> Expr -> Expr
  | fexpr {ForeignExpressions : Type} : Agent -> ForeignExpressions -> Expr

inductive Judgment : Type 1
  | tytrue : Expr -> Proposition -> Judgment
  | tyknows : Agent -> Expr -> Proposition -> Judgment

inductive Ctxt : Type 1
  | ø : Ctxt
  | extend (Gamma : Ctxt) (ty : Judgment) : Ctxt

inductive Lookup : Ctxt -> Judgment -> Type 1
  | here : Lookup (Ctxt.extend Gamma j) j
  | there : Lookup Gamma j -> Lookup (Ctxt.extend Gamma eB) j

inductive CtxtMap {ForeignCtxt : Type} : Ctxt -> Agent -> ForeignCtxt -> Type 1
  | empty [fc : FCtxt FJs ForeignCtxt] : CtxtMap Ctxt.ø k fc.empty
  | keep
    [js : FJudgment Es Ts FJs]
    [fc : FCtxt js ForeignCtxt]:
    CtxtMap Gamma k Gamma'
    -> CtxtMap
        (Ctxt.extend Gamma (Judgment.tyknows k (Expr.fexpr k F) J))
        k
        (fc.extend Gamma' (js.makeJudgment F τ))
  | drop
    [js : FJudgment Es Ts FJs]
    [fc : FCtxt js ForeignCtxt] :
    CtxtMap Gamma k Gamma' -> l ≠ k ->
    CtxtMap (Ctxt.extend Gamma (Judgment.tyknows l (Expr.fexpr l F) J)) k Gamma'

-- Class that captures the notion of type-mapping
class TypeMap (A : Type 1) (B : Type) where
  typeMap : A -> B -> Type

-- Type-checking judgment
inductive TypeCheck : (Pair Ctxt Ctxt) -> Judgment -> Type 2
  | hyp :
      Lookup Delta (Judgment.tytrue (Expr.var x) A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.var x) A)
  | hypstar { C : Proposition } { τ : B } [typeMap : TypeMap Proposition B] :
      typeMap.typeMap C τ
      -> Lookup Delta (Judgment.tyknows k (Expr.var x) (Proposition.Ftype k τ))
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.var x) C)
  | lambdaI :
      TypeCheck ⟨Gamma, Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)⟩ (Judgment.tytrue e B)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.lambda x e) (Proposition.Lam A B))
  | lambdaE :
      TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e1 (Proposition.Lam A B))
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e2 A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.app e1 e2) B)
  -- | boxI { F : FExprs } { τ : FTypes }
  --     [foreignJudgmentProp : FJudgment FExprs FTypes]
  --     [foreignTypeChecker : FTypeCheck foreignJudgmentProp]
  --     {foreignJudgment : foreignJudgmentProp.makeJudgment F τ}
  --     {ForeignPhi : FCtxt foreignJudgmentProp}:
  --     CtxtMap Gamma k ForeignPhi
  --     -> foreignTypeChecker.typeCheck ForeignPhi foreignJudgment
  --     -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.box k (Expr.fexpr k F)) (Proposition.Box k (Proposition.Ftype k τ)))
