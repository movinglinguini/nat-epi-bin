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
import NatEpiBin.Entities.TypeMap

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
  | tell : Agent -> String -> Expr -> Expr -> Expr

inductive Judgment : Type 1
  | tytrue : Expr -> Proposition -> Judgment
  | tyknows : Agent -> Expr -> Proposition -> Judgment

inductive Ctxt : Type 1
  | ø : Ctxt
  | extend (Gamma : Ctxt) (ty : Judgment) : Ctxt

inductive Lookup : Ctxt -> Judgment -> Type 1
  | here : Lookup (Ctxt.extend Gamma j) j
  | there : Lookup Gamma j -> Lookup (Ctxt.extend Gamma eB) j

inductive CtxtMap
    [es : FExpr Es]
    [js : FJudgment es Ts FJs]
    (fc : FCtxt js ForeignCtxt) : Ctxt -> Agent -> ForeignCtxt -> Type 1
  | empty : CtxtMap fc Ctxt.ø k fc.empty
  | keep :
    CtxtMap fc Gamma k Gamma'
    -> CtxtMap
        fc
        (Ctxt.extend Gamma (Judgment.tyknows k (Expr.var u) (Proposition.Ftype k τ)))
        k
        (fc.extend Gamma' (js.makeJudgment (es.var u) τ))
  | drop :
    CtxtMap fc Gamma k Gamma' -> l ≠ k ->
    CtxtMap fc (Ctxt.extend Gamma (Judgment.tyknows l (Expr.var u) J)) k Gamma'

-- Type-checking judgment
inductive TypeCheck : (Pair Ctxt Ctxt) -> Judgment -> Type 2
  | hyp :
      Lookup Delta (Judgment.tytrue (Expr.var x) A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.var x) A)
  | hypstar  :
      Lookup Gamma (Judgment.tyknows k (Expr.var x) C)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tyknows k (Expr.var x) C)
  | lambdaI :
      TypeCheck ⟨Gamma, Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)⟩ (Judgment.tytrue e B)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.lambda x e) (Proposition.Lam A B))
  | lambdaE :
      TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e1 (Proposition.Lam A B))
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue e2 A)
      -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.app e1 e2) B)
  | boxI
    {TypeCheckProp : ForeignContext -> FJs -> Type }
    {Gamma' : ForeignContext}
    [fe : FExpr Es]
    [js : FJudgment fe Ts FJs]
    [fc : FCtxt js ForeignContext]
    :
    CtxtMap fc Gamma k Gamma'
    -> TypeCheckProp Gamma' (js.makeJudgment F τ)
    -> TypeCheck
      ⟨Gamma, Delta⟩
      (Judgment.tytrue
        (Expr.box k (Expr.fexpr k F))
        (Proposition.Box k (Proposition.Ftype k τ))
      )
  | boxE :
    TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue E1 (Proposition.Box k (Proposition.Ftype k τ)))
    -> TypeCheck
        ⟨Ctxt.extend Gamma (Judgment.tyknows k (Expr.var u) (Proposition.Ftype k τ)), Delta⟩
        (Judgment.tytrue E2 C)
    -> TypeCheck
        ⟨Gamma, Delta⟩
        (Judgment.tytrue (Expr.letbox k u E1 E2) C)
  | tell {FType1 FType2 A B Gamma Delta l E1 k u E2 C}
    { TypeMapProp : FType1 -> FType2 -> Type }:
    TypeMapProp A B
    -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tyknows l E1 (Proposition.Ftype l A))
    -> TypeCheck ⟨Ctxt.extend Gamma (Judgment.tyknows k (Expr.var u) (Proposition.Ftype k B)), Delta⟩ (Judgment.tytrue E2 C)
    -> TypeCheck ⟨Gamma, Delta⟩ (Judgment.tytrue (Expr.tell k u E1 E2) C)
