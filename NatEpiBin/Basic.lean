/-
  Author : Luis Garcia
  Definition : Types for an epistemic S4
-/
-- We'll make agents strings for now.
-- In actuality, they should be elements of a
-- universe of agents.
def Agent := String

-- TODO: Move this to a utils file
structure Pair (A B : Type) where
  (first : A)
  (second : B)

-- TODO: Extend typeclass that allows printing to string
inductive Proposition : Type
 | Atom : String -> Proposition
 | Lam : Proposition -> Proposition -> Proposition
 | Box : Agent -> Proposition -> Proposition

-- TODO: Extend typeclass that allows printing to string
inductive Expr : Type
  | var : String -> Expr
  | lambda : String -> Expr -> Expr
  | app : Expr -> Expr -> Expr
  | box : Agent -> Expr -> Expr
  | letbox : Agent -> String -> Expr -> Expr -> Expr

inductive TyTrue : Type
  | true : Expr -> Proposition -> TyTrue

inductive TyKnow : Type
  | knows : Agent -> Expr -> Proposition -> TyKnow

inductive Ctxt : Type
  | ø : Ctxt
  | extend (Gamma : Ctxt) (eA : Pair Expr Proposition) : Ctxt

inductive Lookup : Ctxt -> (Pair Expr Proposition) -> Prop
  | here : Lookup (Ctxt.extend Gamma eA) eA
  | there : Lookup Gamma eA -> Lookup (Ctxt.extend Gamma eB) eA

-- Example expressions
private def exampleId : Expr :=
  Expr.lambda "x" (Expr.var "x")

inductive TypeCheck : (Pair Ctxt Ctxt) -> (Pair Expr Proposition) -> Prop
  | hyp :
      Lookup Delta ⟨(Expr.var x), A⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.var x, A⟩
  | lambdaI :
      TypeCheck ⟨Gamma, Ctxt.extend Delta ⟨Expr.var x, A⟩⟩ ⟨e, B⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.lambda x e, Proposition.Lam A B⟩
  | lambdaE :
      TypeCheck ⟨Gamma, Delta⟩ ⟨e1, Proposition.Lam A B⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨e2, A⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.app e1 e2, B⟩
  | boxI :
      TypeCheck ⟨Gamma, Ctxt.ø⟩ ⟨e, A⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.box a e, Proposition.Box a A⟩
  | boxE :
    TypeCheck ⟨Gamma, Delta⟩ ⟨e1, Proposition.Box a A⟩
    -> TypeCheck ⟨Ctxt.extend Gamma ⟨Expr.var u, A⟩ , Delta⟩ ⟨e2, C⟩
    -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.letbox a u e1 e2, C⟩


-- simple proof of the identity function having type A -> A
private theorem exampleIdProof : TypeCheck ⟨Ctxt.ø, Ctxt.ø⟩ ⟨Expr.lambda "x" (Expr.var "x"), Proposition.Lam (Proposition.Atom "A") (Proposition.Atom "A")⟩ :=
  TypeCheck.lambdaI (TypeCheck.hyp (Lookup.here))
