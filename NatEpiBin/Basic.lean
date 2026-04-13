/-
  Author : Luis Garcia
  Definition : Types for an epistemic S4
-/
-- We'll make agents strings for now.
-- In actuality, they should be elements of a
-- universe of agents.
import NatEpiBin.Entities.Pair
import NatEpiBin.Entities.TypeCheck

def Agent := String
instance : DecidableEq Agent := inferInstanceAs (DecidableEq String)

-- TODO: Move this to a utils file


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

inductive Judgment : Type
  | tytrue : Expr -> Proposition -> Judgment
  | tyknows : Agent -> Expr -> Proposition -> Judgment

inductive Ctxt : Type
  | ø : Ctxt
  | extend (Gamma : Ctxt) (ty : Judgment) : Ctxt

inductive Lookup : Ctxt -> Judgment -> Type
  | here : Lookup (Ctxt.extend Gamma j) j
  | there : Lookup Gamma j -> Lookup (Ctxt.extend Gamma eB) j

inductive KnowledgeRestriction : Ctxt -> Agent -> Ctxt -> Type
  | base : KnowledgeRestriction Ctxt.ø k Ctxt.ø
  | keep : KnowledgeRestriction Gamma k Gamma'
    -> KnowledgeRestriction (Ctxt.extend Gamma (Judgment.tyknows k e j)) a (Ctxt.extend Gamma' (Judgment.tyknows k e j))
  | drop : KnowledgeRestriction Gamma k Gamma' -> ¬ (l = k)
    -> KnowledgeRestriction (Ctxt.extend Gamma (Judgment.tyknows l e j)) k Gamma'

-- Example expressions
private def exampleId : Expr :=
  Expr.lambda "x" (Expr.var "x")

-- Type-checking judgment
inductive TypeCheck : (Pair Ctxt Ctxt) -> (Pair Expr Proposition) -> Type
  | hyp :
      Lookup Delta (Judgment.tytrue (Expr.var x) A)
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.var x, A⟩
  | lambdaI :
      TypeCheck ⟨Gamma, Ctxt.extend Delta (Judgment.tytrue (Expr.var x) A)⟩ ⟨e, B⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.lambda x e, Proposition.Lam A B⟩
  | lambdaE :
      TypeCheck ⟨Gamma, Delta⟩ ⟨e1, Proposition.Lam A B⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨e2, A⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.app e1 e2, B⟩
  | boxI :
      KnowledgeRestriction Gamma k Gamma'
      -> TypeCheck ⟨Gamma', Ctxt.ø⟩ ⟨e, A⟩
      -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.box k e, Proposition.Box k A⟩
  | boxE :
    TypeCheck ⟨Gamma, Delta⟩ ⟨e1, Proposition.Box k A⟩
    -> TypeCheck ⟨Ctxt.extend Gamma (Judgment.tyknows k (Expr.var u) A) , Delta⟩ ⟨e2, C⟩
    -> TypeCheck ⟨Gamma, Delta⟩ ⟨Expr.letbox k u e1 e2, C⟩

def lookup? (ctxt : Ctxt) (eA : Judgment) : Option (Lookup ctxt eA) :=
  match ctxt, eA with
  | Ctxt.ø, _ => none
  | Ctxt.extend Gamma (Judgment.tytrue (Expr.var x) A), (Judgment.tytrue (Expr.var y) B) =>
    if eA == eB then
      some (Lookup.here)
    else
      some

-- Algorithmically build a TypeCheck
def typeCheck? (ctxts : Pair Ctxt Ctxt) (eA : Pair Expr Proposition) : Option (TypeCheck ctxts eA)
  | ⟨Gamma, Delta⟩ ⟨Expr.var x, A⟩ =>

-- simple proof of the identity function having type A -> A
-- private theorem exampleIdProof : TypeCheck ⟨Ctxt.ø, Ctxt.ø⟩ ⟨Expr.lambda "x" (Expr.var "x"), Proposition.Lam (Proposition.Atom "A") (Proposition.Atom "A")⟩ :=
--   TypeCheck.lambdaI (TypeCheck.hyp (Lookup.here))

-- -- example knowledge restriction
-- private theorem exampleKnowledgeRestriction : KnowledgeRestriction
--   (Ctxt.extend
--     (Ctxt.extend
--       Ctxt.ø
--         (Judgment.tyknows "K" (Expr.var "x") (Proposition.Atom "A")))
--         (Judgment.tyknows "L" (Expr.var "x") (Proposition.Atom "A")))
--   "K"
--   (Ctxt.extend
--     Ctxt.ø
--       (Judgment.tyknows "K" (Expr.var "x") (Proposition.Atom "A")))
--   :=
--   KnowledgeRestriction.drop
--     (KnowledgeRestriction.keep
--       KnowledgeRestriction.base)
--     (by decide)
