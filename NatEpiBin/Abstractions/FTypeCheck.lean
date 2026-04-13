import NatEpiBin.Entities.FExpr
import NatEpiBin.Entities.FType

class FJudgment (FExprs : FExpr f) (FTypes : FType τ)  where
  makeJudgment : f -> τ -> FJudgment FExprs FTypes

inductive FCtxt (Judgments : FJudgment FExprs FTypes) :
    Type 1
  | ø : FCtxt Judgments
  | extend (Gamma : FCtxt Judgments) (J : FJudgment FExprs FTypes) : FCtxt Judgments

class FTypeCheck {Judgments : FJudgment FExprs FTypes} (TypeCheckProp : Type) (FCtx : FCtxt Judgments) where
  typeCheck : FJudgment FExprs FTypes -> TypeCheckProp
