import NatEpiBin.Entities.FExpr
import NatEpiBin.Entities.FType

class FJudgment (F : Type) (τ : Type) (J : Type) where
  makeJudgment : F -> τ -> J

-- inductive FCtxt (Judgments : FJudgment FExprs FTypes FJudgments)
--   | ø : FCtxt Judgments
--   | extend { F : FExprs } { τ : FTypes } (Gamma : FCtxt Judgments) (J : FJudgments) : FCtxt Judgments

class FCtxt (FJ : FJudgment Es Ts Js) (C : Type) where
  empty : C
  extend: C -> Js -> C

class FTypeCheck (Judgments : FJudgment Es Ts Js) (FC : FCtxt Judgments Cs) where
  typeCheck : Cs -> Js -> Type

-- class FTypeCheck { F : FExprs } { τ : FTypes } (Judgments : FJudgment FExprs FTypes FJudgments) (T : Type) where
--   typeCheck : FCtxt Judgments -> FJudgments -> T
