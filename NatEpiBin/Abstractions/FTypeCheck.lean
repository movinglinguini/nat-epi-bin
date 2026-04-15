import NatEpiBin.Entities.FExpr
import NatEpiBin.Entities.FType

class FJudgment (FEs : FExpr f) (τ : Type) (J : Type) where
  makeJudgment : f -> τ -> J

class FCtxt (FJ : FJudgment Es Ts Js) (C : Type) where
  empty : C
  extend: C -> Js -> C
