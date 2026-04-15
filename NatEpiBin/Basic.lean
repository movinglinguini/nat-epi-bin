import NatEpiBin.Entities.TypeMap

import NatEpiBin.Abstractions.FTypeCheck

import NatEpiBin.Languages.Glue
import NatEpiBin.Languages.Unary
import NatEpiBin.Languages.Binary

-- Unary type instances
instance unaryExpr : FExpr Unary.Expr where
  var := Unary.Expr.var

instance unaryJudgment : FJudgment unaryExpr Unary.Proposition Unary.Judgment where
  makeJudgment e A := Unary.Judgment.tytrue e A

instance unaryCtxt : FCtxt unaryJudgment Unary.Ctxt where
  empty := Unary.Ctxt.ø
  extend Gamma J := Unary.Ctxt.extend Gamma J

-- Binary type instances
instance binaryExpr : FExpr Binary.Expr where
  var := Binary.Expr.var

instance binaryJudgment : FJudgment binaryExpr Binary.Proposition Binary.Judgment where
  makeJudgment e A := Binary.Judgment.tytrue e A

instance binaryCtxt : FCtxt binaryJudgment Binary.Ctxt where
  empty := Binary.Ctxt.ø
  extend Gamma J := Binary.Ctxt.extend Gamma J

inductive NatToBinRel : Type where
  | NtoB (u : Unary.Proposition) (b : Binary.Proposition) :
    u = Unary.Proposition.Nat ->
    b = Binary.Proposition.Bin ->
    NatToBinRel

-- example type check
-- typecheck a boxed natural number
private def natCheck : Unary.TypeCheck
  Unary.Ctxt.ø
  (Unary.Judgment.tytrue Unary.Expr.zero Unary.Proposition.Nat)
  := Unary.TypeCheck.zeroI

-- ·;· ⊢ boxᵤ 0 : □ᵤℕ
private def exampleTypeCheck1 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.ø, Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (Epistemic.CtxtMap.empty)
      (Unary.TypeCheck.zeroI)
  )

-- u ::ᵤ ℕ ;· ⊢ boxᵤ 0 : □ᵤℕ
-- Should have to keep u in the epistemic context since the target agent is U
private def exampleCheck2 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.extend
    Epistemic.Ctxt.ø
    (Epistemic.Judgment.tyknows "U"
      (Epistemic.Expr.var "u")
      (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)),
   Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (Epistemic.CtxtMap.keep (Epistemic.CtxtMap.empty))
      (Unary.TypeCheck.zeroI)
  )

-- u ::ₐ ℕ ;· ⊢ boxᵤ 0 : □ᵤℕ
-- Should have to drop u from the epistemic context since the target agent is not U
private def exampleCheck3 : Epistemic.TypeCheck
  ⟨Epistemic.Ctxt.extend
    Epistemic.Ctxt.ø
    (Epistemic.Judgment.tyknows "A"
      (Epistemic.Expr.var "u")
      (Epistemic.Proposition.Ftype "A" Unary.Proposition.Nat)),
   Epistemic.Ctxt.ø⟩
  (Epistemic.Judgment.tytrue
    (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.zero)))
    (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)))
  :=
  (
    Epistemic.TypeCheck.boxI
      (
        Epistemic.CtxtMap.drop
        (Epistemic.CtxtMap.empty)
        (by grind)
      )
      (Unary.TypeCheck.zeroI)
  )

-- ·;· ⊢ letboxᵤ u = boxᵤ 1 in boxᵤ (plus u 2) : □ᵤℕ
private def exampleCheck4 :
  Epistemic.TypeCheck
    ⟨Epistemic.Ctxt.ø, Epistemic.Ctxt.ø⟩
    (Epistemic.Judgment.tytrue
      (Epistemic.Expr.letbox "U" "u" --=
        (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.succ Unary.Expr.zero))) -- in
        (Epistemic.Expr.box "U" (Epistemic.Expr.fexpr "U" (Unary.Expr.plus (Unary.Expr.var "u") (Unary.Expr.succ (Unary.Expr.succ Unary.Expr.zero)))))
      )
      (Epistemic.Proposition.Box "U" (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat))
    )
  :=
    (
      Epistemic.TypeCheck.boxE
      -- Typecheck the box part
      (
        Epistemic.TypeCheck.boxI
          (Epistemic.CtxtMap.empty)
          (Unary.TypeCheck.succI Unary.TypeCheck.zeroI)
      )
      -- Typecheck the in part
      (
        Epistemic.TypeCheck.boxI
          (Epistemic.CtxtMap.keep Epistemic.CtxtMap.empty)
          (
            Unary.TypeCheck.plus
              (Unary.TypeCheck.hyp Unary.Lookup.here)
              (Unary.TypeCheck.succI (Unary.TypeCheck.succI (Unary.TypeCheck.zeroI)))
          )
      )
    )

-- u ::ᵤ ℕ ; · ⊢ tellₐ w = u in boxₐ w : □ₐBin
private def exampleCheck5 :
  Epistemic.TypeCheck
    ⟨Epistemic.Ctxt.extend
    Epistemic.Ctxt.ø
    (Epistemic.Judgment.tyknows "U"
      (Epistemic.Expr.var "u")
      (Epistemic.Proposition.Ftype "U" Unary.Proposition.Nat)),
   Epistemic.Ctxt.ø⟩
   (
    Epistemic.Judgment.tytrue
      (Epistemic.Expr.tell "B" "w" (Epistemic.Expr.var "u") (Epistemic.Expr.box "B" (Epistemic.Expr.fexpr "B" (Binary.Expr.var "w"))))
      (Epistemic.Proposition.Box "B" (Epistemic.Proposition.Ftype "B" Binary.Proposition.Bin))
   )
