class TypeChecker (ctxt : Type) (expr : Type) (ty : Type) where
  typeCheck : ctxt -> expr -> ty -> Prop
