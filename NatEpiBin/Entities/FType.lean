-- Types foreign to the epistemic glue language will be FTypes
class FType (τ : Type) where
  fType : τ -> FType τ
