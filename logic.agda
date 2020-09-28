open import base

module logic where

data VarSym : Set where
  :VarSym : String -> VarSym

data FnSym : Set where
  :FnSym : String -> FnSym

data RelSym : Set where
  :RelSym : String -> RelSym

data Term : Set where
  var : VarSym -> Term
  func : FnSym -> List Term -> Term

data Formula : Set where
  _∧_ : Formula -> Formula -> Formula
  _∨_ : Formula -> Formula -> Formula
  ¬_ : Formula -> Formula
  _::_ : RelSym -> List Term -> Formula
  _⋀_ : VarSym -> Formula -> Formula
  _⋁_ : VarSym -> Formula -> Formula

data FormulaNNF : Set where
  _∧_ : FormulaNNF -> FormulaNNF -> FormulaNNF
  _∨_ : FormulaNNF -> FormulaNNF -> FormulaNNF
  _::_ : RelSym -> List Term -> FormulaNNF
  _¬::_ : RelSym -> List Term -> FormulaNNF
  _⋀_ : VarSym -> FormulaNNF -> FormulaNNF
  _⋁_ : VarSym -> FormulaNNF -> FormulaNNF


data Atom : Set where
  _::_ : RelSym -> List Term -> Atom

data Literal : Set where
  Pos : Atom -> Literal
  Neg : Atom -> Literal

data FormulaSkol : Set where
  _∧_ : FormulaSkol -> FormulaSkol -> FormulaSkol
  _∨_ : FormulaSkol -> FormulaSkol -> FormulaSkol
  η : Literal -> FormulaSkol

Clause = List Literal
ClauseSet = List Clause

nnf : Formula -> FormulaNNF
nnf (x ∧ y) = nnf x ∧ nnf y
nnf (x ∨ y) = nnf x ∨ nnf y
nnf (x :: y) = x :: y
nnf (v ⋀ x) = v ⋀ nnf x
nnf (v ⋁ x) = v ⋁ nnf x
nnf (¬ (x ∧ y)) = (nnf (¬ x)) ∨ (nnf (¬ y))
nnf (¬ (x ∨ y)) = (nnf (¬ x)) ∧ (nnf (¬ y))
nnf (¬ (¬ x)) = nnf x
nnf (¬ (x :: y)) = x ¬:: y
nnf (¬ (v ⋀ x)) = v ⋁ (nnf (¬ x))
nnf (¬ (v ⋁ x)) = v ⋀ (nnf (¬ x))

{-# TERMINATING #-}
subst-term : Term -> VarSym -> Term -> Term
subst-term (var (:VarSym x)) (:VarSym s) t with primStringEquality x s
... | true = t
... | false = var (:VarSym x)
subst-term (func fname l) s t = (func fname (map (λ x -> subst-term x s t) l))

subst : FormulaNNF -> VarSym -> Term -> FormulaNNF
subst (f ∧ f₁) s t = subst f s t ∧ subst f₁ s t
subst (f ∨ f₁) s t = subst f s t ∨ subst f₁ s t
subst (P :: l) s t = P :: map (λ x -> subst-term x s t) l
subst (P ¬:: l) s t = P ¬:: map (λ x -> subst-term x s t) l
subst (x ⋀ f) s t = (x ⋀ subst f s t) -- TODO naming collisions
subst (x ⋁ f) s t = (x ⋁ subst f s t) -- TODO naming collisions

vartofn : VarSym -> FnSym
vartofn (:VarSym x) = :FnSym x -- TODO may have naming collisions

{-# TERMINATING #-}
skolemize-impl : List VarSym -> FormulaNNF -> FormulaSkol
skolemize-impl l (x ∧ y) = skolemize-impl l x ∧ skolemize-impl l y
skolemize-impl l (x ∨ y) = skolemize-impl l x ∨ skolemize-impl l y
skolemize-impl l (x :: y) = η (Pos (x :: y))
skolemize-impl l (x ¬:: y) = η (Neg (x :: y))
skolemize-impl l (x ⋀ y) = skolemize-impl (x :: l) y
skolemize-impl l (x ⋁ y) = skolemize-impl l (subst y x (func (vartofn x) (map var l)))

skolemize : FormulaNNF -> FormulaSkol
skolemize a = skolemize-impl [] a


clauselize-helper2 : Clause -> ClauseSet -> ClauseSet
clauselize-helper2 x [] = []
clauselize-helper2 x (a :: y) = (x ∪ a) :: clauselize-helper2 x y

clauselize-helper : ClauseSet -> ClauseSet -> ClauseSet
clauselize-helper [] C₂ = C₂
clauselize-helper (x :: xs) C₂ = clauselize-helper2 x C₂ ∪ clauselize-helper xs C₂

clauselize : FormulaSkol -> ClauseSet
clauselize (f ∧ f₁) = clauselize f ∪ clauselize f₁
clauselize (η x)  = (x :: []) :: []
clauselize (f ∨ f₁) = clauselize-helper (clauselize f) (clauselize f₁)
