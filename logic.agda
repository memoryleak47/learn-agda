open import Agda.Builtin.String
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

data FormulaSkol : Set where
  _∧_ : FormulaSkol -> FormulaSkol -> FormulaSkol
  _∨_ : FormulaSkol -> FormulaSkol -> FormulaSkol
  _::_ : RelSym -> List Term -> FormulaSkol
  _¬::_ : RelSym -> List Term -> FormulaSkol

data Atom : Set where
  :Atom : RelSym -> List Term -> Atom

data Literal : Set where
  Pos : Atom -> Literal
  Neg : Atom -> Literal

data Clause : Set where
  :Clause : List Literal -> Clause

data ClauseSet : Set where
  :ClauseSet : List Clause -> ClauseSet

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
