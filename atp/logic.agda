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
  ∀' : VarSym -> Formula -> Formula
  ∃' : VarSym -> Formula -> Formula

data FormulaNNF : Set where
  _∧_ : FormulaNNF -> FormulaNNF -> FormulaNNF
  _∨_ : FormulaNNF -> FormulaNNF -> FormulaNNF
  _::_ : RelSym -> List Term -> FormulaNNF
  _¬::_ : RelSym -> List Term -> FormulaNNF
  ∀' : VarSym -> FormulaNNF -> FormulaNNF
  ∃' : VarSym -> FormulaNNF -> FormulaNNF


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
nnf (∀' v x) = ∀' v (nnf x)
nnf (∃' v x) = ∃' v (nnf x)
nnf (¬ (x ∧ y)) = (nnf (¬ x)) ∨ (nnf (¬ y))
nnf (¬ (x ∨ y)) = (nnf (¬ x)) ∧ (nnf (¬ y))
nnf (¬ (¬ x)) = nnf x
nnf (¬ (x :: y)) = x ¬:: y
nnf (¬ (∀' v x)) = ∃' v (nnf (¬ x))
nnf (¬ (∃' v x)) = ∀' v (nnf (¬ x))

subst-term : Term -> VarSym -> Term -> Term
subst-term-map : List Term -> VarSym -> Term -> List Term
subst-term-map [] s t = []
subst-term-map (a :: l) s t = subst-term a s t :: subst-term-map l s t

subst-term (var (:VarSym x)) (:VarSym s) t with primStringEquality x s
... | true = t
... | false = var (:VarSym x)
subst-term (func fname l) s t = (func fname (subst-term-map l s t))


subst : FormulaNNF -> VarSym -> Term -> FormulaNNF
subst (f ∧ f₁) s t = subst f s t ∧ subst f₁ s t
subst (f ∨ f₁) s t = subst f s t ∨ subst f₁ s t
subst (P :: l) s t = P :: map (λ x -> subst-term x s t) l
subst (P ¬:: l) s t = P ¬:: map (λ x -> subst-term x s t) l
subst (∀' x f) s t = (∀' x (subst f s t)) -- TODO naming collisions
subst (∃' x f) s t = (∃' x (subst f s t)) -- TODO naming collisions

vartofn : VarSym -> FnSym
vartofn (:VarSym x) = :FnSym x -- TODO may have naming collisions


qc : FormulaNNF -> Nat
qc (x ∧ x₁) = qc x + qc x₁
qc (x ∨ x₁) = qc x + qc x₁
qc (x :: x₁) = zero
qc (x ¬:: x₁) = zero
qc (∀' x x₁) = succ (qc x₁)
qc (∃' x x₁) = succ (qc x₁)

subst-qc-invar : (f : FormulaNNF) -> (v : VarSym) -> (t : Term) -> qc (subst f v t) == qc f
subst-qc-invar (f ∧ f₁) v t = cong2 _+_ {qc (subst f v t)} {qc f} {qc (subst f₁ v t)} {qc f₁} (subst-qc-invar f v t) (subst-qc-invar f₁ v t)
subst-qc-invar (f ∨ f₁) v t = cong2 _+_ {qc (subst f v t)} {qc f} {qc (subst f₁ v t)} {qc f₁} (subst-qc-invar f v t) (subst-qc-invar f₁ v t)
subst-qc-invar (x :: x₁) v t = refl
subst-qc-invar (x ¬:: x₁) v t = refl
subst-qc-invar (∀' x f) v t = cong succ (subst-qc-invar f v t)
subst-qc-invar (∃' x f) v t = cong succ (subst-qc-invar f v t)

skolemize-impl : List VarSym -> (f : FormulaNNF) -> (c : Nat) -> qc f ≤ c -> FormulaSkol
skolemize-impl l (x ∧ y) c p = skolemize-impl l x c (trans {qc x} {qc (x ∧ y)} {c} add≤ p) ∧ skolemize-impl l y c (trans {qc y} {qc (x ∧ y)} {c} add≤2 p)
skolemize-impl l (x ∨ y) c p = skolemize-impl l x c (trans {qc x} {qc (x ∧ y)} {c} add≤ p) ∧ skolemize-impl l y c (trans {qc y} {qc (x ∧ y)} {c} add≤2 p)
skolemize-impl l (x :: y) _ _ = η (Pos (x :: y))
skolemize-impl l (x ¬:: y) _ _ = η (Neg (x :: y))
skolemize-impl l (∀' v y) (succ c) p = skolemize-impl (v :: l) y c (cong-pred p)
skolemize-impl l (∃' v y) (succ c) p = let t = (func (vartofn v) (map var l))
                                           q = (subst-qc-invar y v t)
                                       in skolemize-impl l (subst y v t) c (trans (=→≤ q) (cong-pred p))


skolemize : FormulaNNF -> FormulaSkol
skolemize f = skolemize-impl [] f (qc f) (refl (qc f))

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
