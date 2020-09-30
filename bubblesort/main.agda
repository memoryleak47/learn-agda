open import nat
open import base

data mini {A : Set} {O : Ord A} : (m : A) -> List A -> Set where
  [] : (m : A) -> mini m []
  next : (m a : A) -> (l : List A) -> mini {A} {O} m l -> $ Ord._≤_ O m a -> mini m (a :: l)

data sorted {A : Set} {O : Ord A} : List A -> Set where
  [] : sorted []
  next : (l : List A) -> (m : A) -> mini {O = O} m l -> sorted (m :: l)

data Fin : (n : Nat) -> Set where
  zero : {n : Nat} -> Fin (succ n)
  succ : {n : Nat} -> (a : Fin n) -> Fin (succ n)

data Vector (A : Set) : (n : Nat) -> Set where
  [] : Vector A zero
  _::_ : (a : A) -> {n : Nat} -> Vector A n -> Vector A (succ n)

list→vec : {A : Set} -> (l : List A) -> Vector A (len l)
list→vec [] = []
list→vec (x :: l) = (x :: (list→vec l))

idx : {A : Set} -> {n : Nat} -> Vector A n -> Fin n -> A
idx [] ()
idx (a :: v) (zero) = a
idx (a :: v) (succ i) = idx v i

record ∑_ {L : Set} (R : L -> Set) : Set where
  field fst : L
  field snd : R fst

record is-bij {A B : Set} (f : A -> B) : Set where
  field is-inj : (a₁ : A) -> (a₂ : A) -> f a₁ == f a₂ -> a₁ == a₂
  field is-surj : (b : B) -> ∑ λ a -> f a == b

record isomorph-vec {A : Set} {n : Nat} (v₁ v₂ : Vector A n) : Set where
  field iso : (Fin n -> Fin n)
  field cond : (i : Fin n) -> idx v₁ i == idx v₂ (iso i)
  field iso-is-bij : is-bij iso

transport : {A B : Set} -> A == B -> A -> B
transport (refl _) a = a

record isomorph-list {A : Set} (l₁ : List A) (l₂ : List A) : Set where
  v₁ = list→vec l₁
  v₂ = list→vec l₂
  field cond : (len l₁ == len l₂)
  v₁' = transport (cong (Vector A) cond) v₁
  field vec-iso : isomorph-vec v₁' v₂

is-sorting-properly : {A : Set} -> {O : Ord A} -> (List A -> List A) -> Set
is-sorting-properly {A} {O} alg = ∀ l -> ∑ (λ l₂ -> (∑ (λ (_ : isomorph-list l l₂) -> sorted {O = O} l₂) ))
