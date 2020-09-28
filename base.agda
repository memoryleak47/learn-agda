module base where

open import Agda.Builtin.Bool public
open import Agda.Builtin.String public


data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

add : Nat -> Nat -> Nat
add zero x = x
add (succ x) y = succ (add x y)
_+_ = add

data eq : (A : Set) -> A -> A -> Set where
  refl : (A : Set) -> (a : A) -> eq A a a
_==_ = eq Nat

infixl 50 _+_
infixl 30 _==_

-- eq a a -> eq f(a) f(a)
cong : (A B : Set) -> (a1 : A) -> (a2 : A) -> (eq A a1 a2) -> (f : A -> B) -> (eq B (f a1) (f a2))
cong A B a1 a2 (refl x y) f = refl B (f _)

foo : ∀ x -> x + (succ (succ zero)) == (succ (succ x))
foo zero = refl _ _
foo (succ x) = cong Nat Nat (x + (succ (succ zero))) (succ (succ x)) (foo x) succ
-- x+2 = x+2 -> succ(x)+2 = succ(x)+2
-- (eq Nat (add x (succ (succ zero))) (plustwo x))
-- (eq Nat (add (succ x) (succ (succ zero))) (plustwo (succ x)))

data List (A : Set) : Set where
  [] : List A
  _::_ : (a : A) -> List A -> List A

infixr 40 _::_

map : {A B : Set} -> (f : A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)

union : {A : Set} -> List A -> List A -> List A
union [] b = b
union (x :: xs) b = x :: union xs b
_∪_ = union
infixl 50 _∪_
