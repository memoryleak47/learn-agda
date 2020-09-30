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

data eq : {A : Set} -> A -> A -> Set where
  refl : {A : Set} -> {a : A} -> eq a a
_==_ = eq

infixl 50 _+_
infixl 30 _==_

-- eq a a -> eq f(a) f(a)
cong : {A B : Set} -> {a1 : A} -> {a2 : A} -> (f : A -> B) -> eq a1 a2 -> eq (f a1) (f a2)
cong f refl = refl

foo : ∀ x -> x + (succ (succ zero)) == (succ (succ x))
foo zero = refl
foo (succ x) = cong succ (foo x)
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


max2 : Nat -> Nat -> Nat
max2 zero y = y
max2 x zero = x
max2 (succ x) (succ y) = succ (max2 x y)

max : List Nat -> Nat
max [] = zero
max (a :: x) = max2 a (max x)


data _≤_ : (x y : Nat) -> Set where
  refl : (x : Nat) -> x ≤ x
  succ : (x y : Nat) -> x ≤ y -> x ≤ (succ y)

trans : {x y z : Nat} -> x ≤ y -> y ≤ z -> x ≤ z
trans {x} {y} {.y} p (refl .y) = p
trans {x} {y} {.(succ y₁)} p (succ .y y₁ q) = succ _ _ (trans p q)

_∙_ : {A : Set} -> {x y z : A} -> x == y -> y == z -> x == z
refl ∙ refl = refl

zero≤∀ : (x : Nat) -> zero ≤ x
zero≤∀ zero = refl zero
zero≤∀ (succ x) = succ zero x (zero≤∀ x)

cong2 : {A B C : Set} -> (f : A -> B -> C) -> {a₁ a₂ : A} -> {b₁ b₂ : B} -> a₁ == a₂ -> b₁ == b₂ -> f a₁ b₁ == f a₂ b₂
cong2 f refl refl = refl

cong-succ : {a b : Nat} -> a ≤ b -> succ a ≤ succ b
cong-succ {a} {.a} (refl .a) = refl (succ a)
cong-succ {a} {.(succ y)} (succ .a y p) = succ _ _ (cong-succ p)

cong-pred : {a b : Nat} -> succ a ≤ succ b -> a ≤ b
cong-pred (refl .(succ _)) = refl _
cong-pred {a} {b} (succ .(succ _) _ p) = trans {a} {succ a} {b} (succ _ _ (refl a)) p

add≤ : {x y : Nat} -> x ≤ x + y
add≤ {zero} {y} = zero≤∀ y
add≤ {succ x} {y} = cong-succ (add≤ {x} {y})

zero-neutral : {x : Nat} -> x == x + zero
zero-neutral {zero} = refl
zero-neutral {succ x} = cong succ zero-neutral

! : {A : Set} -> {x y : A} -> x == y -> y == x
! refl = refl

add-succ-r : {x y : Nat} -> x + succ y == succ (x + y)
add-succ-r {zero} {y} = refl
add-succ-r {succ x} {y} = let p = add-succ-r {x} {y} in cong succ p

=→≤ : {a b : Nat} -> a == b -> a ≤ b
=→≤ refl = refl _

addsym : {x y : Nat} -> x + y == y + x
addsym {zero} {zero} = refl
addsym {zero} {succ y} = zero-neutral
addsym {succ x} {zero} = ! zero-neutral
addsym {succ x} {succ y} = let p = addsym {succ x} {y}
                               q = cong {Nat} {Nat} succ p
                               w : succ x + succ y == succ (succ x + y)
                               w = cong {Nat} {Nat} succ add-succ-r
                           in w ∙ q

add≤2 : {x y : Nat} -> x ≤ y + x
add≤2 {x} {y} = trans (add≤ {x} {y}) (=→≤ (addsym {x} {y}))
