data _==_ {A : Set} : (a b : A) -> Set where
  refl : (a : A) -> a == a
infixl 30 _==_ 

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _+_ (A B : Set) : Set where
  left : A -> A + B
  right : B -> A + B
infix 40 _+_

data bool : Set where
  true : bool
  false : bool

$_ : bool -> Set
$_ x = x == true
infix 35 $_

record Ord (A : Set) : Set where
  field _≤_ : A -> A -> bool
  field refl-≤ : (a : A) -> $ a ≤ a
  field trans-≤ : (a b c : A) -> $ a ≤ b -> $ b ≤ c -> $ a ≤ c
  field connex-≤ : (a b : A) -> ($ a ≤ b) + ($ b ≤ a)
  field antisym-≤ : (a b : A) -> $ a ≤ b -> $ b ≤ a -> a == b
  infix 50 _≤_

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

_≤Nat_ : (x y : Nat) -> bool
_≤Nat_ zero y = true
_≤Nat_ (succ x) zero = false
_≤Nat_ (succ x) (succ y) = x ≤Nat y
infix 50 _≤Nat_

refl-≤Nat : (x : Nat) -> $ x ≤Nat x
refl-≤Nat zero = refl true
refl-≤Nat (succ x) = refl-≤Nat x

trans-≤Nat : (a b c : Nat) -> $ a ≤Nat b -> $ b ≤Nat c -> $ a ≤Nat c
trans-≤Nat zero b c p q = refl true
trans-≤Nat (succ a) (succ b) (succ c) p q = trans-≤Nat a b c p q

connex-≤Nat : (a b : Nat) -> ($ a ≤Nat b) + ($ b ≤Nat a)
connex-≤Nat zero b = left (refl true)
connex-≤Nat (succ a) zero = right (refl true)
connex-≤Nat (succ a) (succ b) = connex-≤Nat a b

cong : {A B : Set} -> (f : A -> B) -> {a₁ a₂ : A} -> a₁ == a₂ -> f a₁ == f a₂
cong {A} {B} f {a₁} {a₂} (refl a₁) = refl (f a₁)

antisym-≤Nat : (a b : Nat) -> $ a ≤Nat b -> $ b ≤Nat a -> a == b
antisym-≤Nat zero zero p q = refl zero
antisym-≤Nat (succ a) (succ b) p q = let p2 = antisym-≤Nat a b p q
                                     in cong succ p2

OrdNat : Ord Nat
Ord._≤_ OrdNat = _≤Nat_
Ord.refl-≤ OrdNat = refl-≤Nat
Ord.trans-≤ OrdNat = trans-≤Nat
Ord.connex-≤ OrdNat = connex-≤Nat
Ord.antisym-≤ OrdNat = antisym-≤Nat
