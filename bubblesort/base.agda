open import Agda.Primitive public

variable ℓ : Level
variable ℓ' : Level
data _==_ {A : Set ℓ} : (a b : A) -> Set where
  refl : (a : A) -> a == a
infixl 30 _==_ 

cong : {A : Set ℓ} -> {B : Set ℓ'} -> (f : A -> B) -> {a₁ a₂ : A} -> a₁ == a₂ -> f a₁ == f a₂
cong {A} {B} f {a₁} {a₂} (refl a₁) = refl (f a₁)


data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _+_ (A B : Set) : Set where
  left : A -> A + B
  right : B -> A + B
infix 40 _+_

data _&_ (A B : Set) : Set where
  both : A -> B -> A & B
infix 40 _&_

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

len : {A : Set} -> List A -> Nat
len [] = zero
len (x :: xs) = succ (len xs)

