open import base

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
