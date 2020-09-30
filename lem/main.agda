data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

¬_ : Set -> Set
¬_ A = A -> ⊥
infix 50 ¬_ 

D¬ = {A : Set} -> ¬ ¬ A -> A

foo2 : {A : Set} -> A -> ¬ ¬ A
foo2 {A} p q = q p

data _+_ (A B : Set) : Set where
  left : A -> A + B
  right : B -> A + B

lemma : (A B : Set) -> A + B -> B + A
lemma A B (left x) = right x
lemma A B (right x) = left x

LEM = (A : Set) -> A + ¬ A

-- D¬→LEM : D¬ -> LEM
-- D¬→LEM p A = let q = p {A} in {!!}

⊥-elim : (A : Set) -> ⊥ -> A
⊥-elim A ()

LEM→D¬ : LEM -> D¬
LEM→D¬ p {A} q with p A
... | left x = x
... | right x = ⊥-elim A (q x)
