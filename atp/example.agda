open import logic
open import base

v1 : Term
v1 = var (:VarSym "v1")

v2 : Term
v2 = var (:VarSym "v2")

P : RelSym
P = :RelSym "P"

f : FnSym
f = :FnSym "f"

a : Formula
a = ¬(P :: (v1 :: []) ∧ P :: (v1 :: v2 :: []))

a2 : Formula
a2 = ¬((:VarSym "v1") ⋁ ((:VarSym "v2") ⋀ (¬(P :: (v1 :: v2 :: [])))))

res : ClauseSet
res = clauselize ( skolemize (nnf a2))




