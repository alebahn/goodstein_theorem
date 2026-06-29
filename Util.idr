import Data.Nat

%default total

lteNotEqToLT : (left, right : Nat) -> left `LTE` right -> Not (left = right) -> left `LT` right
lteNotEqToLT Z Z LTEZero neq = void (neq Refl)
lteNotEqToLT Z (S right) LTEZero neq = LTESucc LTEZero
lteNotEqToLT (S left) Z LTEZero neq impossible
lteNotEqToLT (S left) (S right) (LTESucc lte) neq =
  LTESucc (lteNotEqToLT left right lte (\eq => neq (cong S eq)))

[antireflLT] Uninhabited (Data.Nat.LT x x) where
  uninhabited (LTESucc x) = uninhabited x

sameArgIsSameLT : (x, y : Data.Nat.LTE a b) -> x === y
sameArgIsSameLT LTEZero LTEZero = Refl
sameArgIsSameLT (LTESucc x) (LTESucc y) = cong LTESucc (sameArgIsSameLT x y)
