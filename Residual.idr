module Residual

import Data.Fin
import Control.WellFounded

%default total

public export
data Residual : (n : Nat) -> (k : Nat) -> Type where
  MkResidual : (r : Fin n) -> (c : Nat) -> Residual n (c * n + (finToNat r))

public export
minusHelper : (k, n : Nat) -> Either (d : Nat ** k = n + d) (d : Fin n ** k = finToNat d)
minusHelper k 0 = Left (k ** Refl)
minusHelper 0 (S n) = Right (FZ ** Refl)
minusHelper (S k) (S n) with (minusHelper k n)
  minusHelper (S k) (S n) | (Left (d ** prf)) = Left (d ** cong S prf)
  minusHelper (S k) (S n) | (Right (d ** prf)) = Right (FS d ** cong S prf)

public export
plusEqToLTE : (n, d, k : Nat) -> k = n + d -> LTE d k
plusEqToLTE n 0 k prf = LTEZero
plusEqToLTE n (S j) 0 prf = void $ SIsNotZ $ sym $ trans prf (sym $ plusSuccRightSucc n j)
plusEqToLTE n (S j) (S k) prf = LTESucc $ plusEqToLTE n j k (injective (trans prf (sym $ plusSuccRightSucc n j)))

public export
cycleResidual : (n, k : Nat) -> Residual n k -> Residual n (n + k)
cycleResidual n ((c * n) + finToNat r) (MkResidual r c) =
  rewrite plusAssociative n (c * n) (finToNat r) in
          MkResidual r (S c)

public export
getResidual : (n, k : Nat) -> {auto 0 pos : NonZero n} -> Residual n k
getResidual Z k {pos = ItIsSucc} impossible
getResidual (S n) k = getResidual' k (wellFounded k)
  where
    getResidual' : (k : Nat) -> (0 acc : Accessible LT k) -> Residual (S n) k
    getResidual' k acc with (minusHelper k (S n))
      getResidual' k (Access acc) | (Left (d ** prf)) =
        let resid = getResidual' d (acc d (plusEqToLTE n (S d) k (trans prf (plusSuccRightSucc n d)))) in
            rewrite prf in cycleResidual (S n) d resid
      getResidual' k acc | (Right (d ** prf)) = rewrite prf in MkResidual d 0
