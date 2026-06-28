import Control.WellFounded
import Data.Nat
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Properties
import Syntax.PreorderReasoning.Generic
import Hereditary

%default total

{n : Nat} -> Sized (Hereditary n) where
  size h = hereditaryToNat {n} h

biggerExponentBigger : (n : Nat) -> (e1, e2 : Nat) -> (c : Fin (S n)) ->
                       LT e1 e2 ->
                       LT ((S (finToNat c)) * power (S (S n)) e1) (power (S (S n)) e2)
biggerExponentBigger n e1 e2 c lt with (view lt)
  biggerExponentBigger n 0 (S e2) c (LTESucc LTEZero) | LTZero =
    rewrite multOneRightNeutral (finToNat c) in
            transitive (LTESucc (elemSmallerThanBound c))
                       (plusLteMonotone (powerPositiveBasePositive (S n) e2)
                       (plusLteMonotone (powerPositiveBasePositive (S n) e2)
                       (rewrite sym $ multOneRightNeutral n in
                                (multLteMonotoneRight n 1 (power (S (S n)) e2) (powerPositiveBasePositive (S n) e2)))))
  biggerExponentBigger n (S e1) (S e2) c (LTESucc lt) | (LTSucc lt) = CalcWith {leq = LTE} $
    |~ S (S (finToNat c) * power (S (S n)) (S e1))
    ~~ S (S (finToNat c) * (S (S n) * power (S (S n)) e1)) ...(Refl)
    ~~ S (S (finToNat c) * S (S n) * power (S (S n)) e1) ...(cong S $ multAssociative (S (finToNat c)) (S (S n)) (power (S (S n)) e1))
    ~~ S (S (S n) * S (finToNat c) * power (S (S n)) e1) ...(cong (S . (* power (S (S n)) e1)) $ multCommutative (S (finToNat c)) (S (S n)))
    ~~ S (S (S n) * (S (finToNat c) * power (S (S n)) e1)) ...(cong S $ (sym $ multAssociative (S (S n)) (S (finToNat c)) (power (S (S n)) e1)))
    <~ S (S (S n) * (S (finToNat c) * power (S (S n)) e1)) + S n ...(lteAddRight (S (S (S n) * (S (finToNat c) * power (S (S n)) e1))))
    ~~ S (S n) + S (S n) * (S (finToNat c) * power (S (S n)) e1) ...(cong S $ plusCommutative (S (S n) * (S (finToNat c) * power (S (S n)) e1)) (S n))
    ~~ S (S n) * 1 + S (S n) * (S (finToNat c) * power (S (S n)) e1) ...(cong (+ S (S n) * (S (finToNat c) * power (S (S n)) e1)) (sym $ multOneRightNeutral (S (S n))))
    ~~ S (S n) * (1 + (S (finToNat c) * power (S (S n)) e1)) ...(sym $ multDistributesOverPlusRight (S (S n)) 1 (S (finToNat c) * power (S (S n)) e1))
    ~~ S (S n) * (S (S (finToNat c) * power (S (S n)) e1)) ...(Refl)
    <~ (S (S n) * power (S (S n)) e2) ...(multLteMonotoneRight (S (S n)) (S (S (finToNat c) * power (S (S n)) e1)) (power (S (S n)) e2) (biggerExponentBigger n e1 e2 c lt))
    ~~ power (S (S n)) (S e2) ...(Refl)

hltToSizeSmaller : {n : Nat} -> (h, g : Hereditary (S (S n))) -> HLT h g -> LT (size h) (size g)
hltToSizeSmaller HZ (HA coef e rest so) HZLTHA =
  transitive (powerPositiveBasePositive (S n) (hereditaryToNat e))
             (rewrite sym $ plusAssociative (power (S (S n)) (hereditaryToNat e)) (mult (finToNat coef) (power (S (S n)) (hereditaryToNat e))) (hereditaryToNat rest) in
                      lteAddRight (power (S (S n)) (hereditaryToNat e)))
hltToSizeSmaller (HA c1 e r1 so1) (HA c2 e r2 so2) (SameOrderHLT lt) = ?hltToSizeSmaller_rhs_1
hltToSizeSmaller (HA c1 e1 r1 so1) (HA c2 e2 r2 so2) (SmallerOrderHLT hlt) = ?hltToSizeSmaller_rhs_2
hltToSizeSmaller (HA c e r1 so1) (HA c e r2 so2) (SmallerTailHLT hlt) =
  rewrite plusSuccRightSucc ((S (finToNat c)) * power (S (S n)) (hereditaryToNat e)) (hereditaryToNat r1) in
          plusLteMonotoneLeft ((S (finToNat c)) * power (S (S n)) (hereditaryToNat e))
                              (S (hereditaryToNat r1))
                              (hereditaryToNat r2)
                              (hltToSizeSmaller r1 r2 hlt)

{n : Nat} -> WellFounded (Hereditary (S (S n))) HLT where
  wellFounded h = Access $ acc (sizeAccessible h)
  where
    acc : (0 sa : SizeAccessible j) -> (k : Hereditary (S (S n))) -> HLT k j -> Accessible HLT k
    acc (Access rec) k hlt = Access $ acc (rec k (hltToSizeSmaller k j hlt))
