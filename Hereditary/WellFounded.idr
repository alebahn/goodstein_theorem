import Control.WellFounded
import Data.Nat
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Properties
import Syntax.PreorderReasoning.Generic
import Hereditary

%default total

powerPositiveBasePositive : (b, e : Nat) -> power (S b) e `GT` 0
powerPositiveBasePositive b 0 = LTESucc LTEZero
powerPositiveBasePositive b (S e) = transitive (powerPositiveBasePositive b e) (lteAddRight (power (S b) e))

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

powerLteMonotone : (n, e1, e2 : Nat) ->
                   LTE e1 e2 ->
                   LTE (power (S (S n)) e1) (power (S (S n)) e2)
powerLteMonotone n Z e2 LTEZero = powerPositiveBasePositive (S n) e2
powerLteMonotone n (S e1) (S e2) (LTESucc lte) =
  multLteMonotoneRight (S (S n))
                       (power (S (S n)) e1)
                       (power (S (S n)) e2)
                       (powerLteMonotone n e1 e2 lte)

mutual
  hereditarySmallerThanPower : {n : Nat} ->
                               (h, g : Hereditary (S (S n))) ->
                               SmallerOrderH h g ->
                               LT (size h) (power (S (S n)) (size g))
  hereditarySmallerThanPower HZ g HZSSmaller =
    powerPositiveBasePositive (S n) (size g)
  hereditarySmallerThanPower (HA c e r so) g (HASmaller hlt) =
    let p : Nat
        p = power (S (S n)) (size e) in
    CalcWith {leq = LTE} $
      |~ S (size (HA c e r so))
      ~~ S ((S (finToNat c)) * p + size r) ...(Refl)
      ~~ (S (finToNat c)) * p + S (size r)
          ...(plusSuccRightSucc ((S (finToNat c)) * p) (size r))
      <~ (S (finToNat c)) * p + p
          ...(plusLteMonotoneLeft ((S (finToNat c)) * p)
                                  (S (size r))
                                  p
                                  (hereditarySmallerThanPower r e so))
      ~~ p + (S (finToNat c)) * p
          ...(plusCommutative ((S (finToNat c)) * p) p)
      ~~ (S (S (finToNat c))) * p ...(Refl)
      <~ (S (S n)) * p
          ...(multLteMonotoneLeft (S (S (finToNat c)))
                                  (S (S n))
                                  p
                                  (LTESucc (elemSmallerThanBound c)))
      ~~ power (S (S n)) (S (size e)) ...(Refl)
      <~ power (S (S n)) (size g)
          ...(powerLteMonotone n (S (size e)) (size g) (hltToSizeSmaller e g hlt))

  hltToSizeSmaller : {n : Nat} -> (h, g : Hereditary (S (S n))) -> HLT h g -> LT (size h) (size g)
  hltToSizeSmaller HZ (HA coef e rest so) HZLTHA =
    transitive (powerPositiveBasePositive (S n) (hereditaryToNat e))
               (rewrite sym $ plusAssociative (power (S (S n)) (hereditaryToNat e)) (mult (finToNat coef) (power (S (S n)) (hereditaryToNat e))) (hereditaryToNat rest) in
                        lteAddRight (power (S (S n)) (hereditaryToNat e)))
  hltToSizeSmaller (HA c1 e r1 so1) (HA c2 e r2 so2) (SameOrderHLT lt) =
    let p : Nat
        p = power (S (S n)) (size e) in
    CalcWith {leq = LTE} $
      |~ S (size (HA c1 e r1 so1))
      ~~ S ((S (finToNat c1)) * p + size r1) ...(Refl)
      ~~ (S (finToNat c1)) * p + S (size r1)
          ...(plusSuccRightSucc ((S (finToNat c1)) * p) (size r1))
      <~ (S (finToNat c1)) * p + p
          ...(plusLteMonotoneLeft ((S (finToNat c1)) * p)
                                  (S (size r1))
                                  p
                                  (hereditarySmallerThanPower r1 e so1))
      ~~ p + (S (finToNat c1)) * p
          ...(plusCommutative ((S (finToNat c1)) * p) p)
      ~~ (S (S (finToNat c1))) * p ...(Refl)
      <~ (S (finToNat c2)) * p
          ...(multLteMonotoneLeft (S (S (finToNat c1)))
                                  (S (finToNat c2))
                                  p
                                  (LTESucc lt))
      <~ (S (finToNat c2)) * p + size r2
          ...(lteAddRight ((S (finToNat c2)) * p))
      ~~ size (HA c2 e r2 so2) ...(Refl)
  hltToSizeSmaller (HA c1 e1 r1 so1) (HA c2 e2 r2 so2) (SmallerOrderHLT hlt) =
    let p1 : Nat
        p1 = power (S (S n)) (size e1)
        p2 : Nat
        p2 = power (S (S n)) (size e2) in
    CalcWith {leq = LTE} $
      |~ S (size (HA c1 e1 r1 so1))
      ~~ S ((S (finToNat c1)) * p1 + size r1) ...(Refl)
      ~~ (S (finToNat c1)) * p1 + S (size r1)
          ...(plusSuccRightSucc ((S (finToNat c1)) * p1) (size r1))
      <~ (S (finToNat c1)) * p1 + p1
          ...(plusLteMonotoneLeft ((S (finToNat c1)) * p1)
                                  (S (size r1))
                                  p1
                                  (hereditarySmallerThanPower r1 e1 so1))
      ~~ p1 + (S (finToNat c1)) * p1
          ...(plusCommutative ((S (finToNat c1)) * p1) p1)
      ~~ (S (S (finToNat c1))) * p1 ...(Refl)
      <~ (S (S n)) * p1
          ...(multLteMonotoneLeft (S (S (finToNat c1)))
                                  (S (S n))
                                  p1
                                  (LTESucc (elemSmallerThanBound c1)))
      ~~ power (S (S n)) (S (size e1)) ...(Refl)
      <~ p2
          ...(powerLteMonotone n (S (size e1)) (size e2) (hltToSizeSmaller e1 e2 hlt))
      <~ (S (finToNat c2)) * p2
          ...(lteAddRight p2)
      <~ (S (finToNat c2)) * p2 + size r2
          ...(lteAddRight ((S (finToNat c2)) * p2))
      ~~ size (HA c2 e2 r2 so2) ...(Refl)
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
