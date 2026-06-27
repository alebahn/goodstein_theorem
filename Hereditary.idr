import Control.Relation
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Properties
import Control.WellFounded
import Syntax.PreorderReasoning.Generic
import Base

%default total

mutual
  data Hereditary : (n: Nat) -> Type where
    HZ : Hereditary (S n)
    HA : (coef : Fin n) -> (exp : Hereditary (S n)) -> (rest : Hereditary (S n)) -> (0 smaller : SmallerOrderH rest exp) -> Hereditary (S n)

  data SmallerOrderH : Hereditary n -> Hereditary n -> Type where
    HZSSmaller : SmallerOrderH HZ o
    HASmaller : HLT h o -> SmallerOrderH (HA c h t sml) o

  data HLT : Hereditary n -> Hereditary n -> Type where
    HZLTHA : HLT HZ (HA coef e rest so)
    SameOrderHLT : (lt : LT (finToNat c1) (finToNat c2)) -> HLT (HA c1 e r1 so1) (HA c2 e r2 so2)
    SmallerOrderHLT : (hlt : HLT e1 e2) -> HLT (HA c1 e1 r1 so1) (HA c2 e2 r2 so2)
    SmallerTailHLT : (hlt : HLT r1 r2) -> HLT (HA c e r1 so1) (HA c e r2 so2)

private
[antireflLT] Uninhabited (Data.Nat.LT x x) where
  uninhabited (LTESucc x) = uninhabited x

Uninhabited (HLT x x) where
  uninhabited (SameOrderHLT y) = uninhabited @{antireflLT} y
  uninhabited (SmallerOrderHLT y) = uninhabited y
  uninhabited (SmallerTailHLT y) = uninhabited y

nothingHLTHZ : Not (HLT x HZ)
nothingHLTHZ HZLTHA impossible
nothingHLTHZ (SameOrderHLT lt) impossible
nothingHLTHZ (SmallerOrderHLT hlt) impossible
nothingHLTHZ (SmallerTailHLT hlt) impossible

private
sameArgIsSameLT : (x, y : Data.Nat.LTE a b) -> x === y
sameArgIsSameLT LTEZero LTEZero = Refl
sameArgIsSameLT (LTESucc x) (LTESucc y) = cong LTESucc (sameArgIsSameLT x y)

sameArgIsSameHLT : (x, y : HLT a b) -> x === y
sameArgIsSameHLT HZLTHA HZLTHA = Refl
sameArgIsSameHLT (SameOrderHLT x) (SameOrderHLT y) = cong SameOrderHLT (sameArgIsSameLT x y)
sameArgIsSameHLT (SameOrderHLT x) (SmallerOrderHLT y) = absurd y
sameArgIsSameHLT (SameOrderHLT x) (SmallerTailHLT y) = absurd @{antireflLT} x
sameArgIsSameHLT (SmallerOrderHLT x) (SameOrderHLT y) = absurd x
sameArgIsSameHLT (SmallerOrderHLT x) (SmallerOrderHLT y) = cong SmallerOrderHLT (sameArgIsSameHLT x y)
sameArgIsSameHLT (SmallerOrderHLT x) (SmallerTailHLT y) = absurd x
sameArgIsSameHLT (SmallerTailHLT x) (SameOrderHLT y) = absurd @{antireflLT} y
sameArgIsSameHLT (SmallerTailHLT x) (SmallerOrderHLT y) = absurd y
sameArgIsSameHLT (SmallerTailHLT x) (SmallerTailHLT y) = cong SmallerTailHLT (sameArgIsSameHLT x y)

sameArgIsSameOrderH : (x, y : SmallerOrderH h o) -> x === y
sameArgIsSameOrderH HZSSmaller HZSSmaller = Refl
sameArgIsSameOrderH (HASmaller x) (HASmaller y) = cong HASmaller (sameArgIsSameHLT x y)

sameArgIsSameHA : (x : Fin (S base)) -> hea === heb -> hta === htb -> HA x hea hta soa === HA x heb htb sob
sameArgIsSameHA x Refl Refl = rewrite sameArgIsSameOrderH soa sob in Refl

Transitive (Hereditary n) HLT where
  transitive HZLTHA HZLTHA impossible
  transitive (SameOrderHLT w) HZLTHA impossible
  transitive (SmallerOrderHLT w) HZLTHA impossible
  transitive (SmallerTailHLT w) HZLTHA impossible
  transitive HZLTHA (SameOrderHLT w) = HZLTHA
  transitive HZLTHA (SmallerOrderHLT w) = HZLTHA
  transitive HZLTHA (SmallerTailHLT w) = HZLTHA
  transitive (SameOrderHLT w) (SameOrderHLT v) = SameOrderHLT (transitive w (lteSuccLeft v))
  transitive (SameOrderHLT w) (SmallerOrderHLT v) = SmallerOrderHLT v
  transitive (SameOrderHLT w) (SmallerTailHLT v) = SameOrderHLT w
  transitive (SmallerOrderHLT w) (SameOrderHLT v) = SmallerOrderHLT w
  transitive (SmallerOrderHLT w) (SmallerOrderHLT v) = SmallerOrderHLT (transitive w v)
  transitive (SmallerOrderHLT w) (SmallerTailHLT v) = SmallerOrderHLT w
  transitive (SmallerTailHLT w) (SameOrderHLT v) = SameOrderHLT v
  transitive (SmallerTailHLT w) (SmallerOrderHLT v) = SmallerOrderHLT v
  transitive (SmallerTailHLT w) (SmallerTailHLT v) = SmallerTailHLT (transitive w v)

baseToHereditaryAcc : {base : Nat} -> (xs : List (Fin (S (S base)))) ->
  (0 acc : SizeAccessible xs) -> Hereditary (S (S base))

smallerOrderTransSmaller : {h, left, right : Hereditary n} ->
                           SmallerOrderH h left -> HLT left right ->
                           SmallerOrderH h right
smallerOrderTransSmaller HZSSmaller _ = HZSSmaller
smallerOrderTransSmaller (HASmaller lta) ltb = HASmaller (transitive lta ltb)

baseSmallerHereditarySmaller : {base : Nat} ->
                               (as, bs : List (Fin (S (S base)))) -> BaseSmaller as bs ->
                               (0 aAcc : SizeAccessible as) ->
                               (0 bAcc : SizeAccessible bs) ->
                               HLT (baseToHereditaryAcc as aAcc) (baseToHereditaryAcc bs bAcc)

baseToHereditaryOrder : {base : Nat} ->
  (xs : List (Fin (S (S base)))) ->
  (0 tailAcc : SizeAccessible xs) ->
  (0 expAcc : SizeAccessible (natToBase base (length xs))) ->
  SmallerOrderH
    (baseToHereditaryAcc xs tailAcc)
    (baseToHereditaryAcc (natToBase base (length xs)) expAcc)

baseToHereditaryAcc [] acc = HZ
baseToHereditaryAcc (FZ :: xs) (Access rec) =
  baseToHereditaryAcc xs (rec xs reflexive)
baseToHereditaryAcc ((FS x) :: xs) (Access rec) =
  let (expDigits ** smallerPrf ** orderPrf) :
        (expDigits : List (Fin (S (S base))) **
          smallerPrf : LTE (S (length expDigits)) (S (length xs)) **
          SmallerOrderH
            (baseToHereditaryAcc xs (rec xs (reflexive {x = S (length xs)})))
            (baseToHereditaryAcc expDigits (rec expDigits smallerPrf)))
      = ( natToBase base (length xs)
        ** natToBaseLengthSmaller base (length xs)
        ** baseToHereditaryOrder
             xs
             (rec xs (reflexive {x = S (length xs)}))
             (rec (natToBase base (length xs)) (natToBaseLengthSmaller base (length xs)))
        ) in
      HA x
        (baseToHereditaryAcc expDigits (rec expDigits smallerPrf))
        (baseToHereditaryAcc xs (rec xs (reflexive {x = S (length xs)})))
        orderPrf

baseToHereditaryAccIrrelevent : {base : Nat} -> (xs : List (Fin (S (S base)))) ->
  (0 acc1 : SizeAccessible xs) -> (0 acc2 : SizeAccessible xs) -> baseToHereditaryAcc xs acc1 === baseToHereditaryAcc xs acc2
baseToHereditaryAccIrrelevent [] acc1 acc2 = Refl {x = HZ}
baseToHereditaryAccIrrelevent (FZ :: xs) (Access rec1) (Access rec2) = baseToHereditaryAccIrrelevent xs (rec1 xs reflexive) (rec2 xs reflexive)
baseToHereditaryAccIrrelevent ((FS x) :: xs) (Access rec1) (Access rec2) =
  sameArgIsSameHA x (baseToHereditaryAccIrrelevent (natToBase base (length xs))
                                                   (rec1 (natToBase base (length xs)) (natToBaseAccLengthSmaller base (length xs) (sizeAccessible (length xs))))
                                                   (rec2 (natToBase base (length xs)) (natToBaseAccLengthSmaller base (length xs) (sizeAccessible (length xs)))))
                    (baseToHereditaryAccIrrelevent xs (rec1 xs (LTESucc reflexive)) (rec2 xs (LTESucc reflexive)))

baseSmallerHereditarySmaller_headSame : {base : Nat} ->
                                        (x : Fin (S (S base))) -> (xs, ys : List (Fin (S (S base)))) ->
                                        (0 aAcc : SizeAccessible (x :: xs)) ->
                                        (0 bAcc : SizeAccessible (x :: ys)) ->
                                        (0 leq : length xs === length ys) ->
                                        (sml : BaseSmaller xs ys) ->
                                        HLT (baseToHereditaryAcc (x :: xs) aAcc) (baseToHereditaryAcc (x :: ys) bAcc)

baseSmallerHereditarySmaller_leftSmaller : {base : Nat} ->
                                           (x, y : Fin (S (S base))) ->
                                           (xs, ys : List (Fin (S (S base)))) ->
                                           (0 aAcc : SizeAccessible (x :: xs)) ->
                                           (0 bAcc : SizeAccessible (y :: ys)) ->
                                           (lt : LT (finToNat x) (finToNat y)) ->
                                           (0 leq : length xs === length ys) ->
                                           HLT (baseToHereditaryAcc (x :: xs) aAcc) (baseToHereditaryAcc (y :: ys) bAcc)

baseSmallerHereditarySmaller_leftShorter : {base : Nat} -> (y : Fin (S base)) ->
                                           (xs, ys : List (Fin (S (S base)))) ->
                                       (0 aAcc : SizeAccessible (xs)) ->
                                       (0 bAcc : SizeAccessible (FS y :: ys)) ->
                                       (llt : length xs `LTE` length ys) ->
                                       HLT (baseToHereditaryAcc xs aAcc) (baseToHereditaryAcc (FS y :: ys) bAcc)
baseSmallerHereditarySmaller_leftShorter y [] ys (Access aRec) (Access bRec) llt = HZLTHA
baseSmallerHereditarySmaller_leftShorter y (FZ :: xs) ys (Access aRec) bAcc llt =
  baseSmallerHereditarySmaller_leftShorter y xs ys (aRec xs reflexive) bAcc (lteSuccLeft llt)
baseSmallerHereditarySmaller_leftShorter y ((FS x) :: xs) ys (Access aRec) (Access bRec) llt =
  SmallerOrderHLT (baseSmallerHereditarySmaller (natToBase base (length xs)) (natToBase base (length ys)) (natSmallerBaseSmaller base (length xs) (length ys) llt) (aRec (natToBase base (length xs)) (natToBaseLengthSmaller base (length xs))) (bRec (natToBase base (length ys)) (natToBaseLengthSmaller base (length ys))))

baseSmallerHereditarySmaller as bs sml aAcc bAcc with (headSmaller as bs sml)
  baseSmallerHereditarySmaller (x :: xs) (x :: ys) sml aAcc bAcc | (HeadSame leq sml') = baseSmallerHereditarySmaller_headSame x xs ys aAcc bAcc leq sml'
  baseSmallerHereditarySmaller (x :: xs) (y :: ys) sml aAcc bAcc | (LeftSmaller x y xs ys lt leq) = baseSmallerHereditarySmaller_leftSmaller x y xs ys aAcc bAcc lt leq
  baseSmallerHereditarySmaller as (FS y :: ys) sml aAcc bAcc | (LeftShorter llt) = baseSmallerHereditarySmaller_leftShorter y as ys aAcc bAcc llt

baseSmallerHereditarySmaller_headSame FZ xs ys (Access aRec) (Access bRec) leq sml =
  baseSmallerHereditarySmaller xs ys sml (aRec xs reflexive) (bRec ys reflexive)
baseSmallerHereditarySmaller_headSame (FS x) xs ys (Access aRec) (Access bRec) leq sml =
    rewrite baseToHereditaryAccIrrelevent (natToBase base (length xs))
              (aRec (natToBase base (length xs))
                (natToBaseAccLengthSmaller base (length xs) (sizeAccessible (length xs))))
              (rewrite leq in
                       (bRec (natToBase base (length ys))
                        (natToBaseAccLengthSmaller base (length ys) (sizeAccessible (length ys))))) in
    rewrite cong (natToBase base) leq in
    SmallerTailHLT (baseSmallerHereditarySmaller xs ys sml (aRec xs (LTESucc reflexive)) (bRec ys (LTESucc reflexive)))

baseSmallerHereditarySmaller_leftSmaller x FZ xs ys aAcc bAcc lt leq = absurd lt
baseSmallerHereditarySmaller_leftSmaller FZ (FS y) xs ys (Access aRec) bAcc lt leq =
  baseSmallerHereditarySmaller xs (FS y :: ys) (oneLessSmaller xs ys leq) (aRec xs reflexive) bAcc
baseSmallerHereditarySmaller_leftSmaller (FS x) (FS y) xs ys (Access aRec) (Access bRec) lt leq =
    rewrite baseToHereditaryAccIrrelevent (natToBase base (length xs))
              (aRec (natToBase base (length xs))
                (natToBaseAccLengthSmaller base (length xs) (sizeAccessible (length xs))))
              (rewrite leq in
                       (bRec (natToBase base (length ys))
                        (natToBaseAccLengthSmaller base (length ys) (sizeAccessible (length ys))))) in
    rewrite cong (natToBase base) leq in
            SameOrderHLT (fromLteSucc lt)

baseToHereditaryOrder [] tailAcc expAcc = HZSSmaller
baseToHereditaryOrder (FZ :: xs) (Access rec) eAcc =
  smallerOrderTransSmaller (baseToHereditaryOrder xs (rec xs reflexive) (rec (natToBase base (length xs)) (natToBaseLengthSmaller base (length xs))))
                           (baseSmallerHereditarySmaller (natToBase base (length xs)) (natToBase base (length (FZ :: xs)))
                                                         (natSmallerBaseSmaller base (length xs) (length (FZ :: xs)) reflexive)
                                                         (rec (natToBase base (length xs)) (natToBaseLengthSmaller base (length xs)))
                                                         eAcc)
baseToHereditaryOrder (FS x :: xs) (Access rec) eAcc =
  HASmaller (baseSmallerHereditarySmaller (natToBase base (length xs)) (natToBase base (length (FS x :: xs)))
                                          (natSmallerBaseSmaller base (length xs) (length (FS x :: xs)) reflexive)
                                          (rec (natToBase base (length xs)) (natToBaseLengthSmaller base (length xs)))
                                          eAcc)

baseToHereditary : {base : Nat} -> List (Fin (S (S base))) -> Hereditary (S (S base))
baseToHereditary xs = baseToHereditaryAcc xs (sizeAccessible xs)

natToHereditary : {ord : Nat} -> (n : Nat) -> Hereditary (S (S ord))
natToHereditary n = baseToHereditary (natToBase ord n)

hereditaryToNat : {n : Nat} -> Hereditary n -> Nat
hereditaryToNat HZ = Z
hereditaryToNat (HA coef exp rest x) = (S (finToNat coef)) * power n (hereditaryToNat exp) + (hereditaryToNat rest)

-- multPowerPowerPlus : (base, exp, exp' : Nat) ->
--   power base (exp + exp') = (power base exp) * (power base exp')
-- multPowerPowerPlus base Z       exp' =
--     rewrite sym $ plusZeroRightNeutral (power base exp') in Refl
-- multPowerPowerPlus base (S exp) exp' =
--   rewrite multPowerPowerPlus base exp exp' in
--     rewrite sym $ multAssociative base (power base exp) (power base exp') in
--       Refl

--powerOneNeutral : (base : Nat) -> power base 1 = base
--powerOneNeutral base = rewrite multCommutative base 1 in multOneLeftNeutral base
--
--powerOneSuccOne : (exp : Nat) -> power 1 exp = 1
--powerOneSuccOne Z       = Refl
--powerOneSuccOne (S exp) = rewrite powerOneSuccOne exp in Refl
--
--powerPowerMultPower : (base, exp, exp' : Nat) ->
--  power (power base exp) exp' = power base (exp * exp')
--powerPowerMultPower _ exp Z = rewrite multZeroRightZero exp in Refl
--powerPowerMultPower base exp (S exp') =
--  rewrite powerPowerMultPower base exp exp' in
--  rewrite multRightSuccPlus exp exp' in
--  rewrite sym $ multPowerPowerPlus base exp (exp * exp') in
--          Refl

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
    <~ S n + S (S (S n) * (S (finToNat c) * power (S (S n)) e1)) ...(lteAddLeft (S (S (S n) * (S (finToNat c) * power (S (S n)) e1))) (S n))
    ~~ S (S n) + S (S n) * (S (finToNat c) * power (S (S n)) e1) ...(sym $ plusSuccRightSucc (S n) (S (S n) * (S (finToNat c) * power (S (S n)) e1)))
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

