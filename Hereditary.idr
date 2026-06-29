import Control.Relation
import Data.Nat.Order.Properties
import Data.Fin
import Data.Fin.Properties
import Control.WellFounded
import Base
import Ordinal
import Util

%default total

mutual
  data Hereditary : (n: Nat) -> Type where
    HZ : Hereditary (S n)
    HA : (coef : Fin n) -> (exp : Hereditary (S n)) -> (rest : Hereditary (S n)) -> (smaller : SmallerOrderH rest exp) -> Hereditary (S n)

  data SmallerOrderH : Hereditary n -> Hereditary n -> Type where
    HZSSmaller : SmallerOrderH HZ o
    HASmaller : HLT h o -> SmallerOrderH (HA c h t sml) o

  data HLT : Hereditary n -> Hereditary n -> Type where
    HZLTHA : HLT HZ (HA coef e rest so)
    SameOrderHLT : (lt : LT (finToNat c1) (finToNat c2)) -> HLT (HA c1 e r1 so1) (HA c2 e r2 so2)
    SmallerOrderHLT : (hlt : HLT e1 e2) -> HLT (HA c1 e1 r1 so1) (HA c2 e2 r2 so2)
    SmallerTailHLT : (hlt : HLT r1 r2) -> HLT (HA c e r1 so1) (HA c e r2 so2)

Uninhabited (HLT x x) where
  uninhabited (SameOrderHLT y) = uninhabited @{antireflLT} y
  uninhabited (SmallerOrderHLT y) = uninhabited y
  uninhabited (SmallerTailHLT y) = uninhabited y

nothingHLTHZ : Not (HLT x HZ)
nothingHLTHZ HZLTHA impossible
nothingHLTHZ (SameOrderHLT lt) impossible
nothingHLTHZ (SmallerOrderHLT hlt) impossible
nothingHLTHZ (SmallerTailHLT hlt) impossible

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

smallerTransSmallerOrder : {h1, h2, order : Hereditary n} ->
                           HLT h1 h2 -> SmallerOrderH h2 order ->
                           SmallerOrderH h1 order
smallerTransSmallerOrder HZLTHA _ = HZSSmaller
smallerTransSmallerOrder (SameOrderHLT lt) (HASmaller hlt) = HASmaller hlt
smallerTransSmallerOrder (SmallerOrderHLT hlt1) (HASmaller hlt2) = HASmaller (transitive hlt1 hlt2)
smallerTransSmallerOrder (SmallerTailHLT _) (HASmaller hlt) = HASmaller hlt

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

expSmaller : (h : Hereditary (S n)) -> {0 so : SmallerOrderH r h} -> HLT h (HA c h r so)
expSmaller HZ = HZLTHA
expSmaller (HA coef exp rest smaller) = SmallerOrderHLT (expSmaller exp)

restSmaller : (h : Hereditary (S n)) -> {so : SmallerOrderH h e} -> HLT h (HA c e h so)
restSmaller HZ = HZLTHA
restSmaller (HA coef exp rest smaller) {so = (HASmaller hlt)} = SmallerOrderHLT hlt

hereditaryAsOrdinal : Hereditary n -> Ordinal

hSmallerAsoSmaller : SmallerOrderH h ex -> SmallerOrder (hereditaryAsOrdinal h) (hereditaryAsOrdinal ex)

hltAsOlt : HLT ha hb -> OLT (hereditaryAsOrdinal ha) (hereditaryAsOrdinal hb)

hereditaryAsOrdinal HZ = OZ
hereditaryAsOrdinal (HA coef exp rest smaller) = OA (PS (finToNat coef)) (hereditaryAsOrdinal exp) (hereditaryAsOrdinal rest) (hSmallerAsoSmaller smaller)

hSmallerAsoSmaller HZSSmaller = OZSSmaller
hSmallerAsoSmaller (HASmaller hlt) = OASmaller (hltAsOlt hlt)

hltAsOlt HZLTHA = OZLTOA
hltAsOlt (SameOrderHLT lt) = SameOrderLT lt
hltAsOlt (SmallerOrderHLT hlt) = SmallerOrderLT (hltAsOlt hlt)
hltAsOlt (SmallerTailHLT hlt) = SmallerTailLT (hltAsOlt hlt)
