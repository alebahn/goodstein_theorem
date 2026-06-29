import Data.Nat
import Decidable.Equality
import Control.WellFounded
import Util

%default total

data Pos = PS Nat

LT : Pos -> Pos -> Type
LT (PS k) (PS j) = LT k j

[posTransitive] Transitive Pos LT where
  transitive {x = (PS x)} {y = (PS y)} {z = (PS z)} a b = transitive (lteSuccRight a) b

mutual
  data Ordinal : Type where
    OZ : Ordinal
    OA : (coef : Pos) -> (exp : Ordinal) -> (rest : Ordinal) -> SmallerOrder rest exp -> Ordinal

  data SmallerOrder : Ordinal -> Ordinal -> Type where
    OZSSmaller : SmallerOrder OZ o
    OASmaller : OLT oh o -> SmallerOrder (OA c oh t sml) o

  data OLT : Ordinal -> Ordinal -> Type where
    OZLTOA : OLT OZ (OA coef e rest so)
    SameOrderLT : LT c1 c2 -> OLT (OA c1 e r1 so1) (OA c2 e r2 so2)
    SmallerOrderLT : OLT e1 e2 -> OLT (OA c1 e1 r1 so1) (OA c2 e2 r2 so2)
    SmallerTailLT : OLT r1 r2 -> OLT (OA c e r1 so1) (OA c e r2 so2)

natToOrd : Nat -> Ordinal
natToOrd 0 = OZ
natToOrd (S k) = OA (PS k) OZ OZ OZSSmaller

Transitive Ordinal OLT where
  transitive OZLTOA (SameOrderLT _) = OZLTOA
  transitive OZLTOA (SmallerOrderLT _) = OZLTOA
  transitive OZLTOA (SmallerTailLT _) = OZLTOA
  transitive (SameOrderLT lta {c1} {c2}) (SameOrderLT ltb {c1=c2} {c2=c3}) = SameOrderLT (transitive lta ltb @{posTransitive})
  transitive (SameOrderLT _) (SmallerOrderLT olt) = SmallerOrderLT olt
  transitive (SameOrderLT olt) (SmallerTailLT _) = SameOrderLT olt
  transitive (SmallerOrderLT olt) (SameOrderLT _) = SmallerOrderLT olt
  transitive (SmallerOrderLT olta) (SmallerOrderLT oltb) = SmallerOrderLT (transitive olta oltb)
  transitive (SmallerOrderLT olt) (SmallerTailLT _) = SmallerOrderLT olt
  transitive (SmallerTailLT _) (SameOrderLT lt) = SameOrderLT lt
  transitive (SmallerTailLT _) (SmallerOrderLT olt) = SmallerOrderLT olt
  transitive (SmallerTailLT olta) (SmallerTailLT oltb) = SmallerTailLT (transitive olta oltb)

Uninhabited (OLT a OZ) where
  uninhabited OZLTOA impossible
  uninhabited (SameOrderLT x) impossible
  uninhabited (SmallerOrderLT x) impossible
  uninhabited (SmallerTailLT x) impossible

WellFounded Ordinal OLT where
  wellFounded = ordinalAccessible
  where
    zeroAccessible : Accessible OLT OZ
    zeroAccessible = Access (\y, lt => absurd lt)

    mutual
      smallerOrderAccessible : (r : Ordinal) -> SmallerOrder r e -> (0 eAcc : Accessible OLT e) -> Accessible OLT r
      smallerOrderAccessible OZ OZSSmaller _ = zeroAccessible
      smallerOrderAccessible (OA (PS n) oh t sml) (OASmaller lt) (Access rec) =
        let 0 ohAcc = rec oh lt
            0 tAcc = smallerOrderAccessible t sml ohAcc in
            coefAccessible oh ohAcc t sml tAcc n (wellFounded n)

      coefAccessible : (e : Ordinal) ->
                       (0 eAcc : Accessible OLT e) ->
                       (r : Ordinal) ->
                       (so : SmallerOrder r e) ->
                       (0 rAcc : Accessible OLT r) ->
                       (n : Nat) ->
                       (0 nAcc : Accessible Data.Nat.LT n) ->
                       Accessible OLT (OA (PS n) e r so)
      coefAccessible e eAcc r so rAcc n nAcc = Access (rec eAcc rAcc nAcc)
        where
          rec : (0 eAcc : Accessible OLT e) ->
                (0 rAcc : Accessible OLT r) ->
                (0 nAcc : Accessible Data.Nat.LT n) ->
                (y : Ordinal) ->
                OLT y (OA (PS n) e r so) ->
                Accessible OLT y
          rec _ _ _ OZ OZLTOA = zeroAccessible
          rec eAcc _ (Access nRec) (OA (PS k) _ r1 so1) (SameOrderLT lt) =
            coefAccessible e eAcc r1 so1 (smallerOrderAccessible r1 so1 eAcc) k (nRec k lt)
          rec (Access eRec) _ _ (OA (PS k) e1 r1 so1) (SmallerOrderLT lt) =
            let 0 e1Acc = eRec e1 lt in
                coefAccessible e1 e1Acc r1 so1 (smallerOrderAccessible r1 so1 e1Acc) k (wellFounded k)
          rec eAcc (Access rRec) nAcc (OA _ _ r1 so1) (SmallerTailLT lt) =
            let 0 r1Acc = rRec r1 lt in
                coefAccessible e eAcc r1 so1 r1Acc n nAcc

    ordinalAccessible : (o : Ordinal) -> Accessible OLT o
    ordinalAccessible OZ = zeroAccessible
    ordinalAccessible (OA (PS n) e r so) =
      let 0 eAcc = ordinalAccessible e
          0 rAcc = smallerOrderAccessible r so eAcc in
          coefAccessible e eAcc r so rAcc n (wellFounded n)
