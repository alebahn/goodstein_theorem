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
  wellFounded o = Access (acc o)
  where
    sameOrderTrans : {o : Ordinal} -> {c1, c2 : Nat} -> OLT o (OA (PS c1) e r1 so1) -> (LTE c1 c2) -> OLT o (OA (PS c2) e r2 so2)
    sameOrderTrans OZLTOA _ = OZLTOA
    sameOrderTrans (SameOrderLT lt {c1 = PS c0} {c2 = PS c1}) lte = SameOrderLT (transitive lt lte)
    sameOrderTrans (SmallerOrderLT olt) _ = SmallerOrderLT olt
    sameOrderTrans (SmallerTailLT olt {r1 = r0} {r2 = r1}) lte with (decEq c1 c2)
      sameOrderTrans (SmallerTailLT olt {r1 = r0} {r2 = r1}) lte | (Yes Refl) = ?hho
      sameOrderTrans (SmallerTailLT olt {r1 = r0} {r2 = r1}) lte | (No contra) = SameOrderLT (lteNotEqToLT c1 c2 lte contra)

    accAcc : (x : Ordinal) -> (0 aAcc : Accessible OLT x) -> (y : Ordinal) -> OLT y x -> Accessible OLT y
    accAcc (OA coef e rest so) (Access rec) OZ OZLTOA = Access (\z, olt => absurd olt)
    accAcc (OA c2 e r2 so2) (Access rec) (OA c1 e r1 so1) (SameOrderLT z) = ?accAcc_rhs_2
    accAcc (OA c2 e2 r2 so2) (Access rec) (OA c1 e1 r1 so1) (SmallerOrderLT olta) = ?accAcc_rhs_3
    accAcc (OA c e r2 so2) (Access rec) (OA c e r1 so1) (SmallerTailLT z) = ?accAcc_rhs_4

    acc : (x, y : Ordinal) -> OLT y x -> Accessible OLT y
    acc (OA coef e rest so) OZ OZLTOA = Access (\z, olt => absurd olt)
    acc (OA (PS 0) e r2 so2) (OA (PS c1) e r1 so1) (SameOrderLT lt) = absurd lt
    acc (OA (PS (S c2)) e r2 so2) (OA (PS c1) e r1 so1) (SameOrderLT lt) = Access (\z, olt => acc (OA (PS c2) e r2 so2) z (sameOrderTrans ?oo (fromLteSucc lt)))
    acc (OA c2 e2 r2 so2) (OA c1 e1 r1 so1) (SmallerOrderLT olta) = Access (\z, oltb => ?hol)
    acc (OA c e r2 so2) (OA c e r1 so1) (SmallerTailLT z) = ?acc_rhs_3

