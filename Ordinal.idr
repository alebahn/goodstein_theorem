import Data.Nat

%default total

data Pos = PS Nat

LT : Pos -> Pos -> Type
LT (PS k) (PS j) = LT k j

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
