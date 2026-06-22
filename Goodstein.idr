import Data.Nat
import Data.Fin
import Control.WellFounded
import Residual
import Data.List

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

mutual
  data Hereditary : (n: Nat) -> Type where
    HZ : Hereditary (S n)
    HA : (coef : Fin n) -> (exp : Hereditary (S n)) -> (rest : Hereditary (S n)) -> SmallerOrderH rest exp -> Hereditary (S n)

  data SmallerOrderH : Hereditary n -> Hereditary n -> Type where
    HZSSmaller : SmallerOrderH HZ o
    HASmaller : HLT h o -> SmallerOrderH (HA c h t sml) o

  data HLT : Hereditary n -> Hereditary n -> Type where
    HZLTHA : HLT HZ (HA coef e rest so)
    SameOrderHLT : LT (finToNat c1) (finToNat c2) -> HLT (HA c1 e r1 so1) (HA c2 e r2 so2)
    SmallerOrderHLT : HLT e1 e2 -> HLT (HA c1 e1 r1 so1) (HA c2 e2 r2 so2)
    SmallerTailHLT : HLT r1 r2 -> HLT (HA c e r1 so1) (HA c e r2 so2)

data FCmp : Fin n -> Fin n -> Type where
  NLess : LT (finToNat j) (finToNat k) -> FCmp j k
  NEq : FCmp k k
  NMore : GT (finToNat j) (finToNat k) -> FCmp j k

decFCmp : (l, r : Fin n) -> FCmp l r
decFCmp FZ FZ = NEq
decFCmp FZ (FS r) = NLess (LTESucc LTEZero)
decFCmp (FS l) FZ = NMore (LTESucc LTEZero)
decFCmp (FS l) (FS r) with (decFCmp l r)
  decFCmp (FS l) (FS r) | (NLess lt) = NLess (LTESucc lt)
  decFCmp (FS l) (FS l) | NEq = NEq
  decFCmp (FS l) (FS r) | (NMore gt) = NMore (LTESucc gt)

data HCmp : Hereditary n -> Hereditary n -> Type where
  HCLess : HLT x y -> HCmp x y
  HEq : HCmp x x
  HCMore : HLT y x -> HCmp x y

Uninhabited (Data.Nat.LT x x) where
  uninhabited (LTESucc x) = uninhabited x

Uninhabited (HLT x x) where
  uninhabited (SameOrderHLT y) = uninhabited y
  uninhabited (SmallerOrderHLT y) = uninhabited y
  uninhabited (SmallerTailHLT y) = uninhabited y

sameArgIsSameLT : (x, y : Data.Nat.LTE a b) -> x === y
sameArgIsSameLT LTEZero LTEZero = Refl
sameArgIsSameLT (LTESucc x) (LTESucc y) = cong LTESucc (sameArgIsSameLT x y)

sameArgIsSameHLT : (x, y : HLT a b) -> x === y
sameArgIsSameHLT HZLTHA HZLTHA = Refl
sameArgIsSameHLT (SameOrderHLT x) (SameOrderHLT y) = cong SameOrderHLT (sameArgIsSameLT x y)
sameArgIsSameHLT (SameOrderHLT x) (SmallerOrderHLT y) = absurd y
sameArgIsSameHLT (SameOrderHLT x) (SmallerTailHLT y) = absurd x
sameArgIsSameHLT (SmallerOrderHLT x) (SameOrderHLT y) = absurd x
sameArgIsSameHLT (SmallerOrderHLT x) (SmallerOrderHLT y) = cong SmallerOrderHLT (sameArgIsSameHLT x y)
sameArgIsSameHLT (SmallerOrderHLT x) (SmallerTailHLT y) = absurd x
sameArgIsSameHLT (SmallerTailHLT x) (SameOrderHLT y) = absurd y
sameArgIsSameHLT (SmallerTailHLT x) (SmallerOrderHLT y) = absurd y
sameArgIsSameHLT (SmallerTailHLT x) (SmallerTailHLT y) = cong SmallerTailHLT (sameArgIsSameHLT x y)

sameArgIsSameOrderH : (x, y : SmallerOrderH h o) -> x === y
sameArgIsSameOrderH HZSSmaller HZSSmaller = Refl
sameArgIsSameOrderH (HASmaller x) (HASmaller y) = cong HASmaller (sameArgIsSameHLT x y)

decHCmp : (l, r : Hereditary n) -> HCmp l r
decHCmp HZ HZ = HEq
decHCmp HZ (HA coef exp rest x) = HCLess HZLTHA
decHCmp (HA coef exp rest x) HZ = HCMore HZLTHA
decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp2 rest2 sml2) with (decHCmp exp1 exp2)
  decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp2 rest2 sml2) | (HCLess lt) = HCLess (SmallerOrderHLT lt)
  decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq with (decFCmp coef1 coef2)
    decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq | (NLess lt) = HCLess (SameOrderHLT lt)
    decHCmp (HA coef2 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq | NEq with (decHCmp rest1 rest2)
      decHCmp (HA coef2 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq | NEq | (HCLess lt) = HCLess (SmallerTailHLT lt)
      decHCmp (HA coef2 exp1 rest1 sml1) (HA coef2 exp1 rest1 sml2) | HEq | NEq | HEq = rewrite sameArgIsSameOrderH sml1 sml2 in HEq
      decHCmp (HA coef2 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq | NEq | (HCMore gt) = HCMore (SmallerTailHLT gt)
    decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp1 rest2 sml2) | HEq | (NMore gt) = HCMore (SameOrderHLT gt)
  decHCmp (HA coef1 exp1 rest1 sml1) (HA coef2 exp2 rest2 sml2) | (HCMore x) = HCMore (SmallerOrderHLT x)

lteAddLeft : (n, m : Nat) -> LTE n (m + n)
lteAddLeft n m = rewrite plusCommutative m n in lteAddRight n

lteUnderBase : (c, base, tail : Nat) -> LTE c (base + (c + tail))
lteUnderBase c base tail =
  transitive (lteAddLeft c base) (plusLteMonotoneLeft base c (c + tail) (lteAddRight c))

lteMultBase : (c, base : Nat) -> LTE c (c * S (S base))
lteMultBase 0 base = LTEZero
lteMultBase (S c) base =
  LTESucc (rewrite multCommutative c (S (S base)) in
    lteUnderBase c (S base) (S base * c))

ltMultBase : (c, base : Nat) -> Data.Nat.LT (S c) ((S c) * S (S base))
ltMultBase c base =
  LTESucc (LTESucc (rewrite multCommutative c (S (S base)) in
    lteUnderBase c base (S base * c)))

ltResidualQuotient : (c, base : Nat) -> (r : Fin (S (S base))) ->
  Data.Nat.LT (S c) (((S c) * S (S base)) + finToNat r)
ltResidualQuotient c base r =
  transitive (ltMultBase c base) (lteAddRight ((S c) * S (S base)))

natToBaseAcc : (base : Nat) -> (n : Nat) -> (0 acc : Accessible Data.Nat.LT n) -> List (Fin (S (S base)))
natToBaseAcc base n (Access rec) with (getResidual (S (S base)) n)
  natToBaseAcc base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) with (r)
    natToBaseAcc base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) | FZ = []
    natToBaseAcc base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) | (FS r') = [r]
  natToBaseAcc base (((S c) * S (S base)) + finToNat r) (Access rec) | (MkResidual r (S c)) =
    natToBaseAcc base (S c) (rec (S c) (ltResidualQuotient c base r)) ++ [r]

natToBase : (base : Nat) -> (n : Nat) -> List (Fin (S (S base)))
natToBase base n = natToBaseAcc base n (wellFounded n)

data BaseSmaller : (a, b : List (Fin base)) -> Type

lengthDistributesOverAppend : (xs : List a) -> (ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys = 
  -- IH : length (xs ++ ys) = length xs + length ys
  -- S (length (xs ++ ys)) = S (length xs + length ys)
  cong S (lengthDistributesOverAppend xs ys)

natToBaseAccLengthSmaller : (base : Nat) -> (n : Nat) -> (0 acc : Accessible Data.Nat.LT n) ->
                            LTE (S (length (natToBaseAcc base n acc))) (S n)
natToBaseAccLengthSmaller base n (Access rec) with (getResidual (S (S base)) n)
  natToBaseAccLengthSmaller base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) with (r)
    natToBaseAccLengthSmaller base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) | FZ = LTESucc LTEZero
    natToBaseAccLengthSmaller base ((0 * S (S base)) + finToNat r) (Access rec) | (MkResidual r 0) | (FS r') = lteAddRight 2
  natToBaseAccLengthSmaller base (((S c) * S (S base)) + finToNat r) (Access rec) | (MkResidual r (S c)) =
    rewrite lengthDistributesOverAppend (natToBaseAcc base (S c) (rec (S c) (ltResidualQuotient c base r))) [r] in
    rewrite plusCommutative (length (natToBaseAcc base (S c) (rec (S c) (ltResidualQuotient c base r)))) 1 in
            LTESucc (transitive (natToBaseAccLengthSmaller base (S c) (rec (S c) (ltResidualQuotient c base r))) (ltResidualQuotient c base r))

natToBaseLengthSmaller : (base : Nat) -> (n : Nat) ->
  LTE (S (length (natToBase base n))) (S n)
natToBaseLengthSmaller base n = natToBaseAccLengthSmaller base n (wellFounded n)

baseToHereditaryAcc : {base : Nat} -> (xs : List (Fin (S (S base)))) ->
  (0 acc : SizeAccessible xs) -> Hereditary (S (S base))

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

baseToHereditaryOrder [] tailAcc expAcc = HZSSmaller
baseToHereditaryOrder (FZ :: xs) (Access rec) expAcc = ?baseToHereditaryOrder_rhs_4
baseToHereditaryOrder (FS x :: xs) (Access rec) expAcc = HASmaller ?OASmaller_arg_0

baseToHereditary : {base : Nat} -> List (Fin (S (S base))) -> Hereditary (S (S base))
baseToHereditary xs = baseToHereditaryAcc xs (sizeAccessible xs)

natToHereditary : {ord : Nat} -> (n : Nat) -> Hereditary (S (S ord))
natToHereditary n = baseToHereditary (natToBase ord n)

hereditaryToNat : {n : Nat} -> Hereditary n -> Nat
hereditaryToNat HZ = Z
hereditaryToNat (HA coef exp rest x) = (S (finToNat coef)) * power n (hereditaryToNat exp) + (hereditaryToNat rest)

bump : Hereditary n -> Hereditary (S n)
bump HZ = HZ
bump (HA coef exp rest smaller) = HA (weaken coef) (bump exp) (bump rest) ?bumpSmaller

decrement : (h : Hereditary (S (S ord))) -> {auto nonzero : HLT HZ h} -> Hereditary (S (S ord))
decrement (HA coef e HZ so) {nonzero = HZLTHA} = ?decrement_rhs_1
decrement (HA coef e rest@(HA _ _ _ _) so) {nonzero = HZLTHA} = HA coef e (decrement rest) ?decSmaller

covering
goodsteinSequence' : {ord : Nat} -> (start : Hereditary (S (S ord))) -> List Nat
goodsteinSequence' HZ = [0]
goodsteinSequence' h = hereditaryToNat h :: goodsteinSequence' (decrement (bump h) {nonzero = ?nonzerobump})

covering
goodsteinSequence : (start : Nat) -> List Nat
goodsteinSequence start = goodsteinSequence' (natToHereditary {ord = 0} start)
