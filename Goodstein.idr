import Data.Nat
import Data.Fin

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

divModFin' : (fuel : Nat) -> (num : Nat) -> (pDenom : Nat) -> (Nat, Fin (S pDenom))
divModFin' 0 num pDenom = (0, 0)
divModFin' (S k) num pDenom with (isLTE num pDenom)
  divModFin' (S k) num pDenom | (Yes prf) = (Z, natToFinLT num)
  divModFin' (S k) num pDenom | (No contra) =
    let (q, r) = divModFin' k (minus num (S pDenom)) pDenom
    in (S q, r)

divModFin : (num : Nat) -> (denom : Nat) -> {auto pos : IsSucc denom} -> (Nat, Fin denom) 
divModFin num (S denom) = divModFin' num num denom

finToHereditary : Fin n -> Hereditary n
finToHereditary FZ = HZ
finToHereditary (FS j) = HA j HZ HZ HZSSmaller

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

hOne : Hereditary (S (S n))
hOne = HA 0 HZ HZ HZSSmaller

covering
natToBase : {base : Nat} -> (n : Nat) -> List (Fin (S (S base)))
natToBase n with (divModFin n (S (S base)))
  natToBase n | (q, r) = (natToBase q) ++ [r]

covering
baseToHereditary : {base : Nat} -> List (Fin (S (S base))) -> Hereditary (S (S base))
baseToHereditary [] = HZ
baseToHereditary (FZ :: xs) = baseToHereditary xs
baseToHereditary ((FS x) :: xs) = HA x (baseToHereditary (natToBase (S (length xs)))) (baseToHereditary xs) ?HA_arg_3

covering
natToHereditary : {ord : Nat} -> (n : Nat) -> Hereditary (S (S ord))
natToHereditary n = baseToHereditary (natToBase n)

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

