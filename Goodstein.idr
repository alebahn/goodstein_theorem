import Data.Fin
import Data.Fin.Properties
import Control.WellFounded
import Residual
import Data.List
import Decidable.Equality

%default total

lengthDistributesOverAppend : (xs : List a) -> (ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys = 
  -- IH : length (xs ++ ys) = length xs + length ys
  -- S (length (xs ++ ys)) = S (length xs + length ys)
  cong S (lengthDistributesOverAppend xs ys)

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
    HA : (coef : Fin n) -> (exp : Hereditary (S n)) -> (rest : Hereditary (S n)) -> (0 smaller : SmallerOrderH rest exp) -> Hereditary (S n)

  data SmallerOrderH : Hereditary n -> Hereditary n -> Type where
    HZSSmaller : SmallerOrderH HZ o
    HASmaller : HLT h o -> SmallerOrderH (HA c h t sml) o

  data HLT : Hereditary n -> Hereditary n -> Type where
    HZLTHA : HLT HZ (HA coef e rest so)
    SameOrderHLT : (lt : LT (finToNat c1) (finToNat c2)) -> HLT (HA c1 e r1 so1) (HA c2 e r2 so2)
    SmallerOrderHLT : (hlt : HLT e1 e2) -> HLT (HA c1 e1 r1 so1) (HA c2 e2 r2 so2)
    SmallerTailHLT : (hlt : HLT r1 r2) -> HLT (HA c e r1 so1) (HA c e r2 so2)

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

[antireflLT] Uninhabited (Data.Nat.LT x x) where
  uninhabited (LTESucc x) = uninhabited x

Uninhabited (HLT x x) where
  uninhabited (SameOrderHLT y) = uninhabited @{antireflLT} y
  uninhabited (SmallerOrderHLT y) = uninhabited y
  uninhabited (SmallerTailHLT y) = uninhabited y

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

natToBaseAccIrrelevant : (base, n : Nat) ->
                         (0 left : Accessible Data.Nat.LT n) ->
                         (0 right : Accessible Data.Nat.LT n) ->
                         natToBaseAcc base n left === natToBaseAcc base n right
natToBaseAccIrrelevant base n (Access leftRec) (Access rightRec) with (getResidual (S (S base)) n)
  natToBaseAccIrrelevant base ((0 * S (S base)) + finToNat r) (Access leftRec) (Access rightRec) | (MkResidual r 0) with (r)
    natToBaseAccIrrelevant base ((0 * S (S base)) + finToNat r) (Access leftRec) (Access rightRec) | (MkResidual r 0) | FZ = Refl
    natToBaseAccIrrelevant base ((0 * S (S base)) + finToNat r) (Access leftRec) (Access rightRec) | (MkResidual r 0) | (FS r') = Refl
  natToBaseAccIrrelevant base (((S c) * S (S base)) + finToNat r) (Access leftRec) (Access rightRec) | (MkResidual r (S c)) =
    cong (++ [r]) (natToBaseAccIrrelevant
      base
      (S c)
      (leftRec (S c) (ltResidualQuotient c base r))
      (rightRec (S c) (ltResidualQuotient c base r)))

data BaseSmaller : (a, b : List (Fin base)) -> Type where
  BaseEmptySmaller : (x : Fin base) -> (xs : List (Fin (S base))) -> BaseSmaller [] (FS x :: xs)
  BaseValueSmaller : (x, y : Fin base) -> (xs : List (Fin base)) -> (finToNat x `LT` finToNat y) ->
                     BaseSmaller (xs ++ [x]) (xs ++ [y])
  BaseSnocSmaller : {x, y : Fin base} -> {xs, ys : List (Fin base)} -> BaseSmaller xs ys -> BaseSmaller (xs ++ [x]) (ys ++ [y])

|||For use as a view on BaseSmaller.
|||This is less restrictive than BaseSmaller
data HeadSmaller : (a, b : List (Fin base)) -> Type where
  HeadSame : {x : Fin base} -> length xs === length ys -> BaseSmaller xs ys -> HeadSmaller (x :: xs) (x :: ys)
  LeftSmaller : (x, y : Fin base) -> (xs, ys : List (Fin base)) ->
                (finToNat x `LT` finToNat y) ->
                length xs === length ys ->
                HeadSmaller (x :: xs) (y :: ys)
  LeftShorter : LTE (length xs) (length ys) -> HeadSmaller xs (FS y :: ys)

baseValueHeadSmaller : (x, y : Fin base) -> LTE (S (finToNat x)) (finToNat y) ->
                       (zs : List (Fin base)) -> HeadSmaller (zs ++ [x]) (zs ++ [y])
baseValueHeadSmaller x y lt [] = LeftSmaller x y [] [] lt Refl
baseValueHeadSmaller x y lt (z :: xs) = HeadSame (trans (lengthDistributesOverAppend xs [x]) (sym $ (lengthDistributesOverAppend xs [y]))) (BaseValueSmaller x y xs lt)

snocHeadSmaller : {x, y : Fin base} -> {xs, ys : List (Fin base)} -> HeadSmaller xs ys -> HeadSmaller (xs ++ [x]) (ys ++ [y])
snocHeadSmaller (HeadSame {xs} {ys} leq sml) = HeadSame (trans (lengthDistributesOverAppend xs [x]) (trans (cong (+ 1) leq) (sym $ (lengthDistributesOverAppend ys [y])))) (BaseSnocSmaller sml)
snocHeadSmaller (LeftSmaller z w xs ys lt leq) = LeftSmaller z w (xs ++ [x]) (ys ++ [y]) lt (trans (lengthDistributesOverAppend xs [x]) (trans (cong (+ 1) leq) (sym $ (lengthDistributesOverAppend ys [y]))))
snocHeadSmaller (LeftShorter {y = y'} {ys} lt) =
  LeftShorter $ rewrite lengthDistributesOverAppend xs [x] in
                rewrite plusCommutative (length xs) 1 in
                rewrite lengthDistributesOverAppend ys [y] in
                rewrite plusCommutative (length ys) 1 in
                        LTESucc lt

headSmaller : (xs, ys : List (Fin base)) -> (smaller : BaseSmaller xs ys) -> HeadSmaller xs ys
headSmaller [] (FS x :: zs) (BaseEmptySmaller x zs) = LeftShorter LTEZero
headSmaller (zs ++ [x]) (zs ++ [y]) (BaseValueSmaller x y zs lt) = baseValueHeadSmaller x y lt zs
headSmaller (xs ++ [x]) (ys ++ [y]) (BaseSnocSmaller sml) = snocHeadSmaller (headSmaller xs ys sml)

snocNotEmpty : {x : a} -> {xs : List a} -> Not (xs ++ [x] === [])
snocNotEmpty {xs = []} Refl impossible
snocNotEmpty {xs = (y :: xs)} Refl impossible

appendSmallerSmaller : {ws, zs : List (Fin base)} -> BaseSmaller ws zs -> (xs , ys : List (Fin base)) -> (0 leq : length xs === length ys) -> BaseSmaller (ws ++ xs) (zs ++ ys)
appendSmallerSmaller sml [] [] prf = rewrite appendNilRightNeutral ws in
                                     rewrite appendNilRightNeutral zs in
                                             sml
appendSmallerSmaller sml [] (x :: xs) prf = void $ absurd prf
appendSmallerSmaller sml (x :: xs) [] prf = void $ absurd prf
appendSmallerSmaller sml (x :: xs) (y :: ys) prf =
  rewrite appendAssociative ws [x] xs in
  rewrite appendAssociative zs [y] ys in
          appendSmallerSmaller (BaseSnocSmaller sml) xs ys (injective prf)

oneLessSmaller : {y : Fin base} -> (xs , ys : List (Fin (S base))) -> (0 leq : length xs === length ys) -> BaseSmaller xs (FS y :: ys)
oneLessSmaller xs ys prf = appendSmallerSmaller (BaseEmptySmaller y []) xs ys prf

baseEmptySmallerSnocRight' : {x : Fin base} -> BaseSmaller ys xs -> (0 prf : ys = []) -> BaseSmaller [] (xs ++ [x])
baseEmptySmallerSnocRight' (BaseEmptySmaller y zs) prf = BaseEmptySmaller y (zs ++ [x])
baseEmptySmallerSnocRight' (BaseValueSmaller y z zs w) prf = void $ snocNotEmpty prf
baseEmptySmallerSnocRight' (BaseSnocSmaller y) prf = void $ snocNotEmpty prf

baseEmptySmallerSnocRight : {x : Fin base} -> BaseSmaller [] xs -> BaseSmaller [] (xs ++ [x])
baseEmptySmallerSnocRight smaller = baseEmptySmallerSnocRight' smaller Refl

Uninhabited (BaseSmaller xs []) where
  uninhabited a = uninhabited' a Refl
  where
    uninhabited' : BaseSmaller zs ys -> (0 prfY : ys = []) -> Void
    uninhabited' (BaseEmptySmaller _ _) Refl impossible
    uninhabited' (BaseValueSmaller x y xs1 z) prfY = void $ snocNotEmpty prfY
    uninhabited' (BaseSnocSmaller x) prfY = void $ snocNotEmpty prfY

emptyNotSmallerFZ : BaseSmaller [] (FZ :: xs) -> Void
emptyNotSmallerFZ small = emptyNotSmallerFZ' small Refl Refl
where
  emptyNotSmallerFZ' : BaseSmaller ys zs -> (0 prf1 : ys = []) -> (0 prf2 : zs = (FZ :: xs)) -> Void
  emptyNotSmallerFZ' (BaseEmptySmaller _ _) _ Refl impossible
  emptyNotSmallerFZ' (BaseValueSmaller x y xs1 z) prf1 prf2 = void $ snocNotEmpty prf1
  emptyNotSmallerFZ' (BaseSnocSmaller x) prf1 prf2 = void $ snocNotEmpty prf1

natToBaseAccOfPosIsBiggerThanEmpty : (base, n : Nat) ->
                                     (0 acc : Accessible Data.Nat.LT n) ->
                                     (0 nPos : IsSucc n) ->
                                     BaseSmaller [] (natToBaseAcc base n acc)
natToBaseAccOfPosIsBiggerThanEmpty base n (Access rec) nPos with (getResidual (S (S base)) n)
  natToBaseAccOfPosIsBiggerThanEmpty base ((0 * S (S base)) + finToNat r) (Access rec) nPos | (MkResidual r 0) with (r)
    natToBaseAccOfPosIsBiggerThanEmpty base ((0 * S (S base)) + finToNat r) (Access rec) nPos | (MkResidual r 0) | FZ = void $ uninhabited nPos
    natToBaseAccOfPosIsBiggerThanEmpty base ((0 * S (S base)) + finToNat r) (Access rec) nPos | (MkResidual r 0) | (FS x) = BaseEmptySmaller x []
  natToBaseAccOfPosIsBiggerThanEmpty base (((S c) * S (S base)) + finToNat r) (Access rec) nPos | (MkResidual r (S c)) =
    baseEmptySmallerSnocRight (natToBaseAccOfPosIsBiggerThanEmpty base (S c) (rec (S c) (ltResidualQuotient c base r)) ItIsSucc)

positiveResidualLowerBound : (base, cn : Nat) -> (rn : Fin (S (S base))) ->
                             LTE (S base) (((S cn) * S (S base)) + finToNat rn)
positiveResidualLowerBound base cn rn =
  transitive
    (lteSuccRight (reflexive {x = S base}))
    (transitive
      (lteAddRight (S (S base)) {m = cn * S (S base)})
      (lteAddRight ((S cn) * S (S base)) {m = finToNat rn}))

positiveResidualNotLtFin : (base, cn : Nat) -> (rn, rm : Fin (S (S base))) ->
                           Not ((((S cn) * S (S base)) + finToNat rn) `LT` finToNat rm)
positiveResidualNotLtFin base cn rn rm lt =
  succNotLTEpred $
    transitive
      (transitive lt (fromLteSucc (elemSmallerThanBound rm)))
      (positiveResidualLowerBound base cn rn)

plusLeftCancelLT : (left, right, right' : Nat) ->
                   (left + right) `LT` (left + right') ->
                   right `LT` right'
plusLeftCancelLT Z right right' lt = lt
plusLeftCancelLT (S left) right right' (LTESucc lt) =
  plusLeftCancelLT left right right' lt

lteNotEqToLT : (left, right : Nat) -> left `LTE` right -> Not (left = right) -> left `LT` right
lteNotEqToLT Z Z LTEZero neq = void (neq Refl)
lteNotEqToLT Z (S right) LTEZero neq = LTESucc LTEZero
lteNotEqToLT (S left) Z LTEZero neq impossible
lteNotEqToLT (S left) (S right) (LTESucc lte) neq =
  LTESucc (lteNotEqToLT left right lte (\eq => neq (cong S eq)))

multLteMonotoneLeft : (right, left, left' : Nat) ->
                      left `LTE` left' ->
                      (left * right) `LTE` (left' * right)
multLteMonotoneLeft right 0 left' LTEZero = LTEZero
multLteMonotoneLeft right (S left) (S left') (LTESucc lte) =
  plusLteMonotone (reflexive {x = right}) (multLteMonotoneLeft right left left' lte)

quotientResidualLTE : (radix, quotient, quotient', residual : Nat) ->
                      quotient `LTE` quotient' ->
                      ((quotient * radix) + residual) `LTE` ((quotient' * radix) + residual)
quotientResidualLTE radix quotient quotient' residual lte =
  plusLteMonotoneRight residual (quotient * radix) (quotient' * radix)
    (multLteMonotoneLeft radix quotient quotient' lte)

oneMoreQuotientLeft : (radix, cm, residual : Nat) ->
                      (((S (S cm)) * radix) + residual) =
                      (((S cm) * radix) + (radix + residual))
oneMoreQuotientLeft radix cm residual =
  rewrite plusCommutative radix ((S cm) * radix) in
  rewrite sym (plusAssociative ((S cm) * radix) radix residual) in
    Refl

oneMoreQuotientNotLT : (base, cm : Nat) -> (rn, rm : Fin (S (S base))) ->
                       Not ((((S (S cm)) * S (S base)) + finToNat rn) `LT`
                            (((S cm) * S (S base)) + finToNat rm))
oneMoreQuotientNotLT base cm rn rm lt =
  succNotLTEpred $
    transitive
      (transitive
        (LTESucc (plusLeftCancelLT ((S cm) * radix) (radix + finToNat rn) (finToNat rm) $
          rewrite sym (oneMoreQuotientLeft radix cm (finToNat rn)) in
            lt))
        (elemSmallerThanBound rm))
      (lteSuccRight (lteAddRight radix {m = finToNat rn}))
  where
    radix : Nat
    radix = S (S base)

greaterQuotientNotLT : (base, cn, cm : Nat) -> (rn, rm : Fin (S (S base))) ->
                       ((S cm) `LT` (S cn)) ->
                       Not ((((S cn) * S (S base)) + finToNat rn) `LT`
                            (((S cm) * S (S base)) + finToNat rm))
greaterQuotientNotLT base cn cm rn rm cmLtCn lt =
  oneMoreQuotientNotLT base cm rn rm $
    transitive
      (LTESucc (quotientResidualLTE (S (S base)) (S (S cm)) (S cn) (finToNat rn) cmLtCn))
      lt

natSmallerBaseAccSmaller : (base, n, m : Nat) ->
                           (0 nAcc : Accessible Data.Nat.LT n) ->
                           (0 mAcc : Accessible Data.Nat.LT m) ->
                           (n `LT` m) ->
                           BaseSmaller (natToBaseAcc base n nAcc) (natToBaseAcc base m mAcc)
natSmallerBaseAccSmaller base n m (Access nRec) (Access mRec) lt with (getResidual (S (S base)) n)
  natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) m (Access nRec) (Access mRec) lt | (MkResidual rn 0) with (rn)
    natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) m (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ with (getResidual (S (S base)) m)
      natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ | (MkResidual rm 0) with (rm)
        natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ | (MkResidual rm 0) | FZ = absurd @{antireflLT} lt
        natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ | (MkResidual rm 0) | (FS rm') = BaseEmptySmaller rm' []
      natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ | (MkResidual rm (S cm)) =
        baseEmptySmallerSnocRight (natToBaseAccOfPosIsBiggerThanEmpty base (S cm) (mRec (S cm) (ltResidualQuotient cm base rm)) ItIsSucc)
    natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) m (Access nRec) (Access mRec) lt | (MkResidual rn 0) | (FS rn') with (getResidual (S (S base)) m)
      natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | (FS rn') | (MkResidual rm 0) with (rm)
        natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | (FS rn') | (MkResidual rm 0) | FZ = absurd lt
        natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | (FS rn') | (MkResidual rm 0) | (FS rm') = BaseValueSmaller (FS rn') (FS rm') [] lt
      natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | (FS rn') | (MkResidual rm (S cm)) =
        BaseSnocSmaller (natToBaseAccOfPosIsBiggerThanEmpty base (S cm) (mRec (S cm) (ltResidualQuotient cm base rm)) ItIsSucc)
  natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) m (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) with (getResidual (S (S base)) m)
    natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm 0) =
      void (positiveResidualNotLtFin base cn rn rm lt)
    natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm (S cm)) with (isLTE (S (S cn)) (S cm))
      natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm (S cm)) | (Yes quotientLt) =
        BaseSnocSmaller (natSmallerBaseAccSmaller base (S cn) (S cm) (nRec (S cn) (ltResidualQuotient cn base rn)) (mRec (S cm) (ltResidualQuotient cm base rm)) quotientLt)
      natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm (S cm)) | (No quotientNotLt) with (decEq cn cm)
        natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) (((S cn) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm (S cn)) | (No quotientNotLt) | (Yes Refl) =
          rewrite sym (natToBaseAccIrrelevant
            base
            (S cn)
            (nRec (S cn) (ltResidualQuotient cn base rn))
            (mRec (S cn) (ltResidualQuotient cn base rm))) in
              BaseValueSmaller
                rn
                rm
                (natToBaseAcc base (S cn) (nRec (S cn) (ltResidualQuotient cn base rn)))
                (plusLeftCancelLT
                  (S (S (base + (cn * S (S base)))))
                  (finToNat rn)
                  (finToNat rm)
                  lt)
        natSmallerBaseAccSmaller base (((S cn) * S (S base)) + finToNat rn) (((S cm) * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn (S cn)) | (MkResidual rm (S cm)) | (No quotientNotLt) | (No quotientNotSame) =
          void (greaterQuotientNotLT base cn cm rn rm
            (lteNotEqToLT (S cm) (S cn)
              (notLTImpliesGTE quotientNotLt)
              (\eq => quotientNotSame (injective (sym eq))))
            lt)

natSmallerBaseSmaller : (base, n, m : Nat) -> (n `LT` m) -> BaseSmaller (natToBase base n) (natToBase base m)
natSmallerBaseSmaller base n m lt = natSmallerBaseAccSmaller base n m (wellFounded n) (wellFounded m) lt

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

finToNatWeakenSame : (k : Fin n) -> finToNat (weaken k) === finToNat k
finToNatWeakenSame FZ = Refl
finToNatWeakenSame (FS k) = cong S (finToNatWeakenSame k)

bump : Hereditary n -> Hereditary (S n)

bumpSmaller : HLT h g -> HLT (bump h) (bump g)

bumpOrder : SmallerOrderH h o -> SmallerOrderH (bump h) (bump o)

bump HZ = HZ
bump (HA coef exp rest smaller) = HA (weaken coef) (bump exp) (bump rest) (bumpOrder smaller)

bumpSmaller HZLTHA = HZLTHA
bumpSmaller (SameOrderHLT lt {c1} {c2}) = SameOrderHLT $ rewrite (finToNatWeakenSame c1) in
                                                         rewrite (finToNatWeakenSame c2) in
                                                                 lt
bumpSmaller (SmallerOrderHLT hlt) = SmallerOrderHLT (bumpSmaller hlt)
bumpSmaller (SmallerTailHLT hlt) = SmallerTailHLT (bumpSmaller hlt)

bumpOrder HZSSmaller = HZSSmaller
bumpOrder (HASmaller hlt) = HASmaller (bumpSmaller hlt)

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
