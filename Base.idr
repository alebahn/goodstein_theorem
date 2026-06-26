import Data.Fin
import Data.Fin.Properties
import Data.List
import Decidable.Equality
import Control.WellFounded
import Residual

%default total

lengthDistributesOverAppend : (xs : List a) -> (ys : List a) -> length (xs ++ ys) = length xs + length ys
lengthDistributesOverAppend [] ys = Refl
lengthDistributesOverAppend (x :: xs) ys = 
  -- IH : length (xs ++ ys) = length xs + length ys
  -- S (length (xs ++ ys)) = S (length xs + length ys)
  cong S (lengthDistributesOverAppend xs ys)

private
lteAddLeft : (n, m : Nat) -> LTE n (m + n)
lteAddLeft n m = rewrite plusCommutative m n in lteAddRight n

private
lteUnderBase : (c, base, tail : Nat) -> LTE c (base + (c + tail))
lteUnderBase c base tail =
  transitive (lteAddLeft c base) (plusLteMonotoneLeft base c (c + tail) (lteAddRight c))

private
lteMultBase : (c, base : Nat) -> LTE c (c * S (S base))
lteMultBase 0 base = LTEZero
lteMultBase (S c) base =
  LTESucc (rewrite multCommutative c (S (S base)) in
    lteUnderBase c (S base) (S base * c))

private
ltMultBase : (c, base : Nat) -> Data.Nat.LT (S c) ((S c) * S (S base))
ltMultBase c base =
  LTESucc (LTESucc (rewrite multCommutative c (S (S base)) in
    lteUnderBase c base (S base * c)))

private
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
                         (0 left : Accessible LT n) ->
                         (0 right : Accessible LT n) ->
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

private
positiveResidualLowerBound : (base, cn : Nat) -> (rn : Fin (S (S base))) ->
                             LTE (S base) (((S cn) * S (S base)) + finToNat rn)
positiveResidualLowerBound base cn rn =
  transitive
    (lteSuccRight (reflexive {x = S base}))
    (transitive
      (lteAddRight (S (S base)) {m = cn * S (S base)})
      (lteAddRight ((S cn) * S (S base)) {m = finToNat rn}))

private
positiveResidualNotLtFin : (base, cn : Nat) -> (rn, rm : Fin (S (S base))) ->
                           Not ((((S cn) * S (S base)) + finToNat rn) `LT` finToNat rm)
positiveResidualNotLtFin base cn rn rm lt =
  succNotLTEpred $
    transitive
      (transitive lt (fromLteSucc (elemSmallerThanBound rm)))
      (positiveResidualLowerBound base cn rn)

private
plusLeftCancelLT : (left, right, right' : Nat) ->
                   (left + right) `LT` (left + right') ->
                   right `LT` right'
plusLeftCancelLT Z right right' lt = lt
plusLeftCancelLT (S left) right right' (LTESucc lt) =
  plusLeftCancelLT left right right' lt

private
lteNotEqToLT : (left, right : Nat) -> left `LTE` right -> Not (left = right) -> left `LT` right
lteNotEqToLT Z Z LTEZero neq = void (neq Refl)
lteNotEqToLT Z (S right) LTEZero neq = LTESucc LTEZero
lteNotEqToLT (S left) Z LTEZero neq impossible
lteNotEqToLT (S left) (S right) (LTESucc lte) neq =
  LTESucc (lteNotEqToLT left right lte (\eq => neq (cong S eq)))

private
multLteMonotoneLeft : (right, left, left' : Nat) ->
                      left `LTE` left' ->
                      (left * right) `LTE` (left' * right)
multLteMonotoneLeft right 0 left' LTEZero = LTEZero
multLteMonotoneLeft right (S left) (S left') (LTESucc lte) =
  plusLteMonotone (reflexive {x = right}) (multLteMonotoneLeft right left left' lte)

private
quotientResidualLTE : (radix, quotient, quotient', residual : Nat) ->
                      quotient `LTE` quotient' ->
                      ((quotient * radix) + residual) `LTE` ((quotient' * radix) + residual)
quotientResidualLTE radix quotient quotient' residual lte =
  plusLteMonotoneRight residual (quotient * radix) (quotient' * radix)
    (multLteMonotoneLeft radix quotient quotient' lte)

private
oneMoreQuotientLeft : (radix, cm, residual : Nat) ->
                      (((S (S cm)) * radix) + residual) =
                      (((S cm) * radix) + (radix + residual))
oneMoreQuotientLeft radix cm residual =
  rewrite plusCommutative radix ((S cm) * radix) in
  rewrite sym (plusAssociative ((S cm) * radix) radix residual) in
    Refl

private
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

private
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
        natSmallerBaseAccSmaller base ((0 * S (S base)) + finToNat rn) ((0 * S (S base)) + finToNat rm) (Access nRec) (Access mRec) lt | (MkResidual rn 0) | FZ | (MkResidual rm 0) | FZ = absurd lt
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
