import Data.Fin
import Control.WellFounded
import Hereditary
import Hereditary.WellFounded
import Ordinal

%default total

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

bumpAsOrdinalSame : (h : Hereditary n) -> hereditaryAsOrdinal (bump h) === hereditaryAsOrdinal h
bumpAsOrdinalSame HZ = Refl
bumpAsOrdinalSame (HA coef exp rest smaller) =
  rewrite finToNatWeakenSame coef in
  sameArgIsSameOA (PS (finToNat coef)) (bumpAsOrdinalSame exp) (bumpAsOrdinalSame rest)

bumpStillNonZero : (h : Hereditary (S (S n))) -> {auto nonZero : HLT HZ h} -> HLT HZ (bump h)
bumpStillNonZero (HA coef e rest so) {nonZero = HZLTHA} = HZLTHA

decrementAcc : {base : Nat} -> (h : Hereditary (S (S base))) -> {auto nonzero : HLT HZ h} ->
               (0 acc : Accessible HLT h) -> Hereditary (S (S base))

decrementAccSmaller : {base : Nat} -> (h : Hereditary (S (S base))) -> {auto nonzero : HLT HZ h} ->
                      (0 acc : Accessible HLT h) -> HLT (decrementAcc {base} {nonzero} h acc) h

borrowAcc : {base : Nat} -> (h : Hereditary (S (S base))) -> (0 acc : Accessible HLT h) -> Hereditary (S (S base))

borrowAccSmallerOrder : {base : Nat} -> (h : Hereditary (S (S base))) -> (0 acc : Accessible HLT h) -> SmallerOrderH (borrowAcc h acc) h

borrowAccSmallerThanExp : {base : Nat} -> (h : Hereditary (S (S base))) -> (0 acc : Accessible HLT h) ->
                          {0 c : Fin (S base)} -> {0 r : Hereditary (S (S base))} -> {0 so : SmallerOrderH r h} ->
                          HLT (borrowAcc h acc) (HA c h r so)

decrementAcc (HA coef e r@(HA c' e' r' so') so) {nonzero = HZLTHA} (Access rec) =
  HA coef e (decrementAcc r (rec r (restSmaller r))) (smallerTransSmallerOrder (decrementAccSmaller r (rec r (restSmaller r))) so)
decrementAcc (HA FZ e HZ so) {nonzero = HZLTHA} (Access rec) = borrowAcc e (rec e (expSmaller e))
decrementAcc (HA (FS c) e HZ so) {nonzero = HZLTHA} (Access rec) = HA (weaken c) e (borrowAcc e (rec e (expSmaller e))) (borrowAccSmallerOrder e (rec e (expSmaller e)))

decrementAccSmaller (HA FZ e HZ so) {nonzero = HZLTHA} (Access rec) = borrowAccSmallerThanExp e (rec e (expSmaller e))
decrementAccSmaller (HA (FS c) e HZ so) {nonzero = HZLTHA} (Access rec) =
  SameOrderHLT $ rewrite finToNatWeakenSame c in reflexive
decrementAccSmaller (HA coef e r@(HA c' e' r' so') so) {nonzero = HZLTHA} (Access rec) =
  SmallerTailHLT (decrementAccSmaller r (rec r (restSmaller r)))

borrowAcc HZ acc = HZ
borrowAcc ee@(HA coef exp rest smaller) (Access rec) =
  let (eePred ** predSmaller) = (decrementAcc ee (Access rec) ** decrementAccSmaller ee (Access rec))
  in HA last eePred (borrowAcc eePred (rec eePred predSmaller)) (borrowAccSmallerOrder eePred (rec eePred predSmaller))

borrowAccSmallerOrder HZ acc = HZSSmaller
borrowAccSmallerOrder ee@(HA coef exp rest smaller) (Access rec) =
  HASmaller (decrementAccSmaller ee (Access rec))

borrowAccSmallerThanExp HZ acc = HZLTHA
borrowAccSmallerThanExp ee@(HA coef exp rest smaller) (Access rec) =
  SmallerOrderHLT (decrementAccSmaller ee (Access rec))

decrement : {base : Nat} -> (h : Hereditary (S (S base))) -> {auto nonzero : HLT HZ h} -> Hereditary (S (S base))
decrement h = decrementAcc h (wellFounded h)

stepSmaller : {ord : Nat} -> (h : Hereditary (S (S ord))) -> {auto nonzero : HLT HZ h} -> OLT (hereditaryAsOrdinal (decrement (bump h) {nonzero = bumpStillNonZero h})) (hereditaryAsOrdinal h)

goodsteinSequenceAcc : {ord : Nat} -> (start : Hereditary (S (S ord))) -> (0 acc : Accessible OLT (hereditaryAsOrdinal start)) -> List Nat
goodsteinSequenceAcc HZ _ = [0]
goodsteinSequenceAcc h@(HA coef exp rest smaller) (Access rec) =
  hereditaryToNat h :: goodsteinSequenceAcc (decrement (bump h)) (rec _ (stepSmaller h))

goodsteinSequence' : {ord : Nat} -> (start : Hereditary (S (S ord))) -> List Nat
goodsteinSequence' start = goodsteinSequenceAcc start (wellFounded (hereditaryAsOrdinal start))

goodsteinSequence : (start : Nat) -> List Nat
goodsteinSequence start = goodsteinSequence' (natToHereditary {ord = 0} start)
