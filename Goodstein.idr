import Data.Fin
import Control.WellFounded
import Hereditary

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

covering
decrement : {base : Nat} -> (h : Hereditary (S (S base))) -> {auto nonzero : HLT HZ h} -> Hereditary (S (S base))

covering
borrow : {base : Nat} -> (h : Hereditary (S (S base))) -> Hereditary (S (S base))
borrow HZ = HZ
borrow ee@(HA coef exp rest smaller) = HA last (decrement ee) (borrow (decrement ee)) ?borrowSmaller

decrement (HA FZ e HZ so) {nonzero = HZLTHA} = borrow e
decrement (HA (FS c) e HZ so) {nonzero = HZLTHA} = HA (weaken c) e (borrow e) ?borrowSmallerer
decrement (HA coef e rest@(HA _ _ _ _) so) {nonzero = HZLTHA} = HA coef e (decrement rest) ?decSmaller

covering
goodsteinSequence' : {ord : Nat} -> (start : Hereditary (S (S ord))) -> List Nat
goodsteinSequence' HZ = [0]
goodsteinSequence' h = hereditaryToNat h :: goodsteinSequence' (decrement (bump h) {nonzero = ?nonzerobump})

covering
goodsteinSequence : (start : Nat) -> List Nat
goodsteinSequence start = goodsteinSequence' (natToHereditary {ord = 0} start)
