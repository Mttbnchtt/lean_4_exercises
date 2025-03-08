structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero}

#eval Nat.zero = 0
#eval natOrigin

def replaceX ( α : Type) (p : PPoint α) (newX : α) : PPoint α :=
  { p with x := newX}
#check (replaceX)
#check replaceX
#check (replaceX Nat)
#check replaceX Nat
#check (replaceX Nat natOrigin)
#check replaceX Nat natOrigin
#check (replaceX Nat natOrigin 1)
#check replaceX Nat natOrigin 1
#eval replaceX Nat natOrigin 1

inductive Sign where
  | pos : Sign
  | neg : Sign
  | zero : Sign

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int | Sign.zero => Nat :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
  | Sign.zero => (0 : Nat)

#eval posOrNegThree Sign.pos
#eval posOrNegThree Sign.neg
#eval posOrNegThree Sign.zero
