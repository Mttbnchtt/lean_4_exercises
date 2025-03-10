structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero}

#eval Nat.zero = 0
#eval natOrigin

def replaceX (α : Type) (p : PPoint α) (newX : α) : PPoint α :=
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

def divisors ( n : Nat) : List Nat :=
  List.filter (fun x => (¬ (x = 0)) ∧ (n % x = 0)) (List.range (n+1))
#eval divisors 10

#eval [2, 3, 5, 7].length
#eval [2, 3, 5, 7].map (fun x => x + 1)
#eval ([2, 3, 5, 7].map (fun x => x + 1)).length
#eval [2, 3, 5, 7].map (fun x => x + 1)
def primesUnder10 : List Nat := [2, 3, 5, 7]
#eval primesUnder10.length
#eval primesUnder10.head?
#eval primesUnder10.head!
#eval List.nil.head? (α := Nat)
#eval [].head? (α := Nat)
#eval ([] : List Nat).head?

#eval List.sum [2, 3]
#eval [2, 3].sum

def is_perfect (n : Nat) : Bool :=
  (divisors n).sum = n
#eval is_perfect 100

def p (n : Nat) : List Nat :=
  List.filter (fun x => (x ≤ n) ∧ (is_perfect x)) ()
