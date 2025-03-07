-- inductive Bool where
--   | true : Bool
--   | false : Bool

-- inductive Nat where
--   | zero : Nat
--   | succ : Nat → Nat

-- inductive Nat where
--   | zero : Nat
--   | succ (n : Nat) : Nat

def isZero : Nat → Bool
  | Nat.zero => Bool.true
  | _ => Bool.false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero              => Bool.true
  | Nat.succ (Nat.succ k) => even k
  | _                     => Bool.false

#eval even 0
#eval even 3

def even_v2 (n : Nat) : Bool :=
  match n with
  | Nat.zero => Bool.true
  | Nat.succ k => not (even_v2 k)

#eval even_v2 0
#eval even_v2 3

def even_v3 (n : Nat) : Bool :=
  match n with
  | Nat.zero => Bool.true
  | Nat.succ (Nat.succ k) =>
      if even_v3 k then Bool.true else Bool.false
  | _ => Bool.false

#eval even_v3 0
#eval even_v3 3

def plus (n m : Nat) : Nat :=
  match m with
  | Nat.zero => n
  | Nat.succ k => Nat.succ (plus n k)
#eval plus 2 3

def m (n m : Nat) : nat :=
  match m with
  | Nat.zero => Nat.zero
  | Nat.succ k => plus (m (n k) n)
