#eval (1 + 2 : Nat)
#eval 1-2 -- it evaluates to 0 because the default type of the expression is Nat
#eval (1-2 : Int) -- it evaluates to -1 because the type of the expression is Int

#check 1-2
#check (1-2 : Int)
