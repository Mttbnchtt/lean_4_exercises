def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

def append_strings (s1 s2 s3 : String) : String := String.append s1 (String.append s2 s3)
#eval append_strings "A" "B" "C"
#eval append_strings hello " " lean
#check append_strings

def successor (n : Nat) : Nat := n + 1
#eval successor 3
#check successor
#check successor 3

def maximum (n : Nat) (m : Nat) : Nat :=
  if n > m then
    n
  else m
#eval maximum 3 4
#eval maximum (4*3) (2*7)
#check maximum
#check (maximum)

def joinStringWith (str1 str2 str3 : String) : String := String.append str2 (String.append str1 str3)
#eval joinStringWith "A" "B" "C"
#check (joinStringWith)

def volume (h w d : Nat) : Nat := h * w * d
#eval volume 3 4 5
#check (volume)
