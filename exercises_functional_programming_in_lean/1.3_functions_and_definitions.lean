def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

def append_strings (s1 s2 s3 : String) : String := String.append s1 (String.append s2 s3)
#eval append_strings "A" "B" "C"
#eval append_strings hello " " lean
