#eval (true && false)

def and_gate (x y : Bool) : Bool :=
  x && y

#eval (and_gate false false)
#eval (and_gate false true)
#eval (and_gate true true)
#eval (and_gate true true)

inductive Net where
| term: Bool -> Net
| and: Net -> Net -> Net
| or: Net -> Net -> Net

-- derive Repr

def n: Net := Net.term false
