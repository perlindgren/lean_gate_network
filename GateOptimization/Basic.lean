#eval (true && false)

def and_gate (x y : Bool) : Bool :=
  x && y

#eval (and_gate false false)
#eval (and_gate false true)
#eval (and_gate true true)
#eval (and_gate true true)

inductive Net where
| term: Bool -> Net
--| input: String -> Net
| and: Net -> Net -> Net
| or: Net -> Net -> Net
deriving Repr

def f: Net := Net.term false
def t: Net := Net.term true
def i (b:Bool) : Net := Net.term b



def net_eval (n:Net) : Bool :=
  match n with
  | Net.term b => b
  | Net.and x y => (net_eval x) && (net_eval y)
  | Net.or x y =>  (net_eval x) || (net_eval y)


#eval net_eval t
#eval net_eval f

#eval net_eval (.and t f)
#eval net_eval (.and t t)

def net_min (n:Net) : Net :=
  match n with
  | .term _              => n
  | .and l r =>
    match net_min l, net_min r with
    | .term false, _
    | _, .term false     => .term false
    | ll, rr             => .and ll rr
  | .or l r =>
    match net_min l, net_min r with
    | .term true, _
    | _, .term true     => .term true
    | ll, rr             => .or ll rr

#eval net_min (.and t t)
#eval net_min (.and (.and f t) t)
#eval net_min (.and (.or t f) t)
#eval net_min (.or t (.or t f))

theorem net_min_correct : ∀ n, net_eval n = net_eval (net_min n) := by
  intro n
  induction n using net_min.induct <;> simp [net_eval, net_min, *]

-- theorem net_min_proof:  ∀ n, net_eval (net_min n) = net_eval n := by
--   intro n
--   induction n
--   . simp [net_min, net_eval]
--   . rw [net_min]
--     split
--     .
--     . sorry
--     sorry
--   . sorry



  -- rw [net_min.eq_def]
  -- cases n
  -- . simp
  -- .
  -- . sorry



  -- cases (net_min n)
  -- .
  -- . sorry
  -- . sorry
