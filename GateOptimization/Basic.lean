#eval (true && false)

def and_gate (x y : Bool) : Bool :=
  x && y

#eval (and_gate false false)
#eval (and_gate false true)
#eval (and_gate true  true)
#eval (and_gate true  true)

inductive Net where
| term: Bool   -> Net
| var:  String -> Net
| inv:  Net    -> Net
| and:  Net    -> Net -> Net
| or:   Net    -> Net -> Net
deriving Repr

@[match_pattern] -- used in net_min below
def f: Net := .term false
@[match_pattern]
def t: Net := .term true

def eval (n:Net) (env: String -> Bool) : Bool :=
  match n with
  | .term b  => b
  | .var s   => env s
  | .inv i   => ! eval i env
  | .and x y => (eval x env) && (eval y env)
  | .or x y  => (eval x env) || (eval y env)

def ofList (xs : List (String × Bool)) : String → Bool := fun name =>
  xs.find? (fun elem => elem.fst == name) |>.map Prod.snd |>.getD false

-- example environment
def env := ofList [("x", true), ("y", false)]

#eval eval t env
#eval eval f env
#eval eval (.and (.var "x") (.var "y")) env
#eval eval (.and t f) env
#eval eval (.and t t) env

def net_min (n:Net) : Net :=
  match n with
  | .term _
  | .var _   => n
  | .inv i   => match net_min i with
    | t        => f
    | f        => t
    | .inv ii  => ii -- double inversion
    | ii       => .inv ii
  | .and l r => match net_min l, net_min r with
    | f, _
    | _, f     => f
    | t, t     => t
    | t, o
    | o, t     => o
    | ll, rr   => .and ll rr
  | .or l r  => match net_min l, net_min r with
    | t, _
    | _, t     => t
    | f, f     => f
    | f, o
    | o, f     => o
    | ll, rr   => .or ll rr

#eval net_min (.inv t)
#eval net_min (.inv f)
#eval net_min (.and t t)
#eval net_min (.and t (.var "x"))
#eval net_min (.and (.var "x") t)
#eval net_min (.and (.var "x") f)
#eval net_min (.and f (.var "x"))
#eval net_min (.and (.and f t) t)
#eval net_min (.and (.or (.var "y") f) t)
#eval net_min (.or t (.or t f))
#eval net_min (.or f (.or f f))


theorem net_min_correct : ∀ n, eval n = eval (net_min n) := by
  intro n
  induction n using net_min.induct <;> simp [eval, net_min, *]

-- theorem net_min_proof:  ∀ n, net_eval (net_min n) = net_eval n := by
--   intro n
--   induction n
--   . simp [net_min, net_eval]
--   . rw [net_min]
--     split
--     . rw [net_eval]
--       rw [net_eval]
--       simp
--       rw [heqt]

--     . sorry
--     . sorry
--   . sorry
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
