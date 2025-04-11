#eval (true && false)

def and_gate (x y : Bool) : Bool :=
  x && y

#eval (and_gate false false)
#eval (and_gate false true)
#eval (and_gate true  true)
#eval (and_gate true  true)

inductive Net where
| term: Bool -> Net
| inv:  Net  -> Net
| and:  Net  -> Net -> Net
| or:   Net  -> Net -> Net
deriving Repr

@[match_pattern] -- used in net_min below
def f: Net := .term false
@[match_pattern]
def t: Net := .term true


def net_eval (n:Net) : Bool :=
  match n with
  | Net.term b => b
  | Net.inv i => ! net_eval i
  | Net.and x y => (net_eval x) && (net_eval y)
  | Net.or x y =>  (net_eval x) || (net_eval y)


#eval net_eval t
#eval net_eval f
#check (fun (a:Bool) => Net.term a)

#check (fun (a:Bool) => (net_eval (.and t (.term a))))
#eval (fun (a:Bool) => (net_eval (.and t (.term a)))) false
#eval (fun (a:Bool) => (net_eval (.and t (.term a)))) true

#check Net.term

def net (a: Net) : Net := .and a (.inv a)
#check net
#check (net_eval (net t))

#eval net_eval (.and t f)
#eval net_eval (.and t t)

def net_min (n:Net) : Net :=
  match n with
  | .term _       => n
  | .inv i        => match net_min i with
    | t           => f
    | f           => t
    | .inv ii     => ii
    | ii          => .inv ii
  | .and l r      => match net_min l, net_min r with
    | f, _
    | _, f   => f
    | t, t   => t
    | ll, rr => .and ll rr
  | .or l r  => match net_min l, net_min r with
    | t, _
    | _, t   => t
    | f, f   => f
    | ll, rr => .or ll rr

#eval net_min (.and t t)
#eval net_min (.and (.and f t) t)
#eval net_min (.and (.or t f) t)
#eval net_min (.or t (.or t f))
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
