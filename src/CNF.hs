module CNF where

type Variable = Int    -- variable (> 0)
type Literal = Variable  -- variable + sign
type Clause = [Literal]
data CNF = CNF
  { cnf_n_vars :: Int
  , cnf_n_clauses :: Int
  , cnf_clauses :: [Clause]
  }

instance Show CNF where
  show cnf = show (cnf_clauses cnf)

litHasVar :: Variable -> Literal -> Bool
litHasVar var lit = (var == abs lit)

-- When called with var = 0, checks if clause is the empty clause.
clauseHasVar :: Variable -> Clause -> Bool
clauseHasVar 0 clause = (clause == [])
clauseHasVar _ [] = False
clauseHasVar var (lit:lits) = (abs lit == var) || clauseHasVar var lits

clauseIsTautology :: Clause -> Bool
clauseIsTautology [] = False
clauseIsTautology (l:lits) = elem (-l) lits || clauseIsTautology lits

conditionClause :: Literal -> Clause -> Maybe Clause
conditionClause lit clause
  | elem lit clause = Nothing
  | otherwise       = Just $ filter (/= -lit) clause

conditionClauses :: Literal -> [Clause] -> [Clause]
conditionClauses _ [] = []
conditionClauses lit (c:cs) =
  case conditionClause lit c of
    Nothing -> rest
    Just cc -> cc : rest
  where rest = conditionClauses lit cs
