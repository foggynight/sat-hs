module VarOrder where

import Data.List (sortOn)
import Data.Ord (Down(..))

import CNF
import Util

type VarOrderF = CNF -> [Variable]

-- TODO: Add varOrder constructor function which takes weight function, and
-- rewrite to use varOrder constructor?

-- Numeric: Select variables in numerical order.
varOrderNumeric :: VarOrderF
varOrderNumeric cnf = [1 .. (cnf_n_vars cnf)]

-- Fewest Clauses: Select variable which occurs in the fewest clauses.
varOrderFewestClauses :: VarOrderF
varOrderFewestClauses cnf =
  let clauses = (cnf_clauses cnf)
      occurs = map (count_occurs clauses) [1 .. (cnf_n_vars cnf)] in
    (map fst $ sortOn snd occurs)
  where count_occurs clauses var =
          (var, sum $ map ((count var) . (map abs)) clauses)

-- Jerowslow-Wang: Variable exponentially higher weight in shorter clause, more
-- clauses higher weight, select variables to maximize weight.
varOrderJeroslowWang :: VarOrderF
varOrderJeroslowWang (CNF n_vars _ clauses) =
  let vars = [1 .. n_vars]
      vws = zip vars (map calc_weight vars)
  in (map fst $ sortOn (Down . snd) vws)
  where calc_weight var =
          sum $ map (\c -> 2 ^^ (- (length c)) :: Double)
                $ filter (clauseHasVar var) clauses
