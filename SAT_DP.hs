-- SAT_DP.hs - DP Algorithm using Bucket Elimination in Haskell
-- Copyright (C) 2026 Robert Coffey

import Control.Exception (assert)
import Data.Char (isSpace, toLower)
import Data.Int (Int64)
import Data.List (partition)
import Data.Maybe (mapMaybe)
import Debug.Trace (trace)
import Text.Read (readMaybe)

-- CNF -------------------------------------------------------------------------

type Variable = Int64    -- variable (> 0)
type Literal = Variable  -- variable + sign
type Clause = [Literal]
data CNF = CNF
  { cnf_n_vars :: Int64
  , cnf_n_clauses :: Int64
  , cnf_clauses :: [Clause]
  } deriving (Show)

clauseHasVar :: Variable -> Clause -> Bool
clauseHasVar _ [] = False
clauseHasVar var (lit:lits) = (abs lit == var) || clauseHasVar var lits

-- Generate var-resolvent given two clauses.
resolve :: Variable -> Clause -> Clause -> Maybe Clause
resolve var c1 c2 =
  if elem var c1 && elem (-var) c2
  then Just $ (filter (/= var) c1) ++ (filter (/= (-var)) c2)
  else if elem (-var) c1 && elem var c2
       then Just $ (filter (/= (-var)) c1) ++ (filter (/= var) c2)
       else Nothing

-- Generate all var-resolvents given a list of clauses.
resolveAll :: Variable -> [Clause] -> [Clause]
resolveAll _ [] = []
resolveAll var (c:cs) = mapMaybe (resolve var c) cs ++ resolveAll var cs

-- DP --------------------------------------------------------------------------

data Bucket = Bucket
  { buk_var :: Variable
  , buk_clauses :: [Clause]
  } deriving (Show)

-- TODO: No need for CNF, just clauses.
-- Create and fill buckets in order of vars. For each clause, place clause in
-- first bucket whose variable is in clause.
fillBuckets :: [Variable] -> CNF -> [Bucket]
fillBuckets vars (CNF _ _ []) = map (\v -> Bucket v []) vars
fillBuckets [] _ = assert (False) []  -- TODO: ERROR: clauses remain
fillBuckets (v:vars) (CNF _ _ clauses) =
  let (with, without) = partition (clauseHasVar v) clauses in
    Bucket v with : fillBuckets vars (CNF 0 0 without)

-- Insert clause into buckets such that clause is placed into the first bucket
-- in list which represents a variable that is in clause.
insertClause :: Clause -> [Bucket] -> [Bucket]
insertClause [] _ = trace "error: attempted to insert empty clause" []
insertClause _ [] = trace "error: no bucket found for clause" []
insertClause clause (b:buckets) =
  if clauseHasVar (buk_var b) clause
  then Bucket (buk_var b) (clause : (buk_clauses b)) : buckets
  else b : insertClause clause buckets

insertClauses :: [Clause] -> [Bucket] -> [Bucket]
insertClauses [] buckets = buckets
insertClauses (c:clauses) buckets =
  let new_buks = (insertClause c buckets)
  in insertClauses clauses new_buks

resolveBuckets :: [Bucket] -> [Bucket]
resolveBuckets [] = []  -- TODO: ERROR if resolvents remain?
resolveBuckets (b:buckets) =
  let rs = resolveAll (buk_var b) (buk_clauses b)
  in b : resolveBuckets (insertClauses rs buckets)
  --in trace (show rs) (b : resolveBuckets (insertClauses rs buckets))

-- Parser ----------------------------------------------------------------------

-- Expects string of form "p cnf n_vars n_clauses".
-- Returns Maybe (n_vars, n_clauses).
parseDIMACSHeader :: String -> Maybe (Int64, Int64)
parseDIMACSHeader line = case words line of
  [_, _, str_n_vars, str_n_clauses] -> do
    n_vars    <- readMaybe str_n_vars
    n_clauses <- readMaybe str_n_clauses
    Just (n_vars, n_clauses)
  _ -> Nothing

-- Expects string of form "lit ... lit 0" (lit not zero, zero or more lits).
parseDIMACSClause :: String -> Maybe Clause
parseDIMACSClause line = case words line of
  [] -> Nothing
  xs -> let literals = init xs
            end = last xs
        in if (end /= "0")
           then Nothing
           else Just (map (\x -> read x :: Literal) literals)

-- TODO: Check if variable out of range or wrong number of clauses.
-- Parse string containing DIMACS CNF format header and clauses.
-- Skips comment lines and empty lines.
parseDIMACS :: String -> Maybe CNF
parseDIMACS file_str =
  let relev_lines = filter (\x -> x /= "" && toLower (head x) /= 'c')
                    (map (dropWhile isSpace) (lines file_str))
      header_line : clause_lines = relev_lines  -- TODO: Handle error cases.
      (n_vars, n_clauses) = case parseDIMACSHeader header_line of
                              Just (x, y) -> (x, y)
                              Nothing     -> (0, 0)
  in if (n_vars, n_clauses) == (0, 0)
     then Nothing
     else let clauses = mapMaybe parseDIMACSClause clause_lines
          in if n_clauses /= (fromIntegral $ length clauses)
             then Nothing
             else Just $ CNF n_vars n_clauses clauses

-- Main ------------------------------------------------------------------------

newline :: IO ()
newline = putStrLn ""

main' :: String -> IO ()
main' str = do
  let maybe_cnf = parseDIMACS str
  case maybe_cnf of
    Nothing  -> putStrLn "error: invalid CNF"
    Just cnf -> do
      putStr "Initial CNF: "
      print cnf
      newline

      let buckets = fillBuckets [1..(cnf_n_vars cnf)] cnf
      putStrLn "Initial Buckets: "
      mapM_ print buckets
      newline

      let res_buks = resolveBuckets buckets
      putStrLn "Resolved Buckets: "
      mapM_ print res_buks

main :: IO ()
main = do
  input <- getContents
  main' input
