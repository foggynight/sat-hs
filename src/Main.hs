-- SAT_DP.hs - DP Algorithm using Bucket Elimination in Haskell
-- Copyright (C) 2026 Robert Coffey

import Control.Exception (assert)
import Control.Monad.Extra (mapMaybeM)
import Data.Char (isSpace, toLower)
import Data.Int (Int64)
import Data.List (nub, partition)
import Data.Maybe (mapMaybe)
import Debug.Trace (trace)
import Text.Read (readMaybe)

-- CNF -------------------------------------------------------------------------

type Variable = Int64    -- variable (> 0)
type Literal = Variable  -- variable + sign
type Clause = [Literal]
data CNF = CNF
  { cnf_n_vars :: Int64
  , _cnf_n_clauses :: Int64
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

-- TODO: Rewrite such that monadic action handled outside? This should be pure.
-- Generate var-resolvent given two clauses. Removes duplicate literals and
-- returns Nothing if resolvent is tautology.
resolve :: Variable -> Clause -> Clause -> IO (Maybe Clause)
resolve var c1 c2 = do
  result <- do
    if (elem var c1 && elem (-var) c2) || (elem (-var) c1 && elem var c2)
    then do
      putStr $ (show var) ++ ": " ++ (show c1) ++ " " ++ (show c2) ++ " -> "
      let f = not . litHasVar var
      let resolvent = nub $ filter f (c1 ++ c2)
      putStr $ show resolvent
      if clauseIsTautology resolvent
      then do putStr (" (tautology)\n")
              pure Nothing
      else do newline
              pure $ Just resolvent
    else do pure Nothing
  pure result

-- Generate all var-resolvents given a list of clauses.
resolveAll :: Variable -> [Clause] -> IO [Clause]
resolveAll _ [] = pure []
resolveAll var (c:cs) = do
  var_resolvents <- mapMaybeM (resolve var c) cs
  rest_resolvents <- resolveAll var cs
  pure $ var_resolvents ++ rest_resolvents

-- DP --------------------------------------------------------------------------
-- NOTE: All functions assume "0" bucket is at the end of bucket list.

-- Bucket with variable label, contains only clauses that contain that variable.
-- Bucket "0" represents the bucket of empty clauses.
data Bucket = Bucket
  { buk_var :: Variable
  , buk_clauses :: [Clause]
  }

instance Show Bucket where
  show buk = show (buk_var buk) ++ ": " ++ show (buk_clauses buk)

-- Create and fill buckets in order of vars.
-- For each clause, place clause in first bucket whose variable is in clause.
fillBuckets :: [Variable] -> [Clause] -> [Bucket]
fillBuckets vars [] = map (\v -> Bucket v []) vars
fillBuckets [] _ = assert (False) []
fillBuckets (v:vars) clauses =
  let (clauses_with, clauses_without) = partition (clauseHasVar v) clauses
  in Bucket v clauses_with : fillBuckets vars clauses_without

-- Insert clause into buckets such that clause is placed into the first bucket
-- in list which represents a variable that is in clause, inserts empty clause
-- into "0" bucket.
bucketInsertClause :: Clause -> [Bucket] -> [Bucket]
bucketInsertClause clause [] =
  trace ("error: no bucket found for clause: " ++ show clause) []
bucketInsertClause clause (b:buckets) =
  if clauseHasVar (buk_var b) clause
  then Bucket (buk_var b) (clause : (buk_clauses b)) : buckets
  else b : bucketInsertClause clause buckets

bucketInsertClauses :: [Clause] -> [Bucket] -> [Bucket]
bucketInsertClauses [] buckets = buckets
bucketInsertClauses (c:clauses) buckets =
  let new_buks = (bucketInsertClause c buckets)
  in bucketInsertClauses clauses new_buks

resolveBuckets :: [Bucket] -> IO [Bucket]
resolveBuckets [] = pure []
resolveBuckets (b:buckets) = do
  rs <- resolveAll (buk_var b) (buk_clauses b)
  rest <- resolveBuckets (bucketInsertClauses rs buckets)
  pure $ b : rest

assignsSatisfy :: [Literal] -> Clause -> Bool
assignsSatisfy _ [] = False
assignsSatisfy assigns (lit:lits)
  | elem lit assigns = True
  | otherwise        = assignsSatisfy assigns lits

assignsSatisfyAll :: [Literal] -> [Clause] -> Bool
assignsSatisfyAll assigns clauses =
  and $ map (\c -> assignsSatisfy assigns c) clauses

-- Find valid assignment of variable, given list of previous assignments and
-- clause. Returns literal representing variable assignment.
findAssign :: Variable -> [Literal] -> [Clause] -> Literal
findAssign var prev clauses
  | assignsSatisfyAll (var : prev) clauses = var
  | otherwise                              = -var

-- Buckets must be in reverse order of variable ordering, "0" bucket dropped.
extractSolution' :: [Bucket] -> [Literal] -> [Literal]
extractSolution' [] assigns = assigns
extractSolution' ((Bucket var clauses) : buckets) assigns =
  let assign = case clauses of
                 [] -> var  -- Bucket empty, assume positive assignment.
                 cs -> (findAssign var assigns cs)
  in extractSolution' buckets (assign : assigns)

-- Extract satisfying assignment from list of buckets containing clauses of
-- fully resolved CNF. If "0" bucket contains empty clauses, returns Nothing as
-- CNF is unsatisfiable.
extractSolution :: [Bucket] -> Maybe [Literal]
extractSolution [] = trace "error: no buckets to extract solution" Nothing
extractSolution [_zero_buk] = Just []
extractSolution buckets =
  case reverse buckets of
    (zero_buk : rest_buks) -> case buk_clauses zero_buk of
                                [] -> Just $ extractSolution' rest_buks []
                                _  -> Nothing
    _ -> trace "error: reversed buckets failed pattern match" Nothing

-- Parser ----------------------------------------------------------------------

parseFail :: String -> Maybe a
parseFail msg = trace ("error: parse failed: " ++ msg) Nothing

-- Expects string of form "p cnf n_vars n_clauses".
-- Returns Maybe (n_vars, n_clauses).
parseDIMACSHeader :: String -> Maybe (Int64, Int64)
parseDIMACSHeader line = case words line of
  [_, _, str_n_vars, str_n_clauses] -> do
    n_vars    <- readMaybe str_n_vars
    n_clauses <- readMaybe str_n_clauses
    Just (n_vars, n_clauses)
  _ -> trace "error: parse failed: invalid header" Nothing

-- Expects string of form "lit ... lit 0" (lit not zero, zero or more lits).
parseDIMACSClause :: Variable -> String -> Maybe Clause
parseDIMACSClause max_var line = case words line of
  [] -> parseFail "empty clause line"  -- NOTE: Should never reach here.
  xs -> let lits = init xs; end = last xs in
          if end /= "0"
          then parseFail "missing clause terminator"
          else let parsed = mapMaybe (\x -> readMaybe x :: Maybe Literal) lits
               in if (length parsed) /= (length lits)
                  then parseFail "failed to parse literal"
                  else if any (\lit -> lit == 0 || abs lit > max_var) parsed
                       then parseFail "literal out of range"
                       else Just parsed

-- TODO: Stop printing "not enough"/"too many" clauses when real error was
-- failed to parse literal.
parseDIMACS' :: [String] -> Maybe CNF
parseDIMACS' [] = parseFail "missing header"
parseDIMACS' (header_line : clause_lines) = do
  (n_vars, n_clauses) <- parseDIMACSHeader header_line
  let clauses = mapMaybe (\c -> parseDIMACSClause n_vars c) clause_lines
      diff = n_clauses - (fromIntegral $ length clauses)
  if diff > 0
  then parseFail "not enough clauses"
  else if diff < 0
       then parseFail "too many clauses"
       else Just $ CNF n_vars n_clauses clauses

-- Parse string containing DIMACS CNF format header and clauses.
-- Skips comment lines and empty lines.
parseDIMACS :: String -> Maybe CNF
parseDIMACS file_str =
  let relev_lines = filter (\x -> x /= "" && toLower (head x) /= 'c')
                    (map (dropWhile isSpace) (lines file_str))
  in parseDIMACS' relev_lines

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

      -- TODO: Handle variable ordering.
      let buckets = fillBuckets ([1..(cnf_n_vars cnf)] ++ [0]) (cnf_clauses cnf)
      putStrLn "Initial Buckets: "
      mapM_ print buckets
      newline

      putStrLn "Deriving resolvents..."
      res_buks <- resolveBuckets buckets
      newline

      putStrLn "Resolved Buckets: "
      mapM_ print res_buks
      newline

      let solution = extractSolution res_buks
      case solution of
        Nothing -> putStrLn "UNSAT"
        Just lits -> putStr $ "SAT: " ++ (show lits) ++ "\n"

main :: IO ()
main = do
  input <- getContents
  main' input
