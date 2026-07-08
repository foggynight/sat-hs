-- -*- eval: (setq haskell-process-args-cabal-repl '("sat-dp")) -*-
-- ... or: M-x haskell-session-change-target, sat-dp

module Main where

import Control.Exception (assert)
import Data.Char (toLower)
import Data.List (nub, partition)
import Data.Maybe (mapMaybe)
import Debug.Trace (trace)
import Options.Applicative

import CNF
import DIMACS
import Util
import VarOrder

-- Resolution ------------------------------------------------------------------

data Resolvent = Resolvent
  { _res_p1 :: Clause   -- parent 1
  , _res_p2 :: Clause   -- parent 2
  , _res_res :: Clause  -- resolvent clause
  }

instance Show Resolvent where
  show (Resolvent p1 p2 res) =
    concat [ "Clauses: ", (show p1), ", ", (show p2)
           , " -> Resolvent: ", (show res)]

-- Generate var-resolvent given two clauses. Removes duplicate literals.
resolve :: Variable -> Clause -> Clause -> Maybe Resolvent
resolve var c1 c2 = do
  if (elem var c1 && elem (-var) c2) || (elem (-var) c1 && elem var c2)
  then let f = not . litHasVar var
           res = nub $ filter f (c1 ++ c2)
       in Just $ Resolvent c1 c2 res
  else Nothing

-- Generate all var-resolvents given a list of clauses. Returns tuple of
resolveAll :: Variable -> [Clause] -> [Resolvent]
resolveAll _ [] = []
resolveAll var (c:cs) =
  let var_resolvents = mapMaybe (resolve var c) cs
  in var_resolvents ++ resolveAll var cs

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

-- Insert resolvent into buckets such that resolvent clause is placed into the
-- first bucket in list which represents a variable that is in clause, inserts
-- empty clause into "0" bucket.
-- NOTE: Uses Resolvent instead of Clause only for log messages.
bucketsInsertResolvent :: Resolvent -> [Bucket] -> IO [Bucket]
bucketsInsertResolvent res [] = do  -- TODO: What if res trivial? Still prints...
  putStrLn $ show res ++ " (failed to find bucket)"
  pure []
bucketsInsertResolvent (Resolvent p1 p2 res) ((Bucket var cs):bs) = do
  if clauseIsTrivial res
  then do putStrLn $ show orig_res ++ " (trivial clause)"
          pure orig_buks
  else if clauseHasVar var res
       then if elem res cs
            then do putStrLn $ concat [show orig_res, " (duplicate in bucket: ", show var, ")"]
                    pure orig_buks
            else do putStrLn $ concat [show orig_res, " (adding to bucket: ", show var, ")"]
                    pure $ (Bucket var (res : cs)) : bs
       else pure (Bucket var cs) `consM` bucketsInsertResolvent orig_res bs
  where orig_res = (Resolvent p1 p2 res)
        orig_buks = (Bucket var cs) : bs

bucketsInsertResolvents :: [Resolvent] -> [Bucket] -> IO [Bucket]
bucketsInsertResolvents [] bs = pure bs
bucketsInsertResolvents (r:rs) bs = do
  new_bs <- (bucketsInsertResolvent r bs)
  bucketsInsertResolvents rs new_bs

-- Skips trivial resolvent clauses.
resolveBuckets :: [Bucket] -> IO [Bucket]
resolveBuckets [] = pure []
resolveBuckets (b:bs) = do
  let rs = resolveAll (buk_var b) (buk_clauses b)
  new_bs <- bucketsInsertResolvents rs bs
  rest <- resolveBuckets new_bs
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

solve_dp :: CNF -> [Variable] -> IO ()
solve_dp cnf var_order = do
  putStr "Initial CNF: "
  print cnf
  newline

  putStr "Variable Order: "
  print var_order
  newline

  let init_buks = fillBuckets var_order (cnf_clauses cnf)
  putStrLn "Initial Buckets: "
  mapM_ print init_buks
  newline

  putStrLn "Deriving resolvents..."
  res_buks <- resolveBuckets init_buks
  let res_cnt =
        (sum $ map (length . buk_clauses) res_buks)
        - (cnf_n_clauses cnf)
  putStr $ "Resolvents added to buckets: " ++ show res_cnt
  newline; newline

  putStrLn "Resolved Buckets: "
  mapM_ print res_buks
  newline

  let solution = extractSolution res_buks
  case solution of
    Nothing   -> putStrLn "UNSAT"
    Just lits -> putStr $ "SAT: " ++ (show lits) ++ "\n"

-- Main ------------------------------------------------------------------------

data Config = Config
  { conf_cnf_file :: String
  , conf_var_order :: String
  } deriving (Show)

configParser :: Parser Config
configParser = Config
  <$> strArgument
  ( metavar "CNF_FILE"
    <> value "--"
    <> showDefault
    <> help "Filename of input DIMACS CNF file." )
  <*> strOption
  ( short 'R'
    <> long "order"
    <> value "numeric"
    <> showDefault
    <> help "Variable ordering strategy." )

main :: IO ()
main = do
  config <- execParser opts

  let vo_func = case map toLower (conf_var_order config) of
                  "numeric" -> varOrderNumeric
                  "fewest"  -> varOrderFewestClauses
                  "jw"      -> varOrderJeroslowWang
                  _         -> trace "error: invalid variable order argument"
                                     varOrderNumeric

  dimacs_cnf <- case conf_cnf_file config of
                  "--" -> getContents
                  file -> readFile file

  let maybe_cnf = parseDIMACS dimacs_cnf
  case maybe_cnf of
    Nothing  -> putStrLn "error: invalid CNF"
    Just cnf -> do
      let var_order = (vo_func cnf) ++ [0]
      solve_dp cnf var_order

  where opts = info (configParser <**> helper)
               ( fullDesc
                 <> header ( "sat-dp - SAT solver using the DP algorithm"
                          ++ " implemented with bucket elimination." ) )
