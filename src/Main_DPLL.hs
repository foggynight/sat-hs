-- -*- eval: (setq haskell-process-args-cabal-repl '("sat-dpll")) -*-
-- ... or: M-x haskell-session-change-target, sat-dpll

module Main where

import Data.Array (Array, listArray, (!))
import Data.Char (toLower)
import Data.IORef
import Debug.Trace (trace)
import Options.Applicative
import System.IO.Unsafe (unsafePerformIO)

import CNF
import DIMACS
import Util
import VarOrder

-- DPLL ------------------------------------------------------------------------

{-# NOINLINE dpll_count #-}
dpll_count :: IORef Int
dpll_count = unsafePerformIO (newIORef 0)

dpll :: Array Int Variable -> [Clause] -> Int -> IO (Maybe [Literal])
dpll _ [] _ = do
  modifyIORef' dpll_count (+ 1)
  pure $ Just []
dpll var_order clauses depth = do
  let print_prefix = concat $ replicate (depth - 1) "    "
  if elem [] clauses
  then do putStrLn (print_prefix ++ "BACKTRACK: Found empty clause.")
          modifyIORef' dpll_count (+ 1)
          pure Nothing
  else do
    let var = var_order ! depth

    let clauses_pos = (conditionClauses var clauses)
    putStrLn $ concat [print_prefix, " ", show var, " -> ", show clauses_pos]
    next_pos <- dpll var_order clauses_pos (depth + 1)

    if next_pos /= Nothing
    then pure $ Just var `consM` next_pos
    else do
      let clauses_neg = (conditionClauses (-var) clauses)
      putStrLn $ concat [print_prefix, show (-var), " -> ", show clauses_neg]
      next_neg <- dpll var_order clauses_neg (depth + 1)

      if next_neg /= Nothing
      then pure $ Just (-var) `consM` next_neg
      else pure $ Nothing

solve_dpll :: CNF -> [Variable] -> IO ()
solve_dpll cnf var_order = do
  putStrLn $ "Initial CNF: " ++ show cnf
  newline

  putStrLn $ "Variable Order: " ++ show var_order
  newline

  putStrLn $ "Searching for satisfying assignment..."
  result <- dpll
        (listArray (1, (cnf_n_vars cnf)) var_order)
        (cnf_clauses cnf)
        1
  dpll_count' <- readIORef dpll_count
  putStrLn $ "Assignments checked: " ++ show dpll_count'
  newline

  case result of
    Nothing   -> putStrLn "UNSAT"
    Just lits -> putStrLn $ "SAT: " ++ show lits

-- Main ------------------------------------------------------------------------

data Config = Config
  { conf_var_order :: String
  , conf_cnf_file :: String
  } deriving (Show)

configParser :: Parser Config
configParser = Config
  <$> strOption
  ( short 'R'
    <> long "order"
    <> value "numeric"
    <> showDefault
    <> help "Variable ordering strategy." )
  <*> strArgument
  ( metavar "CNF_FILE"
    <> value "--"
    <> showDefault
    <> help "Filename of input DIMACS CNF file." )

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
      let var_order = vo_func cnf
      solve_dpll cnf var_order

  where opts = info (configParser <**> helper)
               ( fullDesc
                 <> header ( "SatDP - SAT solver using DP algorithm implemented"
                          ++ " with bucket elimination." ) )
