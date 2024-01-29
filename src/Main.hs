-- File generated by the BNF Converter (bnfc 2.9.5).

-- | Program to test parser.

module Main where

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import ObjTT.Abs   ( Decl )
import ObjTT.Lex   ( Token, mkPosToken )
import ObjTT.Par   ( pListDecl, myLexer )
import ObjTT.Print ( Print, printTree )

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> getContents >>= run pListDecl
    fs         -> mapM_ (runFile pListDecl) fs

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    ]

runFile :: (Print a, Show a) => ParseFun a -> FilePath -> IO ()
runFile v p f = do
  putStrLn f
  readFile f >>= run v p

run :: (Print a, Show a) => ParseFun a -> String -> IO ()
run p s =
  case p ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      mapM_ (putStr . showPosToken . mkPosToken) ts
      putStrLn err
      exitFailure
    Right tree -> do
      check tree
  where
  ts = myLexer s
  showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

check :: [Decl] -> IO ()
check = _
