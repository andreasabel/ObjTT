-- | Type checker for objective type theory.

module Main where

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import ObjTT.Abs   ( Decl )
import ObjTT.Lex   ( Token, mkPosToken )
import ObjTT.Par   ( pListDecl, myLexer )
import ObjTT.Print ( Print, printTree )

import Check (checkDecls, runChecker)

type Err        = Either String
type ParseFun a = [Token] -> Err a
type Verbosity  = Int

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    []         -> run =<< getContents
    fs         -> mapM_ runFile fs

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    ]

runFile :: FilePath -> IO ()
runFile f = do
  putStrLn f
  run =<< readFile f

run :: String -> IO ()
run s =
  case pListDecl ts of
    Left err -> do
      putStrLn "\nParse              Failed...\n"
      putStrLn "Tokens:"
      mapM_ (putStr . showPosToken . mkPosToken) ts
      putStrLn err
      exitFailure
    Right tree -> do
      check tree
  where
  ts = myLexer s
  showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

check :: [Decl] -> IO ()
check ds =
  case runChecker $ checkDecls ds of
    Left err -> putStrLn "Oh, no!!" >> print err
    Right () -> putStrLn "Yes!!!!"
