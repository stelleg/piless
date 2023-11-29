module Main where
import System.Environment
import Parse
import Piless

main = do
  [file] <- getArgs
  e <- parseFile file
  putStr "Type to synthesize: "
  print e
  case synthesize 5 e of
    Left s -> putStrLn s
    Right xs -> mapM_ print xs
