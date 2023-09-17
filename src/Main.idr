module Main

-- import Chapter1
import Chapter2

main : IO ()
main = do
  putStrLn "Tests"
  putStrLn "ppmHeaderExample \{show ppmHeaderExample}"
  putStrLn "ppmPixelExample \{show ppmPixelExample}"
  putStrLn "ppmLongLines \{show ppmLongLines}"
