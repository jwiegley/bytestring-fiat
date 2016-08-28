module Main where

import HeapFMapExt

main :: IO ()
main = do
    let h0 = emptyHeap
    let (h1, addr) = allocHeap h0 (of_nat 100)
    print $ to_nat0 addr
    let (h2, addr) = allocHeap h1 (of_nat 200)
    print $ to_nat0 addr
    let h3 = pokeHeap h2 (of_nat 105) (of_nat 200)
    let (h4, val) = peekHeap h3 (of_nat 105)
    print $ to_nat0 val
