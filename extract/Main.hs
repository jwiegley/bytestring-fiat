module Main where

import ByteStringExt

main :: IO ()
main = do
    let h0 = emptyHeap
    let (h1, addr) = allocHeap h0 (of_nat 100)
    print $ to_nat0 addr
    let (h2, addr) = allocHeap h1 (of_nat 200)
    print $ to_nat0 addr
    let h3 = pokeHeap h2 (of_nat 105) 'a'
    let (h4, val) = peekHeap h3 (of_nat 105)
    print val

    let b0 = emptyBS h0
    let b1 = consBS h0 b0 'a'
    let b2 = consBS h0 b1 'b'
    let b3 = consBS h0 b2 'c'
    let (b4, mres1) = unconsBS h0 b3
    let (b5, mres2) = unconsBS h0 b4
    print mres1
    print mres2
