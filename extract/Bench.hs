{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Blaze.ByteString.Builder as Blaze
import qualified Blaze.ByteString.Builder.Char8 as Blaze
import           Criterion.Main
import qualified Data.ByteString.Builder as BB
import           Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as LBS
import           Data.List (foldl')
import           Data.Monoid ((<>))
import           Test.QuickCheck.Arbitrary
import           Test.QuickCheck.Gen
import           Test.QuickCheck.Random
import qualified Text.Show.ByteString as BS

showStr :: [Integer] -> ByteString
showStr = BS.pack . concatMap show

showByteString :: [Integer] -> ByteString
showByteString = foldl' (<>) "" . map (BS.pack . show)

showPutM :: [Integer] -> ByteString
showPutM = LBS.toStrict . BS.show . go
  where
    go [] = return ()
    go (x:xs) = BS.showp x >> go xs


showByteStringBuilder :: [Integer] -> ByteString
showByteStringBuilder = LBS.toStrict . BB.toLazyByteString . go
  where
    go [] = mempty
    go (x:xs) = BB.integerDec x <> go xs

showBlazeBuilder :: [Integer] -> ByteString
showBlazeBuilder = Blaze.toByteString . go
  where
    go [] = mempty
    go (x:xs) = Blaze.fromShow x  <> go xs

main :: IO ()
main = defaultMain
  [
  bgroup "[Integer]" $
    map (\i ->
      let sz = 10^i
          inp = take sz is
      in bgroup (show sz)
         [ bench "(++) . show" (nf showStr inp)
         --, bench "(<>) . show" (nf showByteString (if i < 6 then inp else []))
         , bench "putM" (nf showPutM inp)
         , bench "bytestring-builder" (nf showByteStringBuilder inp)
         , bench "blaze-builder" (nf showBlazeBuilder inp)
         ]
    )
    [1..6 :: Integer]
  ]
  where

{-
Running 1 benchmarks...
Benchmark bench: RUNNING...
benchmarking [Integer]/10/(++) . show
time                 357.2 ns   (348.5 ns .. 370.7 ns)
                     0.992 R²   (0.987 R² .. 0.996 R²)
mean                 370.0 ns   (361.5 ns .. 382.1 ns)
std dev              33.85 ns   (26.68 ns .. 43.67 ns)
variance introduced by outliers: 88% (severely inflated)

benchmarking [Integer]/10/(<>) . show
time                 562.1 ns   (540.2 ns .. 595.3 ns)
                     0.989 R²   (0.976 R² .. 0.999 R²)
mean                 551.2 ns   (542.4 ns .. 568.8 ns)
std dev              40.71 ns   (25.53 ns .. 71.47 ns)
variance introduced by outliers: 82% (severely inflated)

benchmarking [Integer]/10/putM
time                 684.2 ns   (648.9 ns .. 714.4 ns)
                     0.988 R²   (0.983 R² .. 0.994 R²)
mean                 650.1 ns   (633.3 ns .. 673.3 ns)
std dev              63.57 ns   (51.97 ns .. 86.39 ns)
variance introduced by outliers: 89% (severely inflated)

benchmarking [Integer]/10/bytestring-builder
time                 611.9 ns   (598.9 ns .. 633.3 ns)
                     0.984 R²   (0.973 R² .. 0.994 R²)
mean                 668.1 ns   (643.7 ns .. 702.3 ns)
std dev              95.74 ns   (76.91 ns .. 121.8 ns)
variance introduced by outliers: 95% (severely inflated)

benchmarking [Integer]/10/blaze-builder
time                 713.5 ns   (671.1 ns .. 748.7 ns)
                     0.986 R²   (0.979 R² .. 0.996 R²)
mean                 662.1 ns   (648.7 ns .. 687.5 ns)
std dev              58.40 ns   (41.08 ns .. 86.22 ns)
variance introduced by outliers: 87% (severely inflated)

benchmarking [Integer]/100/(++) . show
time                 4.136 μs   (3.970 μs .. 4.299 μs)
                     0.989 R²   (0.985 R² .. 0.993 R²)
mean                 4.047 μs   (3.909 μs .. 4.179 μs)
std dev              445.9 ns   (381.7 ns .. 529.1 ns)
variance introduced by outliers: 90% (severely inflated)

benchmarking [Integer]/100/(<>) . show
time                 5.493 μs   (5.385 μs .. 5.678 μs)
                     0.996 R²   (0.993 R² .. 0.999 R²)
mean                 5.447 μs   (5.406 μs .. 5.517 μs)
std dev              182.0 ns   (115.0 ns .. 298.6 ns)
variance introduced by outliers: 42% (moderately inflated)

benchmarking [Integer]/100/putM
time                 4.724 μs   (4.408 μs .. 5.070 μs)
                     0.978 R²   (0.970 R² .. 0.993 R²)
mean                 4.614 μs   (4.462 μs .. 4.840 μs)
std dev              602.4 ns   (457.0 ns .. 761.4 ns)
variance introduced by outliers: 92% (severely inflated)

benchmarking [Integer]/100/bytestring-builder
time                 5.018 μs   (4.801 μs .. 5.261 μs)
                     0.988 R²   (0.984 R² .. 0.993 R²)
mean                 4.819 μs   (4.663 μs .. 4.982 μs)
std dev              518.1 ns   (443.4 ns .. 635.9 ns)
variance introduced by outliers: 89% (severely inflated)

benchmarking [Integer]/100/blaze-builder
time                 4.514 μs   (4.504 μs .. 4.525 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 4.527 μs   (4.510 μs .. 4.550 μs)
std dev              67.80 ns   (50.64 ns .. 90.94 ns)
variance introduced by outliers: 13% (moderately inflated)

benchmarking [Integer]/1000/(++) . show
time                 43.41 μs   (42.68 μs .. 44.12 μs)
                     0.996 R²   (0.994 R² .. 0.998 R²)
mean                 43.43 μs   (42.26 μs .. 44.25 μs)
std dev              3.295 μs   (2.453 μs .. 4.484 μs)
variance introduced by outliers: 74% (severely inflated)

benchmarking [Integer]/1000/(<>) . show
time                 82.38 μs   (79.54 μs .. 86.72 μs)
                     0.971 R²   (0.956 R² .. 0.983 R²)
mean                 92.63 μs   (87.29 μs .. 99.70 μs)
std dev              19.36 μs   (15.63 μs .. 24.85 μs)
variance introduced by outliers: 96% (severely inflated)

benchmarking [Integer]/1000/putM
time                 40.37 μs   (40.30 μs .. 40.45 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 40.47 μs   (40.29 μs .. 40.70 μs)
std dev              668.8 ns   (488.7 ns .. 930.4 ns)
variance introduced by outliers: 12% (moderately inflated)

benchmarking [Integer]/1000/bytestring-builder
time                 42.19 μs   (42.08 μs .. 42.36 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 42.36 μs   (42.13 μs .. 42.63 μs)
std dev              858.4 ns   (665.8 ns .. 1.079 μs)
variance introduced by outliers: 17% (moderately inflated)

benchmarking [Integer]/1000/blaze-builder
time                 44.36 μs   (44.20 μs .. 44.51 μs)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 45.47 μs   (44.80 μs .. 47.27 μs)
std dev              3.377 μs   (1.204 μs .. 5.716 μs)
variance introduced by outliers: 73% (severely inflated)

benchmarking [Integer]/10000/(++) . show
time                 665.0 μs   (660.3 μs .. 670.2 μs)
                     0.999 R²   (0.999 R² .. 0.999 R²)
mean                 666.4 μs   (659.7 μs .. 674.6 μs)
std dev              25.75 μs   (20.86 μs .. 32.12 μs)
variance introduced by outliers: 30% (moderately inflated)

benchmarking [Integer]/10000/(<>) . show
time                 2.956 ms   (2.926 ms .. 2.988 ms)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 2.963 ms   (2.939 ms .. 2.990 ms)
std dev              80.77 μs   (66.57 μs .. 102.5 μs)
variance introduced by outliers: 13% (moderately inflated)

benchmarking [Integer]/10000/putM
time                 447.3 μs   (444.8 μs .. 449.7 μs)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 449.1 μs   (445.5 μs .. 453.3 μs)
std dev              12.99 μs   (9.988 μs .. 17.43 μs)
variance introduced by outliers: 21% (moderately inflated)

benchmarking [Integer]/10000/bytestring-builder
time                 469.0 μs   (467.0 μs .. 471.2 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 468.5 μs   (465.5 μs .. 471.8 μs)
std dev              11.29 μs   (9.162 μs .. 14.23 μs)
variance introduced by outliers: 15% (moderately inflated)

benchmarking [Integer]/10000/blaze-builder
time                 523.2 μs   (489.7 μs .. 559.1 μs)
                     0.977 R²   (0.967 R² .. 0.989 R²)
mean                 544.9 μs   (518.8 μs .. 580.6 μs)
std dev              94.32 μs   (66.95 μs .. 132.3 μs)
variance introduced by outliers: 91% (severely inflated)

benchmarking [Integer]/100000/(++) . show
time                 8.257 ms   (7.612 ms .. 9.227 ms)
                     0.933 R²   (0.888 R² .. 0.970 R²)
mean                 8.898 ms   (8.373 ms .. 9.449 ms)
std dev              1.480 ms   (1.172 ms .. 2.126 ms)
variance introduced by outliers: 77% (severely inflated)

benchmarking [Integer]/100000/(<>) . show
time                 335.7 ms   (318.1 ms .. 350.6 ms)
                     0.999 R²   (0.997 R² .. 1.000 R²)
mean                 329.3 ms   (320.9 ms .. 333.9 ms)
std dev              8.081 ms   (2.107 ms .. 10.78 ms)
variance introduced by outliers: 16% (moderately inflated)

benchmarking [Integer]/100000/putM
time                 4.952 ms   (4.568 ms .. 5.446 ms)
                     0.954 R²   (0.929 R² .. 0.977 R²)
mean                 5.350 ms   (5.124 ms .. 5.738 ms)
std dev              862.1 μs   (529.2 μs .. 1.555 ms)
variance introduced by outliers: 81% (severely inflated)

benchmarking [Integer]/100000/bytestring-builder
time                 4.709 ms   (4.565 ms .. 4.926 ms)
                     0.986 R²   (0.974 R² .. 0.995 R²)
mean                 4.726 ms   (4.634 ms .. 4.855 ms)
std dev              341.9 μs   (273.7 μs .. 445.1 μs)
variance introduced by outliers: 46% (moderately inflated)

benchmarking [Integer]/100000/blaze-builder
time                 4.855 ms   (4.737 ms .. 4.948 ms)
                     0.994 R²   (0.988 R² .. 0.997 R²)
mean                 4.862 ms   (4.781 ms .. 4.966 ms)
std dev              287.6 μs   (227.1 μs .. 397.9 μs)
variance introduced by outliers: 37% (moderately inflated)

benchmarking [Integer]/1000000/(++) . show
time                 82.51 ms   (75.79 ms .. 89.71 ms)
                     0.980 R²   (0.939 R² .. 0.996 R²)
mean                 80.39 ms   (76.45 ms .. 85.57 ms)
std dev              6.922 ms   (5.278 ms .. 9.301 ms)
variance introduced by outliers: 28% (moderately inflated)

benchmarking [Integer]/1000000/(<>) . show
time                 31.08 s    (28.75 s .. 32.86 s)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 31.74 s    (31.20 s .. 32.15 s)
std dev              621.1 ms   (0.0 s .. 705.3 ms)
variance introduced by outliers: 19% (moderately inflated)

benchmarking [Integer]/1000000/putM
time                 40.95 ms   (36.80 ms .. 43.91 ms)
                     0.984 R²   (0.972 R² .. 0.993 R²)
mean                 48.38 ms   (46.19 ms .. 52.22 ms)
std dev              5.463 ms   (3.303 ms .. 8.326 ms)
variance introduced by outliers: 41% (moderately inflated)

benchmarking [Integer]/1000000/bytestring-builder
time                 43.11 ms   (42.56 ms .. 44.52 ms)
                     0.997 R²   (0.991 R² .. 1.000 R²)
mean                 43.15 ms   (42.77 ms .. 44.08 ms)
std dev              1.075 ms   (403.4 μs .. 1.814 ms)

benchmarking [Integer]/1000000/blaze-builder
time                 57.33 ms   (49.31 ms .. 65.16 ms)
                     0.966 R²   (0.940 R² .. 0.986 R²)
mean                 50.03 ms   (47.41 ms .. 53.56 ms)
std dev              5.620 ms   (4.237 ms .. 7.303 ms)
variance introduced by outliers: 44% (moderately inflated)

Benchmark bench: FINISH
-}
