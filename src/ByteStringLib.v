Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.Computation.FixComp
  ByteString.Memory
  ByteString.ByteString.

(************************************************************************
 ** Semantics of the Haskell ByteString library in Fiat.               **
 ************************************************************************)

Definition singleton_Spec (w : Word) : Comp ByteString :=
  xs  <- callCons ByteStringSpec emptyS;
  res <- callMeth ByteStringSpec consS xs w;
  ret (fst res).

(*
Definition pack_Spec (xs : list Word) : Comp ByteString :=
Definition unpack_Spec (bs : ByteString) : Comp (ByteString * list Word) :=
Definition snoc (bs : ByteString) (w : Word) : Comp (ByteString * unit) :=
*)

Import LeastFixedPointFun.

Definition foldr_Spec {A} :
  ByteString -> (Word -> A -> A) -> A -> Comp (ByteString * A) :=
  LeastFixedPoint (fDom := [ByteString; Word -> A -> A; A])
                  (fCod := ByteString * A)
    (fun rec (bs : ByteString) (f : Word -> A -> A) (z : A) =>
       p <- uncons bs;
       Ifopt snd p as w
       Then bs' <- rec (fst p) f z;
            ret (fst bs', f w (snd bs'))
       Else ret (bs, z)).

(*
append :: ByteString -> ByteString -> ByteString
head :: ByteString -> Word
unsnoc :: ByteString -> Maybe (ByteString, Word)
last :: ByteString -> Word
*)

Definition tail_Spec (bs : ByteString) : Comp (ByteString * bool) :=
  p <- uncons bs;
  ret (Ifopt snd p as w
       Then (fst p, true)
       Else (bs, false)).

(*
init :: ByteString -> ByteString
null :: ByteString -> Bool
length :: ByteString -> Int
map :: (Word -> Word) -> ByteString -> ByteString
reverse :: ByteString -> ByteString
intersperse :: Word -> ByteString -> ByteString
intercalate :: ByteString -> [ByteString] -> ByteString
transpose :: [ByteString] -> [ByteString]
foldl :: (a -> Word -> a) -> a -> ByteString -> a
foldl' :: (a -> Word -> a) -> a -> ByteString -> a
foldl1 :: (Word -> Word -> Word) -> ByteString -> Word
foldl1' :: (Word -> Word -> Word) -> ByteString -> Word
foldr :: (Word -> a -> a) -> a -> ByteString -> a
foldr' :: (Word -> a -> a) -> a -> ByteString -> a
foldr1 :: (Word -> Word -> Word) -> ByteString -> Word
foldr1' :: (Word -> Word -> Word) -> ByteString -> Word
concat :: [ByteString] -> ByteString
concatMap :: (Word -> ByteString) -> ByteString -> ByteString
any :: (Word -> Bool) -> ByteString -> Bool
all :: (Word -> Bool) -> ByteString -> Bool
maximum :: ByteString -> Word
minimum :: ByteString -> Word
scanl :: (Word -> Word -> Word) -> Word -> ByteString -> ByteString
scanl1 :: (Word -> Word -> Word) -> ByteString -> ByteString
scanr :: (Word -> Word -> Word) -> Word -> ByteString -> ByteString
scanr1 :: (Word -> Word -> Word) -> ByteString -> ByteString
mapAccumL :: (acc -> Word -> (acc, Word)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR :: (acc -> Word -> (acc, Word)) -> acc -> ByteString -> (acc, ByteString)
replicate :: Int -> Word -> ByteString
unfoldr :: (a -> Maybe (Word, a)) -> a -> ByteString
unfoldrN :: Int -> (a -> Maybe (Word, a)) -> a -> (ByteString, Maybe a)
take :: Int -> ByteString -> ByteString
drop :: Int -> ByteString -> ByteString
splitAt :: Int -> ByteString -> (ByteString, ByteString)
takeWhile :: (Word -> Bool) -> ByteString -> ByteString
dropWhile :: (Word -> Bool) -> ByteString -> ByteString
span :: (Word -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd :: (Word -> Bool) -> ByteString -> (ByteString, ByteString)
break :: (Word -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd :: (Word -> Bool) -> ByteString -> (ByteString, ByteString)
group :: ByteString -> [ByteString]
groupBy :: (Word -> Word -> Bool) -> ByteString -> [ByteString]
inits :: ByteString -> [ByteString]
tails :: ByteString -> [ByteString]
split :: Word -> ByteString -> [ByteString]
splitWith :: (Word -> Bool) -> ByteString -> [ByteString]
isPrefixOf :: ByteString -> ByteString -> Bool
isSuffixOf :: ByteString -> ByteString -> Bool
isInfixOf :: ByteString -> ByteString -> Bool
breakSubstring :: ByteString -> ByteString -> (ByteString, ByteString)
findSubstring :: ByteString -> ByteString -> Maybe Int
findSubstrings :: ByteString -> ByteString -> [Int]
elem :: Word -> ByteString -> Bool
notElem :: Word -> ByteString -> Bool
find :: (Word -> Bool) -> ByteString -> Maybe Word
filter :: (Word -> Bool) -> ByteString -> ByteString
partition :: (Word -> Bool) -> ByteString -> (ByteString, ByteString)
index :: ByteString -> Int -> Word
elemIndex :: Word -> ByteString -> Maybe Int
elemIndices :: Word -> ByteString -> [Int]
elemIndexEnd :: Word -> ByteString -> Maybe Int
findIndex :: (Word -> Bool) -> ByteString -> Maybe Int
findIndices :: (Word -> Bool) -> ByteString -> [Int]
count :: Word -> ByteString -> Int
zip :: ByteString -> ByteString -> [(Word, Word)]
zipWith :: (Word -> Word -> a) -> ByteString -> ByteString -> [a]
unzip :: [(Word, Word)] -> (ByteString, ByteString)
sort :: ByteString -> ByteString
copy :: ByteString -> ByteString
*)

(*
packCString :: CString -> IO ByteString
packCStringLen :: CStringLen -> IO ByteString
useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
getLine :: IO ByteString
getContents :: IO ByteString
putStr :: ByteString -> IO ()
putStrLn :: ByteString -> IO ()
interact :: (ByteString -> ByteString) -> IO ()
readFile :: FilePath -> IO ByteString
writeFile :: FilePath -> ByteString -> IO ()
appendFile :: FilePath -> ByteString -> IO ()
hGetLine :: Handle -> IO ByteString
hGetContents :: Handle -> IO ByteString
hGet :: Handle -> Int -> IO ByteString
hGetSome :: Handle -> Int -> IO ByteString
hGetNonBlocking :: Handle -> Int -> IO ByteString
hPut :: Handle -> ByteString -> IO ()
hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutStr :: Handle -> ByteString -> IO ()
hPutStrLn :: Handle -> ByteString -> IO ()
*)

(*
breakByte :: Word -> ByteString -> (ByteString, ByteString)
*)
