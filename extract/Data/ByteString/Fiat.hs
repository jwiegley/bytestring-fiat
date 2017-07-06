{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PackageImports #-}

module Data.ByteString.Fiat (

        -- * The @ByteString@ type
        ByteString(..),         -- abstract, instances: Eq, Ord, Show, Read, Data, Typeable, Monoid

        -- * Introducing and eliminating 'ByteString's
        empty,                  -- :: ByteString
        singleton,              -- :: Word8   -> ByteString
        pack,                   -- :: [Word8] -> ByteString
        unpack,                 -- :: ByteString -> [Word8]

        -- * Basic interface
        cons,                   -- :: Word8 -> ByteString -> ByteString
        snoc,                   -- :: ByteString -> Word8 -> ByteString
        append,                 -- :: ByteString -> ByteString -> ByteString
        head,                   -- :: ByteString -> Word8
        uncons,                 -- :: ByteString -> Maybe (Word8, ByteString)
        unsnoc,                 -- :: ByteString -> Maybe (ByteString, Word8)
        last,                   -- :: ByteString -> Word8
        tail,                   -- :: ByteString -> ByteString
        init,                   -- :: ByteString -> ByteString
        null,                   -- :: ByteString -> Bool
        length,                 -- :: ByteString -> Int

        -- * Transforming ByteStrings
        map,                    -- :: (Word8 -> Word8) -> ByteString -> ByteString
        reverse,                -- :: ByteString -> ByteString
        intersperse,            -- :: Word8 -> ByteString -> ByteString
        intercalate,            -- :: ByteString -> [ByteString] -> ByteString
        transpose,              -- :: [ByteString] -> [ByteString]

        -- * Reducing 'ByteString's (folds)
        foldl,                  -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl',                 -- :: (a -> Word8 -> a) -> a -> ByteString -> a
        foldl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldl1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        foldr,                  -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr',                 -- :: (Word8 -> a -> a) -> a -> ByteString -> a
        foldr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
        foldr1',                -- :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8

        -- ** Special folds
        concat,                 -- :: [ByteString] -> ByteString
        concatMap,              -- :: (Word8 -> ByteString) -> ByteString -> ByteString
        any,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        all,                    -- :: (Word8 -> Bool) -> ByteString -> Bool
        maximum,                -- :: ByteString -> Word8
        minimum,                -- :: ByteString -> Word8

        -- * Building ByteStrings
        -- ** Scans
        scanl,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanl1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
        scanr,                  -- :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
        scanr1,                 -- :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString

        -- ** Accumulating maps
        mapAccumL,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
        mapAccumR,              -- :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)

        -- ** Generating and unfolding ByteStrings
        replicate,              -- :: Int -> Word8 -> ByteString
        unfoldr,                -- :: (a -> Maybe (Word8, a)) -> a -> ByteString
        unfoldrN,               -- :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)

        -- * Substrings

        -- ** Breaking strings
        take,                   -- :: Int -> ByteString -> ByteString
        drop,                   -- :: Int -> ByteString -> ByteString
        splitAt,                -- :: Int -> ByteString -> (ByteString, ByteString)
        takeWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        dropWhile,              -- :: (Word8 -> Bool) -> ByteString -> ByteString
        span,                   -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        spanEnd,                -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        break,                  -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        breakEnd,               -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
        group,                  -- :: ByteString -> [ByteString]
        groupBy,                -- :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
        inits,                  -- :: ByteString -> [ByteString]
        tails,                  -- :: ByteString -> [ByteString]
        stripPrefix,            -- :: ByteString -> ByteString -> Maybe ByteString
        stripSuffix,            -- :: ByteString -> ByteString -> Maybe ByteString

        -- ** Breaking into many substrings
        split,                  -- :: Word8 -> ByteString -> [ByteString]
        splitWith,              -- :: (Word8 -> Bool) -> ByteString -> [ByteString]

        -- * Predicates
        isPrefixOf,             -- :: ByteString -> ByteString -> Bool
        isSuffixOf,             -- :: ByteString -> ByteString -> Bool
        isInfixOf,              -- :: ByteString -> ByteString -> Bool

        -- ** Search for arbitrary substrings
        breakSubstring,         -- :: ByteString -> ByteString -> (ByteString,ByteString)
        findSubstring,          -- :: ByteString -> ByteString -> Maybe Int
        findSubstrings,         -- :: ByteString -> ByteString -> [Int]

        -- * Searching ByteStrings

        -- ** Searching by equality
        elem,                   -- :: Word8 -> ByteString -> Bool
        notElem,                -- :: Word8 -> ByteString -> Bool

        -- ** Searching with a predicate
        find,                   -- :: (Word8 -> Bool) -> ByteString -> Maybe Word8
        filter,                 -- :: (Word8 -> Bool) -> ByteString -> ByteString
        partition,              -- :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)

        -- * Indexing ByteStrings
        index,                  -- :: ByteString -> Int -> Word8
        elemIndex,              -- :: Word8 -> ByteString -> Maybe Int
        elemIndices,            -- :: Word8 -> ByteString -> [Int]
        elemIndexEnd,           -- :: Word8 -> ByteString -> Maybe Int
        findIndex,              -- :: (Word8 -> Bool) -> ByteString -> Maybe Int
        findIndices,            -- :: (Word8 -> Bool) -> ByteString -> [Int]
        count,                  -- :: Word8 -> ByteString -> Int

        -- * Zipping and unzipping ByteStrings
        zip,                    -- :: ByteString -> ByteString -> [(Word8,Word8)]
        zipWith,                -- :: (Word8 -> Word8 -> c) -> ByteString -> ByteString -> [c]
        unzip,                  -- :: [(Word8,Word8)] -> (ByteString,ByteString)

        -- * Ordered ByteStrings
        sort,                   -- :: ByteString -> ByteString

        -- * Low level conversions
        -- ** Copying ByteStrings
        copy,                   -- :: ByteString -> ByteString

        -- ** Packing 'CString's and pointers
        packCString,            -- :: CString -> IO ByteString
        packCStringLen,         -- :: CStringLen -> IO ByteString

        -- ** Using ByteStrings as 'CString's
        useAsCString,           -- :: ByteString -> (CString    -> IO a) -> IO a
        useAsCStringLen,        -- :: ByteString -> (CStringLen -> IO a) -> IO a

        -- * I\/O with 'ByteString's

        -- ** Standard input and output
        getLine,                -- :: IO ByteString
        getContents,            -- :: IO ByteString
        putStr,                 -- :: ByteString -> IO ()
        putStrLn,               -- :: ByteString -> IO ()
        interact,               -- :: (ByteString -> ByteString) -> IO ()

        -- ** Files
        readFile,               -- :: FilePath -> IO ByteString
        writeFile,              -- :: FilePath -> ByteString -> IO ()
        appendFile,             -- :: FilePath -> ByteString -> IO ()

        -- ** I\/O with Handles
        hGetLine,               -- :: Handle -> IO ByteString
        hGetContents,           -- :: Handle -> IO ByteString
        hGet,                   -- :: Handle -> Int -> IO ByteString
        hGetSome,               -- :: Handle -> Int -> IO ByteString
        hGetNonBlocking,        -- :: Handle -> Int -> IO ByteString
        hPut,                   -- :: Handle -> ByteString -> IO ()
        hPutNonBlocking,        -- :: Handle -> ByteString -> IO ByteString
        hPutStr,                -- :: Handle -> ByteString -> IO ()
        hPutStrLn,              -- :: Handle -> ByteString -> IO ()

        breakByte

  ) where

import qualified Prelude as P
import Prelude hiding           (reverse,head,tail,last,init,null
                                ,length,map,lines,foldl,foldr,unlines
                                ,concat,any,take,drop,splitAt,takeWhile
                                ,dropWhile,span,break,elem,filter,maximum
                                ,minimum,all,concatMap,foldl1,foldr1
                                ,scanl,scanl1,scanr,scanr1
                                ,readFile,writeFile,appendFile,replicate
                                ,getContents,getLine,putStr,putStrLn,interact
                                ,zip,zipWith,unzip,notElem)

import Data.Bits                (finiteBitSize, shiftL, (.|.), (.&.))

import Data.ByteString.Fiat.Internal
    hiding (IO, Ptr, Word, PS(..), singleton, id,
            empty, fmap, find, filter, partition, map)
import qualified Data.ByteString.Fiat.Internal as Internal

import qualified Data.List as List

import qualified "bytestring" Data.ByteString as BS
import Debug.Trace

import Data.Word                (Word8)
import Data.Maybe               (isJust)

import Control.Exception        (finally, bracket, assert, throwIO)
import Control.Monad            (when)

import Foreign.C.String         (CString, CStringLen)
import Foreign.C.Types          (CSize)
import Foreign.ForeignPtr       (ForeignPtr, withForeignPtr, touchForeignPtr,
                                 newForeignPtr)
import Foreign.ForeignPtr.Unsafe(unsafeForeignPtrToPtr)
import Foreign.Marshal.Alloc    (allocaBytes, finalizerFree)
import Foreign.Marshal.Array    (allocaArray)
import Foreign.Ptr
import Foreign.Storable         (Storable(..))

import System.IO                (stdin,stdout,hClose,hFileSize
                                ,hGetBuf,hPutBuf,openBinaryFile
                                ,IOMode(..))
import System.IO.Error          (mkIOError, illegalOperationErrorType)


import System.IO                (hGetBufNonBlocking, hPutBufNonBlocking)

import System.IO                (hGetBufSome)

import Data.IORef
import GHC.IO.Handle.Internals
import GHC.IO.Handle.Types
import GHC.IO.Buffer
import GHC.IO.BufferedIO as Buffered
import GHC.IO                   (unsafePerformIO, unsafeDupablePerformIO)
import Data.Char                (ord)
import Foreign.Marshal.Utils    (copyBytes)

import GHC.Prim                 (Word#)
import GHC.Base                 (build)
import GHC.Word hiding (Word8)

import Data.Data
import Data.Hashable
import Data.Semigroup (Semigroup(..))
import Data.String (IsString(..))


type ByteString = Internal.PS0

instance Eq Internal.PS0 where
    x == y = trace "== not translated" $ unwrap x == unwrap y
-- instance Data Internal.PS0 where
instance Ord Internal.PS0 where
    x `compare` y = trace "compare not translated" $ unwrap x `Prelude.compare` unwrap y
-- instance Read Internal.PS0 where
instance Show Internal.PS0 where
    show x = trace "show not translated" $ show (unwrap x)
instance IsString Internal.PS0 where
    fromString s = trace "fromString not translated" $ wrap (fromString s)
instance Semigroup Internal.PS0 where
    x <> y = trace "<> not translated" $ wrap (unwrap x <> unwrap y)
instance Monoid Internal.PS0 where
    mempty  = empty
    mappend = append

instance Hashable Internal.PS0 where
    hashWithSalt salt bs =
        trace "hashWithSalt not translated" $ hashWithSalt salt (unwrap bs)

pattern PS a b c <- Internal.MakePS0 a _ b c

empty :: ByteString
empty = Internal.ghcEmptyDSL'

singleton :: Word8 -> ByteString
singleton = Internal.ghcConsDSL' Internal.ghcEmptyDSL'



pack :: [Word8] -> ByteString
pack = Internal.ghcPackDSL'

unpack :: ByteString -> [Word8]
unpack = Internal.ghcUnpackDSL'

unwrap :: ByteString -> BS.ByteString
unwrap bs =
    let (bs', mres) = Internal.ghcUnconsDSL' bs in
    case mres of
        Nothing -> BS.empty
        Just c  -> BS.cons c (unwrap bs')

wrap :: BS.ByteString -> ByteString
wrap = BS.foldr' (flip Internal.ghcConsDSL') Internal.ghcEmptyDSL'

unpackFoldr :: ByteString -> (Word8 -> a -> a) -> a -> a
unpackFoldr bs k z = undefined

null :: ByteString -> Bool
null (PS _ _ l) = l == 0

length :: ByteString -> Int
length (PS _ _ l) = l


infixr 5 `cons`
infixl 5 `snoc`

cons :: Word8 -> ByteString -> ByteString
cons = flip Internal.ghcConsDSL'

snoc :: ByteString -> Word8 -> ByteString
snoc bs@(PS x s l) c = trace "snoc not translated" $ wrap (BS.snoc (unwrap bs) c)

head :: ByteString -> Word8
head bs@(PS x s l) = trace "head not translated" $ BS.head (unwrap bs)

tail :: ByteString -> ByteString
tail bs@(PS p s l) = trace "tail not translated" $ wrap (BS.tail (unwrap bs))

uncons :: ByteString -> Maybe (Word8, ByteString)
uncons bs = let (bs', mres) = Internal.ghcUnconsDSL' bs in fmap (, bs') mres

last :: ByteString -> Word8
last bs@(PS x s l) = trace "last not translated" $ BS.last (unwrap bs)

init :: ByteString -> ByteString
init bs@(PS p s l) = trace "init not translated" $ wrap (BS.init (unwrap bs))

unsnoc :: ByteString -> Maybe (ByteString, Word8)
unsnoc bs@(PS x s l) = trace "unsnoc not translated" $ fmap (bimap wrap id) (BS.unsnoc (unwrap bs))

append :: ByteString -> ByteString -> ByteString
append = Internal.ghcAppendDSL'


map :: (Word8 -> Word8) -> ByteString -> ByteString
map f bs@(PS fp s len) = trace "map not translated" $ wrap (BS.map f (unwrap bs))

reverse :: ByteString -> ByteString
reverse bs@(PS x s l) = trace "reverse not translated" $ wrap (BS.reverse (unwrap bs))

intersperse :: Word8 -> ByteString -> ByteString
intersperse c bs@(PS x s l) = trace "intersperse not translated" $ wrap (BS.intersperse c (unwrap bs))

transpose :: [ByteString] -> [ByteString]
transpose bs = trace "transpose not translated" $ fmap wrap (BS.transpose (fmap unwrap bs))

foldl :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl f z bs@(PS fp off len) = trace "foldl not translated" $ BS.foldl f z (unwrap bs)

foldl' :: (a -> Word8 -> a) -> a -> ByteString -> a
foldl' f v bs@(PS fp off len) = trace "foldl' not translated" $ BS.foldl' f v (unwrap bs)

foldr :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr k z bs@(PS fp off len) = trace "foldr not translated" $ BS.foldr k z (unwrap bs)

foldr' :: (Word8 -> a -> a) -> a -> ByteString -> a
foldr' k v bs@(PS fp off len) = trace "foldr' not translated" $ BS.foldr' k v (unwrap bs)

foldl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1 f bs = trace "foldl1 not translated" $ BS.foldl1 f (unwrap bs)

foldl1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldl1' f bs = trace "foldl1' not translated" $ BS.foldl1' f (unwrap bs)

foldr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1 f bs = trace "foldr1 not translated" $ BS.foldr1 f (unwrap bs)

foldr1' :: (Word8 -> Word8 -> Word8) -> ByteString -> Word8
foldr1' f bs = trace "foldr1' not translated" $ BS.foldr1' f (unwrap bs)

concat :: [ByteString] -> ByteString
concat bss = trace "concat not translated" $ wrap (BS.concat (fmap unwrap bss))

concatMap :: (Word8 -> ByteString) -> ByteString -> ByteString
concatMap f bs = trace "concatMap not translated" $ wrap (BS.concatMap (unwrap . f) (unwrap bs))


any :: (Word8 -> Bool) -> ByteString -> Bool
any f bs@(PS x s l) = trace "any not translated" $ BS.any f (unwrap bs)

all :: (Word8 -> Bool) -> ByteString -> Bool
all f bs@(PS x s l) = trace "all not translated" $ BS.all f (unwrap bs)

maximum :: ByteString -> Word8
maximum bs@(PS x s l) = trace "maximum not translated" $ BS.maximum (unwrap bs)

minimum :: ByteString -> Word8
minimum bs@(PS x s l) = trace "minimum not translated" $ BS.minimum (unwrap bs)

mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumL f acc bs@(PS fp o len) = trace "mapAccumL not translated" $ fmap wrap (BS.mapAccumL f acc (unwrap bs))

mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
mapAccumR f acc bs@(PS fp o len) = trace "mapAccumR not translated" $ fmap wrap (BS.mapAccumR f acc (unwrap bs))


scanl :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanl f v bs@(PS fp s len) = trace "scanl not translated" $ wrap (BS.scanl f v (unwrap bs))

scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanl1 f bs = trace "scanl1 not translated" $ wrap (BS.scanl1 f (unwrap bs))

scanr :: (Word8 -> Word8 -> Word8) -> Word8 -> ByteString -> ByteString
scanr f v bs@(PS fp s len) = trace "scanr not translated" $ wrap (BS.scanr f v (unwrap bs))

scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
scanr1 f bs = trace "scanr1 not translated" $ wrap (BS.scanr1 f (unwrap bs))

replicate :: Int -> Word8 -> ByteString
replicate w c = trace "replicate not translated" $ wrap (BS.replicate w c)

unfoldr :: (a -> Maybe (Word8, a)) -> a -> ByteString
unfoldr f x = trace "unfoldr not translated" $ wrap (BS.unfoldr f x)

bimap :: (a -> c) -> (b -> d) -> (a, b) -> (c, d)
bimap f g (x, y) = (f x, g y)

unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
unfoldrN i f x0 = trace "unfoldrN not translated" $ bimap wrap id (BS.unfoldrN i f x0)

take :: Int -> ByteString -> ByteString
take n bs@(PS x s l) = trace "take not translated" $ wrap (BS.take n (unwrap bs))

drop  :: Int -> ByteString -> ByteString
drop n bs@(PS x s l) = trace "drop not translated" $ wrap (BS.drop n (unwrap bs))

splitAt :: Int -> ByteString -> (ByteString, ByteString)
splitAt n bs@(PS x s l) = trace "splitAt not translated" $ bimap wrap wrap (BS.splitAt n (unwrap bs))

takeWhile :: (Word8 -> Bool) -> ByteString -> ByteString
takeWhile f bs = trace "takeWhile not translated" $ wrap (BS.takeWhile f (unwrap bs))

dropWhile :: (Word8 -> Bool) -> ByteString -> ByteString
dropWhile f bs = trace "dropWhile not translated" $ wrap (BS.dropWhile f (unwrap bs))


break :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p bs = trace "break not translated" $ bimap wrap wrap (BS.break p (unwrap bs))


breakByte :: Word8 -> ByteString -> (ByteString, ByteString)
breakByte c bs = trace "breakByte not translated" $ bimap wrap wrap (BS.breakByte c (unwrap bs))

breakEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p bs = trace "breakEnd not translated" $ bimap wrap wrap (BS.breakEnd p (unwrap bs))

span :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p bs = trace "span not translated" $ bimap wrap wrap (BS.span p (unwrap bs))

-- spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
-- spanByte c bs@(PS x s l) = trace "spanByte not translated" $ bimap wrap wrap (BS.spanByte c (unwrap bs))

spanEnd :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd  p bs = trace "spanEnd not translated" $ bimap wrap wrap (BS.spanEnd p (unwrap bs))

splitWith :: (Word8 -> Bool) -> ByteString -> [ByteString]
splitWith pred_ bs@(PS fp off len) = trace "splitWith not translated" $ fmap wrap (BS.splitWith pred_ (unwrap bs))

split :: Word8 -> ByteString -> [ByteString]
split w bs@(PS x s l) = trace "split not translated" $ fmap wrap (BS.split w (unwrap bs))

group :: ByteString -> [ByteString]
group bs = trace "group not translated" $ fmap wrap (BS.group (unwrap bs))

groupBy :: (Word8 -> Word8 -> Bool) -> ByteString -> [ByteString]
groupBy k bs = trace "groupBy not translated" $ fmap wrap (BS.groupBy k (unwrap bs))

intercalate :: ByteString -> [ByteString] -> ByteString
intercalate bs bss = trace "intercalate not translated" $ wrap (BS.intercalate (unwrap bs) (fmap unwrap bss))


-- intercalateWithByte :: Word8 -> ByteString -> ByteString -> ByteString
-- intercalateWithByte c bs1@(PS ffp s l) bs2@(PS fgp t m) = trace "intercalateWithByte not translated" $ wrap (BS.intercalateWithByte c (unwrap bs1) (unwrap bs2))

index :: ByteString -> Int -> Word8
index bs n = trace "index not translated" $ BS.index (unwrap bs) n

elemIndex :: Word8 -> ByteString -> Maybe Int
elemIndex c bs@(PS x s l) = trace "elemIndex not translated" $ BS.elemIndex c (unwrap bs)

elemIndexEnd :: Word8 -> ByteString -> Maybe Int
elemIndexEnd ch bs@(PS x s l) = trace "elemIndexEnd not translated" $ BS.elemIndexEnd ch (unwrap bs)

elemIndices :: Word8 -> ByteString -> [Int]
elemIndices w bs@(PS x s l) = trace "elemIndices not translated" $ BS.elemIndices w (unwrap bs)

count :: Word8 -> ByteString -> Int
count w bs@(PS x s m) = trace "count not translated" $ BS.count w (unwrap bs)

findIndex :: (Word8 -> Bool) -> ByteString -> Maybe Int
findIndex k bs@(PS x s l) = trace "findIndex not translated" $ BS.findIndex k (unwrap bs)

findIndices :: (Word8 -> Bool) -> ByteString -> [Int]
findIndices p bs = trace "findIndices not translated" $ BS.findIndices p (unwrap bs)

elem :: Word8 -> ByteString -> Bool
elem c bs = trace "elem not translated" $ BS.elem c (unwrap bs)

notElem :: Word8 -> ByteString -> Bool
notElem c bs = trace "notElem not translated" $ BS.notElem c (unwrap bs)

filter :: (Word8 -> Bool) -> ByteString -> ByteString
filter k bs@(PS x s l) = trace "filter not translated" $ wrap (BS.filter k (unwrap bs))

find :: (Word8 -> Bool) -> ByteString -> Maybe Word8
find f bs = trace "find not translated" $ BS.find f (unwrap bs)

partition :: (Word8 -> Bool) -> ByteString -> (ByteString, ByteString)
partition f bs = trace "partition not translated" $ bimap wrap wrap (BS.partition f (unwrap bs))

isPrefixOf :: ByteString -> ByteString -> Bool
isPrefixOf bs1@(PS x1 s1 l1) bs2@(PS x2 s2 l2) = trace "isPrefixOf not translated" $ BS.isPrefixOf (unwrap bs1) (unwrap bs2)

stripPrefix :: ByteString -> ByteString -> Maybe ByteString
stripPrefix bs1@(PS _ _ l1) bs2 = trace "stripPrefix not translated" $ fmap wrap (BS.stripPrefix (unwrap bs1) (unwrap bs2))

isSuffixOf :: ByteString -> ByteString -> Bool
isSuffixOf bs1@(PS x1 s1 l1) bs2@(PS x2 s2 l2) = trace "isSuffixOf not translated" $ BS.isSuffixOf (unwrap bs1) (unwrap bs2)

stripSuffix :: ByteString -> ByteString -> Maybe ByteString
stripSuffix bs1@(PS _ _ l1) bs2@(PS _ _ l2) = trace "stripSuffix not translated" $ fmap wrap (BS.stripSuffix (unwrap bs1) (unwrap bs2))

isInfixOf :: ByteString -> ByteString -> Bool
isInfixOf p s = trace "isInfixOf not translated" $ BS.isInfixOf (unwrap p) (unwrap s)

breakSubstring :: ByteString -- ^ String to search for
               -> ByteString -- ^ String to search in
               -> (ByteString,ByteString) -- ^ Head and tail of string broken at substring
breakSubstring pat bs = trace "breakSubstring not translated" $ bimap wrap wrap (BS.breakSubstring (unwrap pat) (unwrap bs))

findSubstring :: ByteString -- ^ String to search for.
              -> ByteString -- ^ String to seach in.
              -> Maybe Int
findSubstring pat src = trace "findSubstring not translated" $ BS.findSubstring (unwrap pat) (unwrap src)

findSubstrings :: ByteString -- ^ String to search for.
               -> ByteString -- ^ String to seach in.
               -> [Int]
findSubstrings pat src = trace "findSubstrings not translated" $ BS.findSubstrings (unwrap pat) (unwrap src)


zip :: ByteString -> ByteString -> [(Word8,Word8)]
zip ps qs = trace "zip not translated" $ BS.zip (unwrap ps) (unwrap qs)

zipWith :: (Word8 -> Word8 -> a) -> ByteString -> ByteString -> [a]
zipWith f ps qs = trace "zipWith not translated" $ BS.zipWith f (unwrap ps) (unwrap qs)

-- zipWith' :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
-- zipWith' f (PS fp s l) (PS fq t m) = trace "zipWith' not translated" $ wrap (BS.zipWith' (unwrap bs))

unzip :: [(Word8,Word8)] -> (ByteString,ByteString)
unzip ls = trace "unzip not translated" $ bimap wrap wrap (BS.unzip ls)


inits :: ByteString -> [ByteString]
inits bs@(PS x s l) = trace "inits not translated" $ fmap wrap (BS.inits (unwrap bs))

tails :: ByteString -> [ByteString]
tails p = trace "tails not translated" $ fmap wrap (BS.tails (unwrap p))


sort :: ByteString -> ByteString
sort bs@(PS input s l) = trace "sort not translated" $ wrap (BS.sort (unwrap bs))

useAsCString :: ByteString -> (CString -> IO a) -> IO a
useAsCString bs@(PS fp o l) action = trace "useAsCString not translated" $ BS.useAsCString (unwrap bs) action

useAsCStringLen :: ByteString -> (CStringLen -> IO a) -> IO a
useAsCStringLen p@(PS _ _ l) f = trace "useAsCStringLen not translated" $ BS.useAsCStringLen (unwrap p) f


packCString :: CString -> IO ByteString
packCString cstr = trace "packCString not translated" $ fmap wrap (BS.packCString cstr)

packCStringLen :: CStringLen -> IO ByteString
packCStringLen (cstr, len) = trace "packCStringLen not translated" $ fmap wrap (BS.packCStringLen (cstr, len))


copy :: ByteString -> ByteString
copy bs@(PS x s l) = trace "copy not translated" $ wrap (BS.copy (unwrap bs))

getLine :: IO ByteString
getLine = trace "getLine not translated" $ fmap wrap BS.getLine


hGetLine :: Handle -> IO ByteString
hGetLine h = trace "hGetLine not translated" $ fmap wrap (BS.hGetLine h)

-- mkPS :: RawBuffer Word8 -> Int -> Int -> IO ByteString
-- mkPS buf start end = trace "mkPS not translated" $ wrap (BS.mkPS (unwrap bs))

-- mkBigPS :: Int -> [ByteString] -> IO ByteString
-- mkBigPS _ pss = trace "mkBigPS not translated" $ wrap (BS.mkBigPS (unwrap bs))


hPut :: Handle -> ByteString -> IO ()
hPut h bs@(PS ps s l) = trace "hPut not translated" $ BS.hPut h (unwrap bs)

hPutNonBlocking :: Handle -> ByteString -> IO ByteString
hPutNonBlocking h bs@(PS ps s l) = trace "hPutNonBlocking not translated" $ fmap wrap (BS.hPutNonBlocking h (unwrap bs))

hPutStr :: Handle -> ByteString -> IO ()
hPutStr h bs = trace "hPutStr not translated" $ BS.hPutStr h (unwrap bs)

hPutStrLn :: Handle -> ByteString -> IO ()
hPutStrLn h bs = trace "hPutStrLn not translated" $ BS.hPutStrLn h (unwrap bs)

putStr :: ByteString -> IO ()
putStr bs = trace "putStr not translated" $ BS.putStr (unwrap bs)

putStrLn :: ByteString -> IO ()
putStrLn bs = trace "putStrLn not translated" $ BS.putStrLn (unwrap bs)

hGet :: Handle -> Int -> IO ByteString
hGet h i = trace "hGet not translated" $ fmap wrap (BS.hGet h i)

hGetNonBlocking :: Handle -> Int -> IO ByteString
hGetNonBlocking h i = trace "hGetNonBlocking not translated" $ fmap wrap (BS.hGetNonBlocking h i)

hGetSome :: Handle -> Int -> IO ByteString
hGetSome hh i = trace "hGetSome not translated" $ fmap wrap (BS.hGetSome hh i)

-- illegalBufferSize :: Handle -> String -> Int -> IO a
-- illegalBufferSize handle fn sz = trace "illegalBufferSize not translated" $ BS.illegalBufferSize (unwrap bs)

hGetContents :: Handle -> IO ByteString
hGetContents hnd = trace "hGetContents not translated" $ fmap wrap (BS.hGetContents hnd)

-- hGetContentsSizeHint :: Handle
--                      -> Int -- ^ first read size
--                      -> Int -- ^ initial buffer size increment
--                      -> IO ByteString
-- hGetContentsSizeHint hnd = trace "hGetContentsSizeHint not translated" $ fmap wrap (BS.hGetContentsSizeHint (unwrap bs))

getContents :: IO ByteString
getContents = trace "getContents not translated" $ fmap wrap BS.getContents

interact :: (ByteString -> ByteString) -> IO ()
interact transformer = trace "interact not translated" $ BS.interact (unwrap . transformer . wrap)

readFile :: FilePath -> IO ByteString
readFile f = trace "readFile not translated" $ fmap wrap (BS.readFile f)

writeFile :: FilePath -> ByteString -> IO ()
writeFile f txt = trace "writeFile not translated" $ BS.writeFile f (unwrap txt)

appendFile :: FilePath -> ByteString -> IO ()
appendFile f txt = trace "appendFile not translated" $ BS.appendFile f (unwrap txt)

-- findIndexOrEnd :: (Word8 -> Bool) -> ByteString -> Int
-- findIndexOrEnd k (PS x s l) = trace "findIndexOrEnd not translated" $ BS.findIndexOrEnd (unwrap bs)

-- errorEmptyList :: String -> a
-- errorEmptyList fun = trace "errorEmptyList not translated" $ BS.errorEmptyList (unwrap bs)

-- moduleError :: String -> String -> a
-- moduleError fun msg = trace "moduleError not translated" $ BS.moduleError (unwrap bs)

-- moduleErrorIO :: String -> String -> IO a
-- moduleErrorIO fun msg = trace "moduleErrorIO not translated" $ BS.moduleErrorIO (unwrap bs)

-- moduleErrorMsg :: String -> String -> String
-- moduleErrorMsg fun msg = trace "moduleErrorMsg not translated" $ BS.moduleErrorMsg (unwrap bs)

-- findFromEndUntil :: (Word8 -> Bool) -> ByteString -> Int
-- findFromEndUntil f bs@(PS x s l) = trace "findFromEndUntil not translated" $ BS.findFromEndUntil (unwrap bs)
