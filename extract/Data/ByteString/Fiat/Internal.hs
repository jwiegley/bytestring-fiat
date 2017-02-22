{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Data.ByteString.Fiat.Internal where

import qualified Data.ByteString.Fiat.HString as HString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Ratio
import qualified Data.Word
import qualified Foreign.ForeignPtr
import qualified Foreign.ForeignPtr.Unsafe
import qualified Foreign.Marshal.Alloc
import qualified Foreign.Marshal.Array
import qualified Foreign.Marshal.Utils
import qualified Foreign.Ptr
import qualified Foreign.Storable
import qualified GHC.Real
import qualified GHC.ForeignPtr
import qualified Prelude
import qualified System.IO.Unsafe


#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
--unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
--unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

id :: a1 -> a1
id x =
  x

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

positive_rect :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                 -> Prelude.Int -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (\p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (\_ ->
    f1)
    p

positive_rec :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                -> Prelude.Int -> a1
positive_rec =
  positive_rect

n_rect :: a1 -> (Prelude.Int -> a1) -> Prelude.Int -> a1
n_rect f f0 n =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ ->
    f)
    (\x ->
    f0 x)
    n

n_rec :: a1 -> (Prelude.Int -> a1) -> Prelude.Int -> a1
n_rec =
  n_rect

succ :: Prelude.Int -> Prelude.Int
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x)
    (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    p)
    (\_ -> (\x -> 2 Prelude.* x)
    1)
    x

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      q)
      (\_ -> (\x -> 2 Prelude.* x)
      1)
      y)
    x

add_carry :: Prelude.Int -> Prelude.Int -> Prelude.Int
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x)
      (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (add p q))
      (\_ -> (\x -> 2 Prelude.* x)
      (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1)
      (succ q))
      (\q -> (\x -> 2 Prelude.* x)
      (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1)
      1)
      y)
    x

pred_double :: Prelude.Int -> Prelude.Int
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x)
    p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1)
    (pred_double p))
    (\_ ->
    1)
    x

data Mask =
   IsNul
 | IsPos Prelude.Int
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Int -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x

sub_mask :: Prelude.Int -> Prelude.Int -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x)
      p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      IsNeg)
      (\_ ->
      IsNeg)
      (\_ ->
      IsNul)
      y)
    x

sub_mask_carry :: Prelude.Int -> Prelude.Int -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y)
    (\_ ->
    IsNeg)
    x

compare_cont :: Prelude.Ordering -> Prelude.Int -> Prelude.Int ->
                Prelude.Ordering
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont r p q)
      (\q ->
      compare_cont Prelude.GT p q)
      (\_ ->
      Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q ->
      compare_cont Prelude.LT p q)
      (\q ->
      compare_cont r p q)
      (\_ ->
      Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.LT)
      (\_ ->
      Prelude.LT)
      (\_ ->
      r)
      y)
    x

compare :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare =
  compare_cont Prelude.EQ

eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q0 ->
      eqb p0 q0)
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.False)
      (\q0 ->
      eqb p0 q0)
      (\_ ->
      Prelude.False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      q)
    p

of_succ_nat :: Prelude.Int -> Prelude.Int
of_succ_nat n =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    1)
    (\x ->
    succ (of_succ_nat x))
    n

eq_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec x y =
  positive_rec (\_ h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\p0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h p0))
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      y0) (\_ h y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h p0))
      (\_ ->
      Prelude.False)
      y0) (\y0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      y0) x y

peano_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
peano_rect a f p =
  let {
   f2 = peano_rect (f 1 a) (\p0 x ->
          f (succ ((\x -> 2 Prelude.* x) p0))
            (f ((\x -> 2 Prelude.* x) p0) x))}
  in
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\q ->
    f ((\x -> 2 Prelude.* x) q) (f2 q))
    (\q ->
    f2 q)
    (\_ ->
    a)
    p

succ0 :: Prelude.Int -> Prelude.Int
succ0 n =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ -> (\x -> x)
    1)
    (\p -> (\x -> x)
    (succ p))
    n

compare0 :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare0 n m =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.EQ)
      (\_ ->
      Prelude.LT)
      m)
    (\n' ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.GT)
      (\m' ->
      compare n' m')
      m)
    n

eqb0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb0 n m =
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      m)
    (\p ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.False)
      (\q ->
      eqb p q)
      m)
    n

eq_dec0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec0 n m =
  n_rec (\m0 ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      m0) (\p m0 ->
    (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
      (\_ ->
      Prelude.False)
      (\p0 ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (eq_dec p p0))
      m0) n m

peano_rect0 :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f ((\x -> x) p)} in
  (\fO fP n -> if n Prelude.== 0 then fO () else fP n)
    (\_ ->
    f0)
    (\p ->
    peano_rect (f 0 f0) f' p)
    n

peano_rec :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
peano_rec =
  peano_rect0

rev :: ([] a1) -> [] a1
rev l =
  case l of {
   [] -> [];
   (:) x l' -> (Prelude.++) (rev l') ((:) x [])}

fold_left :: (a1 -> a2 -> a1) -> ([] a2) -> a1 -> a1
fold_left = \f l z -> Data.List.foldl f z l

data T =
   F1 Prelude.Int
 | FS Prelude.Int T

case0 :: T -> a1
case0 _ =
  __

case1 :: a2 -> (HString.Vector a1) -> a2
case1 h v =
  case v of {
   HString.Nil -> h;
   HString.Cons _ _ _ -> __}

caseS :: (a1 -> Prelude.Int -> (HString.Vector a1) -> a2) -> Prelude.Int ->
         (HString.Vector a1) -> a2
caseS h _ v =
  case v of {
   HString.Nil -> __;
   HString.Cons h0 n t -> h h0 n t}

caseS' :: Prelude.Int -> (HString.Vector a1) -> (a1 -> (HString.Vector 
          a1) -> a2) -> a2
caseS' _ v h =
  case v of {
   HString.Nil -> __;
   HString.Cons h0 _ t -> h h0 t}

rect2 :: a3 -> (Prelude.Int -> (HString.Vector a1) -> (HString.Vector 
         a2) -> a3 -> a1 -> a2 -> a3) -> Prelude.Int -> (HString.Vector 
         a1) -> (HString.Vector a2) -> a3
rect2 bas rect _ v1 v2 =
  case v1 of {
   HString.Nil -> case1 bas v2;
   HString.Cons h1 n' t1 ->
    caseS' n' v2 (\h2 t2 -> rect n' t1 t2 (rect2 bas rect n' t1 t2) h1 h2)}

hd :: Prelude.Int -> (HString.Vector a1) -> a1
hd =
  caseS (\h _ _ -> h)

nth :: Prelude.Int -> (HString.Vector a1) -> T -> a1
nth _ v' p =
  case p of {
   F1 n -> caseS (\h _ _ -> h) n v';
   FS n p' -> caseS (\_ n0 t p0 -> nth n0 t p0) n v' p'}

tl :: Prelude.Int -> (HString.Vector a1) -> HString.Vector a1
tl =
  caseS (\_ _ t -> t)

map :: (a1 -> a2) -> Prelude.Int -> (HString.Vector a1) -> HString.Vector a2
map f _ v =
  case v of {
   HString.Nil -> HString.Nil;
   HString.Cons a n v' -> HString.Cons (f a) n (map f n v')}

type ReflexiveT a r = a -> r

reflexivityT :: (ReflexiveT a1 a2) -> a1 -> a2
reflexivityT reflexiveT =
  reflexiveT

type TransitiveT a r = a -> a -> a -> r -> r -> r

transitivityT :: (TransitiveT a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
transitivityT transitiveT =
  transitiveT

data PreOrderT a r =
   Build_PreOrderT (ReflexiveT a r) (TransitiveT a r)

preOrderT_ReflexiveT :: (PreOrderT a1 a2) -> ReflexiveT a1 a2
preOrderT_ReflexiveT preOrderT =
  case preOrderT of {
   Build_PreOrderT preOrderT_ReflexiveT0 _ -> preOrderT_ReflexiveT0}

preOrderT_TransitiveT :: (PreOrderT a1 a2) -> TransitiveT a1 a2
preOrderT_TransitiveT preOrderT =
  case preOrderT of {
   Build_PreOrderT _ preOrderT_TransitiveT0 -> preOrderT_TransitiveT0}

type MethodType' rep = Any

type MethodType rep = Any

type ADTSig =
  Any -> (,) ((,) Prelude.Int ([] ())) (Prelude.Maybe ())
  -- singleton inductive, whose constructor was Build_ADTSig
  
type MethodIndex = Any

methodDomCod :: ADTSig -> MethodIndex -> (,) ((,) Prelude.Int ([] ()))
                (Prelude.Maybe ())
methodDomCod a =
  a

type ADT =
  MethodIndex -> MethodType Any
  -- singleton inductive, whose constructor was Build_ADT
  
type Rep = Any

vector_caseS' :: (a1 -> Prelude.Int -> (HString.Vector a1) -> a2 -> a3) ->
                 Prelude.Int -> (HString.Vector a1) -> a2 -> a3
vector_caseS' h n v q =
  let {h0 = \h0 t -> h h0 n t q} in
  case v of {
   HString.Nil -> __;
   HString.Cons h1 _ t -> h0 h1 t}

data Prim_prod a b =
   Build_prim_prod a b

prim_fst :: (Prim_prod a1 a2) -> a1
prim_fst p =
  case p of {
   Build_prim_prod prim_fst0 _ -> prim_fst0}

prim_snd :: (Prim_prod a1 a2) -> a2
prim_snd p =
  case p of {
   Build_prim_prod _ prim_snd0 -> prim_snd0}

type Ilist a b = Any

icons :: a1 -> Prelude.Int -> (HString.Vector a1) -> a2 -> (Ilist a1 
         a2) -> Prim_prod a2 Any
icons _ _ _ b il =
  Build_prim_prod b il

inil :: ()
inil =
  ()

ilist_hd :: Prelude.Int -> (HString.Vector a1) -> (Ilist a1 a2) -> Any
ilist_hd _ as0 il =
  case as0 of {
   HString.Nil -> unsafeCoerce ();
   HString.Cons _ _ _ -> prim_fst (unsafeCoerce il)}

ilist_tl :: Prelude.Int -> (HString.Vector a1) -> (Ilist a1 a2) -> Any
ilist_tl _ as0 il =
  case as0 of {
   HString.Nil -> unsafeCoerce ();
   HString.Cons _ _ _ -> prim_snd (unsafeCoerce il)}

ith :: Prelude.Int -> (HString.Vector a1) -> (Ilist a1 a2) -> T -> a2
ith _ as0 il n =
  case n of {
   F1 k ->
    caseS (\h n0 t ->
      unsafeCoerce ilist_hd (HString.nsucc n0) (HString.Cons h n0 t)) k as0
      il;
   FS k n' ->
    vector_caseS' (\h n0 t m il0 ->
      ith n0 t (ilist_tl (HString.nsucc n0) (HString.Cons h n0 t) il0) m) k
      as0 n' il}

imap :: (a1 -> a2 -> a3) -> Prelude.Int -> (HString.Vector a1) -> (Ilist 
        a1 a2) -> Ilist a1 a3
imap f _ as0 il =
  case as0 of {
   HString.Nil -> unsafeCoerce inil;
   HString.Cons a n as' ->
    unsafeCoerce icons a n as'
      (unsafeCoerce f a
        (ilist_hd (HString.nsucc n) (HString.Cons a n as') il))
      (imap f n as' (ilist_tl (HString.nsucc n) (HString.Cons a n as') il))}

data MethSig =
   Build_methSig Prelude.String Prelude.Int ([] ()) (Prelude.Maybe ())

methID :: MethSig -> Prelude.String
methID m =
  case m of {
   Build_methSig methID0 _ _ _ -> methID0}

methArity :: MethSig -> Prelude.Int
methArity m =
  case m of {
   Build_methSig _ methArity0 _ _ -> methArity0}

methDom :: MethSig -> [] ()
methDom m =
  case m of {
   Build_methSig _ _ methDom0 _ -> methDom0}

methCod :: MethSig -> Prelude.Maybe ()
methCod m =
  case m of {
   Build_methSig _ _ _ methCod0 -> methCod0}

data DecoratedADTSig =
   Build_DecoratedADTSig ADTSig Prelude.Int (HString.Vector Prelude.String)

decADTSig :: DecoratedADTSig -> ADTSig
decADTSig d =
  case d of {
   Build_DecoratedADTSig decADTSig0 _ _ -> decADTSig0}

buildADTSig :: Prelude.Int -> (HString.Vector MethSig) -> DecoratedADTSig
buildADTSig n methSigs =
  Build_DecoratedADTSig (\idx ->
    let {domcod = nth n methSigs (unsafeCoerce idx)} in
    (,) ((,) (methArity domcod) (methDom domcod)) (methCod domcod)) n
    (map methID n methSigs)

type CMethodType' rep = Any

type CMethodType rep = Any

type PcADT cRep =
  MethodIndex -> CMethodType cRep
  -- singleton inductive, whose constructor was Build_pcADT
  
pcMethods :: ADTSig -> (PcADT a1) -> MethodIndex -> CMethodType a1
pcMethods _ p =
  p

type CADT = (,) () (PcADT Any)

type CRep = Any

cMethods :: ADTSig -> CADT -> MethodIndex -> CMethodType CRep
cMethods sig c idx =
  pcMethods sig (Prelude.snd c) idx

liftcMethod' :: ([] ()) -> (Prelude.Maybe ()) -> (CMethodType' a1) ->
                MethodType' a1
liftcMethod' dom cod =
  case dom of {
   [] -> __;
   (:) _ dom' -> (\cMethod ->
    unsafeCoerce (\t -> liftcMethod' dom' cod (unsafeCoerce cMethod t)))}

liftcMethod :: Prelude.Int -> ([] ()) -> (Prelude.Maybe ()) -> (CMethodType
               a1) -> MethodType a1
liftcMethod arity dom cod =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    liftcMethod' dom cod)
    (\arity' cMethod ->
    unsafeCoerce (\r -> liftcMethod arity' dom cod (unsafeCoerce cMethod r)))
    arity

liftcADT :: ADTSig -> CADT -> ADT
liftcADT sig a idx =
  liftcMethod (Prelude.fst (Prelude.fst (methodDomCod sig idx)))
    (Prelude.snd (Prelude.fst (methodDomCod sig idx)))
    (Prelude.snd (methodDomCod sig idx)) (cMethods sig a idx)

type MethDef rep =
  MethodType rep
  -- singleton inductive, whose constructor was Build_methDef
  
methBody :: MethSig -> (MethDef a1) -> MethodType a1
methBody _ m =
  m

getMethDef :: Prelude.Int -> (HString.Vector MethSig) -> (Ilist MethSig
              (MethDef a1)) -> T -> MethodType a1
getMethDef n methSigs methDefs idx =
  methBody (nth n methSigs idx) (ith n methSigs methDefs idx)

type DecoratedADT = ADT

buildADT :: Prelude.Int -> (HString.Vector MethSig) -> (Ilist MethSig
            (MethDef a1)) -> DecoratedADT
buildADT n' methSigs methDefs =
  unsafeCoerce getMethDef n' methSigs methDefs

type CMethDef rep =
  CMethodType rep
  -- singleton inductive, whose constructor was Build_cMethDef
  
cMethBody :: MethSig -> (CMethDef a1) -> CMethodType a1
cMethBody _ c =
  c

getcMethDef :: Prelude.Int -> (HString.Vector MethSig) -> (Ilist MethSig
               (CMethDef a1)) -> T -> CMethodType a1
getcMethDef n methSigs methDefs idx =
  cMethBody (nth n methSigs idx) (ith n methSigs methDefs idx)

type DecoratedcADT = CADT

buildcADT :: Prelude.Int -> (HString.Vector MethSig) -> (Ilist MethSig
             (CMethDef a1)) -> DecoratedcADT
buildcADT n' methSigs methDefs =
  (,) __ (\idx -> getcMethDef n' methSigs (unsafeCoerce methDefs) (unsafeCoerce idx))

type Iterate_Dep_Type_BoundedIndex' p = Any

iterate_Dep_Type_equiv' :: Prelude.Int -> (Iterate_Dep_Type_BoundedIndex' 
                           a1) -> T -> a1
iterate_Dep_Type_equiv' _ h idx =
  case idx of {
   F1 _ -> prim_fst (unsafeCoerce h);
   FS i n' -> iterate_Dep_Type_equiv' i (prim_snd (unsafeCoerce h)) n'}

type Iterate_Dep_Type_BoundedIndex p = Iterate_Dep_Type_BoundedIndex' p

lookup_Iterate_Dep_Type :: Prelude.Int -> (Iterate_Dep_Type_BoundedIndex 
                           a1) -> T -> a1
lookup_Iterate_Dep_Type m x idx =
  iterate_Dep_Type_equiv' m x idx

data RefineADT =
   RefinesADT

refineADT_PreOrder :: ADTSig -> PreOrderT ADT RefineADT
refineADT_PreOrder _ =
  Build_PreOrderT (\_ -> RefinesADT) (\_ _ _ _ _ -> RefinesADT)

refineADT_Build_ADT_Rep :: ADTSig -> (MethodIndex -> MethodType a1) ->
                           (MethodIndex -> MethodType a2) -> RefineADT
refineADT_Build_ADT_Rep _ _ _ =
  RefinesADT

type FullySharpened = (,) CADT RefineADT

data SharpenedUnderDelegates =
   Build_SharpenedUnderDelegates Prelude.Int (T -> ADTSig) (() -> (T -> PcADT
                                                           Any) -> CADT) 
 (T -> ADT)

sharpened_Implementation :: ADTSig -> SharpenedUnderDelegates -> (T -> PcADT
                            a1) -> CADT
sharpened_Implementation _ s delegateImpls =
  case s of {
   Build_SharpenedUnderDelegates _ _ sharpened_Implementation0 _ ->
    unsafeCoerce sharpened_Implementation0 __ delegateImpls}

type FullySharpenedUnderDelegates =
  () -> (T -> PcADT Any) -> (T -> RefineADT) -> RefineADT

fullySharpened_Start :: ADTSig -> ADT -> CADT -> RefineADT -> FullySharpened
fullySharpened_Start _ _ cadt x =
  (,) cadt x

fullySharpened_Finish :: ADTSig -> ADT -> SharpenedUnderDelegates -> CADT ->
                         FullySharpenedUnderDelegates -> (T -> PcADT 
                         a1) -> (T -> RefineADT) -> RefineADT -> RefineADT
fullySharpened_Finish sig spec adt cadt x delegateImpls validImpls x0 =
  transitivityT (preOrderT_TransitiveT (refineADT_PreOrder sig)) spec
    (liftcADT sig (sharpened_Implementation sig adt delegateImpls))
    (liftcADT sig cadt) (unsafeCoerce x __ delegateImpls validImpls) x0

sharpenStep :: ADTSig -> ADT -> ADT -> ADT -> RefineADT -> RefineADT ->
               RefineADT
sharpenStep sig adt adt' adt'' refine_adt' x =
  transitivityT (preOrderT_TransitiveT (refineADT_PreOrder sig)) adt adt'
    adt'' refine_adt' x

type UnCurry_Dom = Any

type UnCurried_methodType rep = (HString.Vector rep) -> UnCurry_Dom -> Any

curry_methodType' :: ([] ()) -> (Prelude.Maybe ()) -> (UnCurry_Dom -> Any) ->
                     MethodType' a1
curry_methodType' dom cod f =
  case dom of {
   [] -> unsafeCoerce f ();
   (:) _ dom' ->
    unsafeCoerce (\t ->
      curry_methodType' dom' cod (\t' -> unsafeCoerce f ((,) t t')))}

curry_methodType :: Prelude.Int -> ([] ()) -> (Prelude.Maybe ()) ->
                    (UnCurried_methodType a1) -> MethodType a1
curry_methodType arity dom cod f =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    curry_methodType' dom cod (f HString.Nil))
    (\n' ->
    unsafeCoerce (\t ->
      curry_methodType n' dom cod (\t' -> f (HString.Cons t n' t'))))
    arity

absMethod :: Prelude.Int -> ([] ()) -> (Prelude.Maybe ()) -> (MethodType 
             a1) -> MethodType a2
absMethod arity dom cod _ =
  curry_methodType arity dom cod __

refineADT_Build_ADT_Rep_default :: ADTSig -> (MethodIndex -> MethodType 
                                   a1) -> RefineADT
refineADT_Build_ADT_Rep_default sig oldMeths =
  refineADT_Build_ADT_Rep sig oldMeths (\idx ->
    absMethod (Prelude.fst (Prelude.fst (methodDomCod sig idx)))
      (Prelude.snd (Prelude.fst (methodDomCod sig idx)))
      (Prelude.snd (methodDomCod sig idx)) (oldMeths idx))

notation_Friendly_BuildMostlySharpenedcADT :: Prelude.Int -> (HString.Vector
                                              MethSig) -> Prelude.Int -> (T
                                              -> ADTSig) -> (() -> (T ->
                                              PcADT Any) -> Ilist MethSig
                                              (CMethodType a1)) -> (T ->
                                              PcADT a2) -> CADT
notation_Friendly_BuildMostlySharpenedcADT n methSigs _ _ cMethods0 delegateImpls =
  buildcADT n methSigs
    (imap (unsafeCoerce (\_ x -> x)) n methSigs
      (unsafeCoerce cMethods0 __ delegateImpls))

notation_Friendly_FullySharpened_BuildMostlySharpenedcADT :: Prelude.Int ->
                                                             (HString.Vector
                                                             MethSig) ->
                                                             (Ilist MethSig
                                                             (MethDef a1)) ->
                                                             Prelude.Int ->
                                                             (T -> ADTSig) ->
                                                             (() -> (T ->
                                                             PcADT Any) ->
                                                             Ilist MethSig
                                                             (CMethodType a2))
                                                             -> (T -> ADT) ->
                                                             (() -> (T ->
                                                             PcADT Any) -> (T
                                                             -> RefineADT) ->
                                                             Iterate_Dep_Type_BoundedIndex
                                                             ()) -> (T ->
                                                             PcADT a3) -> (T
                                                             -> RefineADT) ->
                                                             RefineADT
notation_Friendly_FullySharpened_BuildMostlySharpenedcADT _ _ _ _ _ _ _ _ _ _ =
  RefinesADT

type NamedDelegatee =
  ADTSig
  -- singleton inductive, whose constructor was Build_NamedDelegatee
  
delegateeSig :: NamedDelegatee -> ADTSig
delegateeSig n =
  n

build_NamedDelegatees :: Prelude.Int -> (HString.Vector ADTSig) ->
                         (HString.Vector ()) -> HString.Vector NamedDelegatee
build_NamedDelegatees n delegateSigs delegateReps =
  rect2 HString.Nil (\n0 _ _ delegatees _ sig -> HString.Cons sig n0
    delegatees) n delegateReps delegateSigs

notation_Friendly_SharpenFully :: Prelude.Int -> Prelude.Int ->
                                  (HString.Vector MethSig) -> (Ilist 
                                  MethSig (MethDef a1)) -> (HString.Vector
                                  ADTSig) -> (HString.Vector ()) -> (() -> (T
                                  -> PcADT Any) -> Ilist MethSig
                                  (CMethodType a2)) -> (Ilist NamedDelegatee
                                  ADT) -> (() -> (T -> PcADT Any) -> (T ->
                                  RefineADT) -> Iterate_Dep_Type_BoundedIndex
                                  ()) -> (T -> PcADT a3) -> (T -> RefineADT)
                                  -> RefineADT
notation_Friendly_SharpenFully m n methSigs methDefs delegateSigs' delegateReps' cMethods0 delegateSpecs' cMethodsRefinesSpec delegateImpls validImpls =
  let {delegatees = build_NamedDelegatees m delegateSigs' delegateReps'} in
  let {delegateSigs = \idx -> delegateeSig (nth m delegatees idx)} in
  let {delegateSpecs = ith m delegatees delegateSpecs'} in
  notation_Friendly_FullySharpened_BuildMostlySharpenedcADT n methSigs
    methDefs m delegateSigs cMethods0 delegateSpecs cMethodsRefinesSpec
    delegateImpls validImpls

refineADT_BuildADT_Rep_refine_All :: Prelude.Int -> (HString.Vector MethSig)
                                     -> (Ilist MethSig (MethDef a1)) ->
                                     (Ilist MethSig (MethDef a2)) ->
                                     RefineADT
refineADT_BuildADT_Rep_refine_All n methSigs methDefs refined_methDefs =
  refineADT_Build_ADT_Rep (decADTSig (buildADTSig n methSigs))
    (unsafeCoerce getMethDef n methSigs methDefs)
    (unsafeCoerce getMethDef n methSigs refined_methDefs)

getADTSig :: DecoratedADTSig -> ADT -> DecoratedADTSig
getADTSig sig _ =
  sig

ifDep_Then_Else :: Prelude.Bool -> (() -> a1) -> (() -> a1) -> a1
ifDep_Then_Else c t e =
  case c of {
   Prelude.True -> t __;
   Prelude.False -> e __}

data Compare x =
   LT
 | EQ
 | GT

compare_rect :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) ->
                (Compare a1) -> a2
compare_rect _ _ f f0 f1 c =
  case c of {
   LT -> f __;
   EQ -> f0 __;
   GT -> f1 __}

compare_rec :: a1 -> a1 -> (() -> a2) -> (() -> a2) -> (() -> a2) -> (Compare
               a1) -> a2
compare_rec x y =
  compare_rect x y

compare1 :: Prelude.Int -> Prelude.Int -> Compare Prelude.Int
compare1 x y =
  case compare0 x y of {
   Prelude.EQ -> EQ;
   Prelude.LT -> LT;
   Prelude.GT -> GT}

eq_dec1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec1 =
  eq_dec0

type T0 = Prelude.Int

compare2 :: Prelude.Int -> Prelude.Int -> Compare Prelude.Int
compare2 x y =
  case compare0 x y of {
   Prelude.EQ -> EQ;
   Prelude.LT -> LT;
   Prelude.GT -> GT}

eq_dec2 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec2 =
  eq_dec0

type Ptr a = Foreign.ForeignPtr.ForeignPtr a

type Size = Prelude.Int

type Word = Data.Word.Word8

type T1 = Ptr Word

eq_dec3 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eq_dec3 =
  (Prelude.==)

emptyS :: Prelude.String
emptyS =
  (:) 'e' ((:) 'm' ((:) 'p' ((:) 't' ((:) 'y' []))))

packS :: Prelude.String
packS =
  (:) 'p' ((:) 'a' ((:) 'c' ((:) 'k' [])))

unpackS :: Prelude.String
unpackS =
  (:) 'u' ((:) 'n' ((:) 'p' ((:) 'a' ((:) 'c' ((:) 'k' [])))))

consS :: Prelude.String
consS =
  (:) 'c' ((:) 'o' ((:) 'n' ((:) 's' [])))

unconsS :: Prelude.String
unconsS =
  (:) 'u' ((:) 'n' ((:) 'c' ((:) 'o' ((:) 'n' ((:) 's' [])))))

appendS :: Prelude.String
appendS =
  (:) 'a' ((:) 'p' ((:) 'p' ((:) 'e' ((:) 'n' ((:) 'd' [])))))

byteStringSpec :: DecoratedADT
byteStringSpec =
  buildADT (HString.nsucc (HString.nsucc (HString.nsucc (HString.nsucc
    (HString.nsucc (HString.nsucc (0 :: Prelude.Int))))))) (HString.Cons
    (Build_methSig emptyS (0 :: Prelude.Int) [] Prelude.Nothing)
    (HString.nsucc (HString.nsucc (HString.nsucc (HString.nsucc
    (HString.nsucc (0 :: Prelude.Int)))))) (HString.Cons (Build_methSig packS
    (0 :: Prelude.Int) ((:) __ []) Prelude.Nothing) (HString.nsucc
    (HString.nsucc (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))))
    (HString.Cons (Build_methSig unpackS (HString.nsucc (0 :: Prelude.Int))
    [] (Prelude.Just __)) (HString.nsucc (HString.nsucc (HString.nsucc
    (0 :: Prelude.Int)))) (HString.Cons (Build_methSig consS (HString.nsucc
    (0 :: Prelude.Int)) ((:) __ []) Prelude.Nothing) (HString.nsucc
    (HString.nsucc (0 :: Prelude.Int))) (HString.Cons (Build_methSig unconsS
    (HString.nsucc (0 :: Prelude.Int)) [] (Prelude.Just __)) (HString.nsucc
    (0 :: Prelude.Int)) (HString.Cons (Build_methSig appendS (HString.nsucc
    (HString.nsucc (0 :: Prelude.Int))) [] Prelude.Nothing)
    (0 :: Prelude.Int) HString.Nil))))))
    (unsafeCoerce icons (Build_methSig emptyS (0 :: Prelude.Int) []
      Prelude.Nothing) (HString.nsucc (HString.nsucc (HString.nsucc
      (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))))) (HString.Cons
      (Build_methSig packS (0 :: Prelude.Int) ((:) __ []) Prelude.Nothing)
      (HString.nsucc (HString.nsucc (HString.nsucc (HString.nsucc
      (0 :: Prelude.Int))))) (HString.Cons (Build_methSig unpackS
      (HString.nsucc (0 :: Prelude.Int)) [] (Prelude.Just __)) (HString.nsucc
      (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))) (HString.Cons
      (Build_methSig consS (HString.nsucc (0 :: Prelude.Int)) ((:) __ [])
      Prelude.Nothing) (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))
      (HString.Cons (Build_methSig unconsS (HString.nsucc (0 :: Prelude.Int))
      [] (Prelude.Just __)) (HString.nsucc (0 :: Prelude.Int)) (HString.Cons
      (Build_methSig appendS (HString.nsucc (HString.nsucc
      (0 :: Prelude.Int))) [] Prelude.Nothing) (0 :: Prelude.Int)
      HString.Nil))))) __
      (icons (Build_methSig packS (0 :: Prelude.Int) ((:) __ [])
        Prelude.Nothing) (HString.nsucc (HString.nsucc (HString.nsucc
        (HString.nsucc (0 :: Prelude.Int))))) (HString.Cons (Build_methSig
        unpackS (HString.nsucc (0 :: Prelude.Int)) [] (Prelude.Just __))
        (HString.nsucc (HString.nsucc (HString.nsucc (0 :: Prelude.Int))))
        (HString.Cons (Build_methSig consS (HString.nsucc (0 :: Prelude.Int))
        ((:) __ []) Prelude.Nothing) (HString.nsucc (HString.nsucc
        (0 :: Prelude.Int))) (HString.Cons (Build_methSig unconsS
        (HString.nsucc (0 :: Prelude.Int)) [] (Prelude.Just __))
        (HString.nsucc (0 :: Prelude.Int)) (HString.Cons (Build_methSig
        appendS (HString.nsucc (HString.nsucc (0 :: Prelude.Int))) []
        Prelude.Nothing) (0 :: Prelude.Int) HString.Nil)))) __
        (unsafeCoerce icons (Build_methSig unpackS (HString.nsucc
          (0 :: Prelude.Int)) [] (Prelude.Just __)) (HString.nsucc
          (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))) (HString.Cons
          (Build_methSig consS (HString.nsucc (0 :: Prelude.Int)) ((:) __ [])
          Prelude.Nothing) (HString.nsucc (HString.nsucc (0 :: Prelude.Int)))
          (HString.Cons (Build_methSig unconsS (HString.nsucc
          (0 :: Prelude.Int)) [] (Prelude.Just __)) (HString.nsucc
          (0 :: Prelude.Int)) (HString.Cons (Build_methSig appendS
          (HString.nsucc (HString.nsucc (0 :: Prelude.Int))) []
          Prelude.Nothing) (0 :: Prelude.Int) HString.Nil))) __
          (icons (Build_methSig consS (HString.nsucc (0 :: Prelude.Int)) ((:)
            __ []) Prelude.Nothing) (HString.nsucc (HString.nsucc
            (0 :: Prelude.Int))) (HString.Cons (Build_methSig unconsS
            (HString.nsucc (0 :: Prelude.Int)) [] (Prelude.Just __))
            (HString.nsucc (0 :: Prelude.Int)) (HString.Cons (Build_methSig
            appendS (HString.nsucc (HString.nsucc (0 :: Prelude.Int))) []
            Prelude.Nothing) (0 :: Prelude.Int) HString.Nil)) __
            (unsafeCoerce icons (Build_methSig unconsS (HString.nsucc
              (0 :: Prelude.Int)) [] (Prelude.Just __)) (HString.nsucc
              (0 :: Prelude.Int)) (HString.Cons (Build_methSig appendS
              (HString.nsucc (HString.nsucc (0 :: Prelude.Int))) []
              Prelude.Nothing) (0 :: Prelude.Int) HString.Nil) __
              (icons (Build_methSig appendS (HString.nsucc (HString.nsucc
                (0 :: Prelude.Int))) [] Prelude.Nothing) (0 :: Prelude.Int)
                HString.Nil __ (unsafeCoerce inil)))))))

annotate_ADT :: Prelude.Int -> (HString.Vector MethSig) -> (Ilist MethSig
                (MethDef a1)) -> (Ilist MethSig (MethDef a2)) ->
                (Iterate_Dep_Type_BoundedIndex ()) -> RefineADT
annotate_ADT n' methSigs methDefs methDefs' _ =
  transitivityT
    (preOrderT_TransitiveT
      (refineADT_PreOrder (decADTSig (buildADTSig n' methSigs))))
    (buildADT n' methSigs methDefs) (\idx ->
    absMethod
      (Prelude.fst
        (Prelude.fst
          (methodDomCod (decADTSig (buildADTSig n' methSigs)) idx)))
      (Prelude.snd
        (Prelude.fst
          (methodDomCod (decADTSig (buildADTSig n' methSigs)) idx)))
      (Prelude.snd (methodDomCod (decADTSig (buildADTSig n' methSigs)) idx))
      (getMethDef n' methSigs methDefs (unsafeCoerce idx)))
    (buildADT n' methSigs methDefs')
    (refineADT_Build_ADT_Rep_default (decADTSig (buildADTSig n' methSigs))
      (unsafeCoerce getMethDef n' methSigs methDefs)) RefinesADT

data Hlist =
   HNil
 | HCons ([] ()) Any Hlist

hlist_head :: ([] ()) -> Hlist -> a1
hlist_head _ l =
  case l of {
   HNil -> false_rect;
   HCons _ x _ ->  (unsafeCoerce x)}

hlist_tail :: ([] ()) -> Hlist -> Hlist
hlist_tail _ l =
  case l of {
   HNil -> false_rect;
   HCons _ _ xs ->  xs}

comp :: (a2 -> a3) -> (a1 -> a2) -> a1 -> a3
comp f g x =
  f (g x)

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

data Free f a =
   Pure a
 | Join (Any -> Free f a) f

iter :: (Functor a1) -> (a1 -> a2) -> (Free a1 a2) -> a2
iter h phi fr =
  case fr of {
   Pure x -> x;
   Join g h0 -> phi (fmap h (comp (iter h phi) g) h0)}

data MethodCall rep rec_ =
   Call MethodIndex Hlist (rep -> Any)

methodCall_fmap :: ADTSig -> (a2 -> a3) -> (MethodCall a1 a2) -> MethodCall
                   a1 a3
methodCall_fmap sig f mc =
  case mc of {
   Call midx args k -> Call midx args (\r' ->
    case Prelude.snd (methodDomCod sig midx) of {
     Prelude.Just _ -> unsafeCoerce (\cod -> f (unsafeCoerce k r' cod));
     Prelude.Nothing -> unsafeCoerce f (k r')})}

methodCall_Functor :: ADTSig -> Functor (MethodCall a1 Any)
methodCall_Functor sig _ _ =
  methodCall_fmap sig

type ClientDSL rep a = Free (MethodCall rep Any) a

type Reflect_ADT_DSL_computation a = (,) (ClientDSL Rep a) ()

reflect_ADT_DSL_computation_simplify :: ADTSig -> ADT ->
                                        (Reflect_ADT_DSL_computation 
                                        a1) -> Reflect_ADT_DSL_computation 
                                        a1
reflect_ADT_DSL_computation_simplify _ _ c_DSL =
  (,) (Prelude.fst c_DSL) __

reflect_ADT_DSL_computation_If_Then_Else :: ADTSig -> ADT -> Prelude.Bool ->
                                            (Reflect_ADT_DSL_computation 
                                            a1) ->
                                            (Reflect_ADT_DSL_computation 
                                            a1) ->
                                            Reflect_ADT_DSL_computation 
                                            a1
reflect_ADT_DSL_computation_If_Then_Else _ _ c c_DSL k_DSL =
  (,)
    ((\c t e -> if c then t else e) c (Prelude.fst c_DSL)
      (Prelude.fst k_DSL)) __

reflect_ADT_DSL_computation_IfDep_Then_Else :: ADTSig -> ADT -> Prelude.Bool
                                               -> (() ->
                                               Reflect_ADT_DSL_computation
                                               a1) -> (() ->
                                               Reflect_ADT_DSL_computation
                                               a1) ->
                                               Reflect_ADT_DSL_computation 
                                               a1
reflect_ADT_DSL_computation_IfDep_Then_Else _ _ c c_DSL k_DSL =
  (,)
    (ifDep_Then_Else c (\_ -> Prelude.fst (c_DSL __)) (\_ ->
      Prelude.fst (k_DSL __))) __

type T2 = Prelude.Int

eq_dec4 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec4 =
  eq_dec1

lt_dec :: Prelude.Int -> Prelude.Int -> Prelude.Bool
lt_dec x y =
  compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ ->
    Prelude.False) (compare1 x y)

eqb1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb1 x y =
  case eq_dec4 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type T3 = Prelude.Int

eq_dec5 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec5 =
  eq_dec1

lt_dec0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
lt_dec0 x y =
  compare_rec x y (\_ -> Prelude.True) (\_ -> Prelude.False) (\_ ->
    Prelude.False) (compare1 x y)

eqb2 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb2 x y =
  case eq_dec5 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type Key = Prelude.Int

type T4 elt = [] ((,) Prelude.Int elt)

empty :: T4 a1
empty =
  []

is_empty :: (T4 a1) -> Prelude.Bool
is_empty l =
  case l of {
   [] -> Prelude.True;
   (:) _ _ -> Prelude.False}

mem :: Key -> (T4 a1) -> Prelude.Bool
mem k s =
  case s of {
   [] -> Prelude.False;
   (:) p l ->
    case p of {
     (,) k' _ ->
      case compare1 k k' of {
       LT -> Prelude.False;
       EQ -> Prelude.True;
       GT -> mem k l}}}

data R_mem elt =
   R_mem_0 (T4 elt)
 | R_mem_1 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_mem_2 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_mem_3 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) Prelude.Bool 
 (R_mem elt)

r_mem_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
              -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
              a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
              () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
              (R_mem a1) -> a2 -> a2) -> (T4 a1) -> Prelude.Bool -> (R_mem
              a1) -> a2
r_mem_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_mem_0 s -> f s __;
   R_mem_1 s k' _x l -> f0 s k' _x l __ __ __;
   R_mem_2 s k' _x l -> f1 s k' _x l __ __ __;
   R_mem_3 s k' _x l _res r0 ->
    f2 s k' _x l __ __ __ _res r0 (r_mem_rect k f f0 f1 f2 l _res r0)}

r_mem_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
             ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4 
             a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
             () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
             ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
             (R_mem a1) -> a2 -> a2) -> (T4 a1) -> Prelude.Bool -> (R_mem 
             a1) -> a2
r_mem_rec k =
  r_mem_rect k

mem_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
            ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4 
            a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> ()
            -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
            ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
            a1) -> a2
mem_rect k f2 f1 f0 f s =
  
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      [] -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ -> let {hrec = mem_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare1 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}})

mem_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
           ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4 
           a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> ()
           -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
           ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
           a1) -> a2
mem_rec k =
  mem_rect k

r_mem_correct :: Key -> (T4 a1) -> Prelude.Bool -> R_mem a1
r_mem_correct k s _res =
  let {princ = \x -> mem_rect x} in
  unsafeCoerce princ k (\y _ _ _ ->  (R_mem_0 y)) (\y y0 y1 y2 _ _ _ _ _ ->
     (R_mem_1 y y0 y1 y2)) (\y y0 y1 y2 _ _ _ _ _ ->  (R_mem_2 y y0 y1 y2))
    (\y y0 y1 y2 _ _ _ y6 _ _ ->
     (R_mem_3 y y0 y1 y2 (mem k y2) (y6 (mem k y2) __))) s _res __

find :: Key -> (T4 a1) -> Prelude.Maybe a1
find k s =
  case s of {
   [] -> Prelude.Nothing;
   (:) p s' ->
    case p of {
     (,) k' x ->
      case compare1 k k' of {
       LT -> Prelude.Nothing;
       EQ -> Prelude.Just x;
       GT -> find k s'}}}

data R_find elt =
   R_find_0 (T4 elt)
 | R_find_1 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_find_2 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_find_3 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) (Prelude.Maybe
                                                                elt) 
 (R_find elt)

r_find_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
               -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
               a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
               () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
               ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe 
               a1) -> (R_find a1) -> a2 -> a2) -> (T4 a1) -> (Prelude.Maybe
               a1) -> (R_find a1) -> a2
r_find_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_find_0 s -> f s __;
   R_find_1 s k' x s' -> f0 s k' x s' __ __ __;
   R_find_2 s k' x s' -> f1 s k' x s' __ __ __;
   R_find_3 s k' x s' _res r0 ->
    f2 s k' x s' __ __ __ _res r0 (r_find_rect k f f0 f1 f2 s' _res r0)}

r_find_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
              -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
              a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
              () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> () -> () -> (Prelude.Maybe 
              a1) -> (R_find a1) -> a2 -> a2) -> (T4 a1) -> (Prelude.Maybe
              a1) -> (R_find a1) -> a2
r_find_rec k =
  r_find_rect k

find_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
             ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4 
             a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
             () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
             ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
             a1) -> a2
find_rect k f2 f1 f0 f s =
  
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      [] -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = find_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare1 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}})

find_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
            ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4 
            a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> ()
            -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
            ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
            a1) -> a2
find_rec k =
  find_rect k

r_find_correct :: Key -> (T4 a1) -> (Prelude.Maybe a1) -> R_find a1
r_find_correct k s _res =
  let {princ = \x -> find_rect x} in
  unsafeCoerce princ k (\y _ _ _ ->  (R_find_0 y)) (\y y0 y1 y2 _ _ _ _ _ ->
     (R_find_1 y y0 y1 y2)) (\y y0 y1 y2 _ _ _ _ _ ->  (R_find_2 y y0 y1 y2))
    (\y y0 y1 y2 _ _ _ y6 _ _ ->
     (R_find_3 y y0 y1 y2 (find k y2) (y6 (find k y2) __))) s _res __

add0 :: Key -> a1 -> (T4 a1) -> T4 a1
add0 k x s =
  case s of {
   [] -> (:) ((,) k x) [];
   (:) p l ->
    case p of {
     (,) k' y ->
      case compare1 k k' of {
       LT -> (:) ((,) k x) s;
       EQ -> (:) ((,) k x) l;
       GT -> (:) ((,) k' y) (add0 k x l)}}}

data R_add elt =
   R_add_0 (T4 elt)
 | R_add_1 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_add_2 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_add_3 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) (T4 elt) 
 (R_add elt)

r_add_rect :: Key -> a1 -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int
              -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) ->
              ((T4 a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) ->
              () -> () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> () -> () -> (T4 a1) -> (R_add
              a1) -> a2 -> a2) -> (T4 a1) -> (T4 a1) -> (R_add a1) -> a2
r_add_rect k x f f0 f1 f2 _ _ r =
  case r of {
   R_add_0 s -> f s __;
   R_add_1 s k' y l -> f0 s k' y l __ __ __;
   R_add_2 s k' y l -> f1 s k' y l __ __ __;
   R_add_3 s k' y l _res r0 ->
    f2 s k' y l __ __ __ _res r0 (r_add_rect k x f f0 f1 f2 l _res r0)}

r_add_rec :: Key -> a1 -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int ->
             a1 -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
             a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
             () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
             ((,) Prelude.Int a1)) -> () -> () -> () -> (T4 a1) -> (R_add 
             a1) -> a2 -> a2) -> (T4 a1) -> (T4 a1) -> (R_add a1) -> a2
r_add_rec k x =
  r_add_rect k x

add_rect :: Key -> a1 -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int ->
            a1 -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
            a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> ()
            -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
            ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
            a1) -> a2
add_rect k x f2 f1 f0 f s =
  
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      [] -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = add_rect k x f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare1 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}})

add_rec :: Key -> a1 -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int ->
           a1 -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
           a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> ()
           -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
           ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
           a1) -> a2
add_rec k x =
  add_rect k x

r_add_correct :: Key -> a1 -> (T4 a1) -> (T4 a1) -> R_add a1
r_add_correct k x s _res =
  add_rect k x (\y _ _ _ ->  (R_add_0 y)) (\y y0 y1 y2 _ _ _ _ _ ->
     (R_add_1 y y0 y1 y2)) (\y y0 y1 y2 _ _ _ _ _ ->  (R_add_2 y y0 y1 y2))
    (\y y0 y1 y2 _ _ _ y6 _ _ ->
     (R_add_3 y y0 y1 y2 (add0 k x y2) (y6 (add0 k x y2) __))) s _res __

remove :: Key -> (T4 a1) -> T4 a1
remove k s =
  case s of {
   [] -> [];
   (:) p l ->
    case p of {
     (,) k' x ->
      case compare1 k k' of {
       LT -> s;
       EQ -> l;
       GT -> (:) ((,) k' x) (remove k l)}}}

data R_remove elt =
   R_remove_0 (T4 elt)
 | R_remove_1 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_remove_2 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt))
 | R_remove_3 (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) (T4 elt) 
 (R_remove elt)

r_remove_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int ->
                 a1 -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) ->
                 ((T4 a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1))
                 -> () -> () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 ->
                 ([] ((,) Prelude.Int a1)) -> () -> () -> () -> (T4 a1) ->
                 (R_remove a1) -> a2 -> a2) -> (T4 a1) -> (T4 a1) ->
                 (R_remove a1) -> a2
r_remove_rect k f f0 f1 f2 _ _ r =
  case r of {
   R_remove_0 s -> f s __;
   R_remove_1 s k' x l -> f0 s k' x l __ __ __;
   R_remove_2 s k' x l -> f1 s k' x l __ __ __;
   R_remove_3 s k' x l _res r0 ->
    f2 s k' x l __ __ __ _res r0 (r_remove_rect k f f0 f1 f2 l _res r0)}

r_remove_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
                -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
                a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> ()
                -> () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
                ((,) Prelude.Int a1)) -> () -> () -> () -> (T4 a1) ->
                (R_remove a1) -> a2 -> a2) -> (T4 a1) -> (T4 a1) -> (R_remove
                a1) -> a2
r_remove_rec k =
  r_remove_rect k

remove_rect :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
               -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
               a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
               () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
               ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4
               a1) -> a2
remove_rect k f2 f1 f0 f s =
  
    (let {f3 = f2 s} in
     let {f4 = f1 s} in
     let {f5 = f0 s} in
     let {f6 = f s} in
     case s of {
      [] -> f3 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f7 = f6 t0 e l __} in
         let {
          f8 = \_ _ ->
           let {hrec = remove_rect k f2 f1 f0 f l} in f7 __ __ hrec}
         in
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case compare1 k t0 of {
          LT -> f10 __ __;
          EQ -> f9 __ __;
          GT -> f8 __ __}}})

remove_rec :: Key -> ((T4 a1) -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1
              -> ([] ((,) Prelude.Int a1)) -> () -> () -> () -> a2) -> ((T4
              a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
              () -> () -> a2) -> ((T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> (T4 
              a1) -> a2
remove_rec k =
  remove_rect k

r_remove_correct :: Key -> (T4 a1) -> (T4 a1) -> R_remove a1
r_remove_correct k s _res =
  let {princ = \x -> remove_rect x} in
  unsafeCoerce princ k (\y _ _ _ ->  (R_remove_0 y))
    (\y y0 y1 y2 _ _ _ _ _ ->  (R_remove_1 y y0 y1 y2))
    (\y y0 y1 y2 _ _ _ _ _ ->  (R_remove_2 y y0 y1 y2))
    (\y y0 y1 y2 _ _ _ y6 _ _ ->
     (R_remove_3 y y0 y1 y2 (remove k y2) (y6 (remove k y2) __))) s _res __

elements :: (T4 a1) -> T4 a1
elements m =
  m

fold :: (Key -> a1 -> a2 -> a2) -> (T4 a1) -> a2 -> a2
fold f m acc =
  case m of {
   [] -> acc;
   (:) p m' ->
    case p of {
     (,) k e -> fold f m' (f k e acc)}}

data R_fold elt a =
   R_fold_0 (Key -> elt -> a -> a) (T4 elt) a
 | R_fold_1 (Key -> elt -> a -> a) (T4 elt) a Prelude.Int elt ([]
                                                              ((,)
                                                              Prelude.Int
                                                              elt)) a 
 (R_fold elt a)

r_fold_rect :: (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any -> () ->
               a2) -> (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any ->
               Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> Any ->
               (R_fold a1 Any) -> a2 -> a2) -> (Key -> a1 -> a3 -> a3) -> (T4
               a1) -> a3 -> a3 -> (R_fold a1 a3) -> a2
r_fold_rect f f0 _ _ _ _ r =
  case r of {
   R_fold_0 f1 m acc -> unsafeCoerce f __ f1 m acc __;
   R_fold_1 f1 m acc k e m' _res r0 ->
    unsafeCoerce f0 __ f1 m acc k e m' __ _res r0
      (r_fold_rect f f0 f1 m' (f1 k e acc) _res r0)}

r_fold_rec :: (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any -> () -> a2)
              -> (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any ->
              Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> Any ->
              (R_fold a1 Any) -> a2 -> a2) -> (Key -> a1 -> a3 -> a3) -> (T4
              a1) -> a3 -> a3 -> (R_fold a1 a3) -> a2
r_fold_rec f f0 f1 m acc a r =
  r_fold_rect f f0 f1 m acc a r

fold_rect :: (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any -> () -> a2)
             -> (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any ->
             Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> a2 ->
             a2) -> (Key -> a1 -> a3 -> a3) -> (T4 a1) -> a3 -> a2
fold_rect f0 f f1 m acc =
  
    (let {f2 = unsafeCoerce f0 __ f1 m acc} in
     let {f3 = unsafeCoerce f __ f1 m acc} in
     case m of {
      [] -> f2 __;
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f4 = f3 t0 e l __} in
         let {hrec = fold_rect f0 f f1 l (f1 t0 e acc)} in f4 hrec}})

fold_rec :: (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any -> () -> a2)
            -> (() -> (Key -> a1 -> Any -> Any) -> (T4 a1) -> Any ->
            Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () -> a2 -> a2)
            -> (Key -> a1 -> a3 -> a3) -> (T4 a1) -> a3 -> a2
fold_rec f f0 f1 m acc =
  fold_rect f f0 f1 m acc

r_fold_correct :: (Key -> a1 -> a2 -> a2) -> (T4 a1) -> a2 -> a2 -> R_fold 
                  a1 a2
r_fold_correct f m acc _res =
  let {princ = \x x0 -> fold_rect x x0} in
  unsafeCoerce princ (\_ y0 y1 y2 _ _ _ ->  (R_fold_0 y0 y1 y2))
    (\_ y0 y1 y2 y3 y4 y5 _ y7 _ _ ->
     (R_fold_1 y0 y1 y2 y3 y4 y5 (fold y0 y5 (y0 y3 y4 y2))
      (y7 (fold y0 y5 (y0 y3 y4 y2)) __))) f m acc _res __

equal :: (a1 -> a1 -> Prelude.Bool) -> (T4 a1) -> (T4 a1) -> Prelude.Bool
equal cmp m m' =
  case m of {
   [] ->
    case m' of {
     [] -> Prelude.True;
     (:) _ _ -> Prelude.False};
   (:) p l ->
    case p of {
     (,) x e ->
      case m' of {
       [] -> Prelude.False;
       (:) p0 l' ->
        case p0 of {
         (,) x' e' ->
          case compare1 x x' of {
           EQ -> (Prelude.&&) (cmp e e') (equal cmp l l');
           _ -> Prelude.False}}}}}

data R_equal elt =
   R_equal_0 (T4 elt) (T4 elt)
 | R_equal_1 (T4 elt) (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) 
 Prelude.Int elt ([] ((,) Prelude.Int elt)) Prelude.Bool (R_equal elt)
 | R_equal_2 (T4 elt) (T4 elt) Prelude.Int elt ([] ((,) Prelude.Int elt)) 
 Prelude.Int elt ([] ((,) Prelude.Int elt)) (Compare Prelude.Int)
 | R_equal_3 (T4 elt) (T4 elt) (T4 elt) (T4 elt)

r_equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((T4 a1) -> (T4 a1) -> () -> ()
                -> a2) -> ((T4 a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([]
                ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> ([]
                ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
                (R_equal a1) -> a2 -> a2) -> ((T4 a1) -> (T4 a1) ->
                Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
                Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
                (Compare Prelude.Int) -> () -> () -> a2) -> ((T4 a1) -> (T4
                a1) -> (T4 a1) -> () -> (T4 a1) -> () -> () -> a2) -> (T4 
                a1) -> (T4 a1) -> Prelude.Bool -> (R_equal a1) -> a2
r_equal_rect cmp f f0 f1 f2 _ _ _ r =
  case r of {
   R_equal_0 m m' -> f m m' __ __;
   R_equal_1 m m' x e l x' e' l' _res r0 ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (r_equal_rect cmp f f0 f1 f2 l l' _res r0);
   R_equal_2 m m' x e l x' e' l' _x -> f1 m m' x e l __ x' e' l' __ _x __ __;
   R_equal_3 m m' _x _x0 -> f2 m m' _x __ _x0 __ __}

r_equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((T4 a1) -> (T4 a1) -> () -> ()
               -> a2) -> ((T4 a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([]
               ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> ([]
               ((,) Prelude.Int a1)) -> () -> () -> () -> Prelude.Bool ->
               (R_equal a1) -> a2 -> a2) -> ((T4 a1) -> (T4 a1) ->
               Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
               Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
               (Compare Prelude.Int) -> () -> () -> a2) -> ((T4 a1) -> (T4
               a1) -> (T4 a1) -> () -> (T4 a1) -> () -> () -> a2) -> (T4 
               a1) -> (T4 a1) -> Prelude.Bool -> (R_equal a1) -> a2
r_equal_rec cmp =
  r_equal_rect cmp

equal_rect :: (a1 -> a1 -> Prelude.Bool) -> ((T4 a1) -> (T4 a1) -> () -> ()
              -> a2) -> ((T4 a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> ((T4
              a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> ([]
              ((,) Prelude.Int a1)) -> () -> (Compare Prelude.Int) -> () ->
              () -> a2) -> ((T4 a1) -> (T4 a1) -> (T4 a1) -> () -> (T4 
              a1) -> () -> () -> a2) -> (T4 a1) -> (T4 a1) -> a2
equal_rect cmp f2 f1 f0 f m m' =
  
    (let {f3 = f2 m m'} in
     let {f4 = f1 m m'} in
     let {f5 = f0 m m'} in
     let {f6 = f m m'} in
     let {f7 = f6 m __} in
     let {f8 = f7 m' __} in
     case m of {
      [] ->
       let {f9 = f3 __} in
       case m' of {
        [] -> f9 __;
        (:) _ _ -> f8 __};
      (:) p l ->
       case p of {
        (,) t0 e ->
         let {f9 = f5 t0 e l __} in
         let {f10 = f4 t0 e l __} in
         case m' of {
          [] -> f8 __;
          (:) p0 l0 ->
           case p0 of {
            (,) t1 e0 ->
             let {f11 = f9 t1 e0 l0 __} in
             let {f12 = let {_x = compare1 t0 t1} in f11 _x __} in
             let {f13 = f10 t1 e0 l0 __} in
             let {
              f14 = \_ _ ->
               let {hrec = equal_rect cmp f2 f1 f0 f l l0} in f13 __ __ hrec}
             in
             case compare1 t0 t1 of {
              EQ -> f14 __ __;
              _ -> f12 __}}}}})

equal_rec :: (a1 -> a1 -> Prelude.Bool) -> ((T4 a1) -> (T4 a1) -> () -> () ->
             a2) -> ((T4 a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([]
             ((,) Prelude.Int a1)) -> () -> Prelude.Int -> a1 -> ([]
             ((,) Prelude.Int a1)) -> () -> () -> () -> a2 -> a2) -> ((T4 
             a1) -> (T4 a1) -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1))
             -> () -> Prelude.Int -> a1 -> ([] ((,) Prelude.Int a1)) -> () ->
             (Compare Prelude.Int) -> () -> () -> a2) -> ((T4 a1) -> (T4 
             a1) -> (T4 a1) -> () -> (T4 a1) -> () -> () -> a2) -> (T4 
             a1) -> (T4 a1) -> a2
equal_rec cmp =
  equal_rect cmp

r_equal_correct :: (a1 -> a1 -> Prelude.Bool) -> (T4 a1) -> (T4 a1) ->
                   Prelude.Bool -> R_equal a1
r_equal_correct cmp m m' _res =
  equal_rect cmp (\y y0 _ _ _ _ ->  (R_equal_0 y y0))
    (\y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ ->
     (R_equal_1 y y0 y1 y2 y3 y5 y6 y7 (equal cmp y3 y7)
      (y11 (equal cmp y3 y7) __))) (\y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ ->
     (R_equal_2 y y0 y1 y2 y3 y5 y6 y7 y9)) (\y y0 y1 _ y3 _ _ _ _ ->
     (R_equal_3 y y0 y1 y3)) m m' _res __

map0 :: (a1 -> a2) -> (T4 a1) -> T4 a2
map0 f m =
  case m of {
   [] -> [];
   (:) p m' ->
    case p of {
     (,) k e -> (:) ((,) k (f e)) (map0 f m')}}

mapi :: (Key -> a1 -> a2) -> (T4 a1) -> T4 a2
mapi f m =
  case m of {
   [] -> [];
   (:) p m' ->
    case p of {
     (,) k e -> (:) ((,) k (f k e)) (mapi f m')}}

option_cons :: Key -> (Prelude.Maybe a1) -> ([] ((,) Key a1)) -> []
               ((,) Key a1)
option_cons k o l =
  case o of {
   Prelude.Just e -> (:) ((,) k e) l;
   Prelude.Nothing -> l}

map2_l :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe 
          a3) -> (T4 a1) -> T4 a3
map2_l f m =
  case m of {
   [] -> [];
   (:) p l ->
    case p of {
     (,) k e ->
      option_cons k (f (Prelude.Just e) Prelude.Nothing) (map2_l f l)}}

map2_r :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe 
          a3) -> (T4 a2) -> T4 a3
map2_r f m' =
  case m' of {
   [] -> [];
   (:) p l' ->
    case p of {
     (,) k e' ->
      option_cons k (f Prelude.Nothing (Prelude.Just e')) (map2_r f l')}}

map2 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (T4
        a1) -> (T4 a2) -> T4 a3
map2 f m =
  case m of {
   [] -> map2_r f;
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       map2_aux m' =
         case m' of {
          [] -> map2_l f m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case compare1 k k' of {
              LT ->
               option_cons k (f (Prelude.Just e) Prelude.Nothing)
                 (map2 f l m');
              EQ ->
               option_cons k (f (Prelude.Just e) (Prelude.Just e'))
                 (map2 f l l');
              GT ->
               option_cons k' (f Prelude.Nothing (Prelude.Just e'))
                 (map2_aux l')}}}}
      in map2_aux}}

combine :: (T4 a1) -> (T4 a2) -> T4
           ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
combine m =
  case m of {
   [] -> map0 (\e' -> (,) Prelude.Nothing (Prelude.Just e'));
   (:) p l ->
    case p of {
     (,) k e ->
      let {
       combine_aux m' =
         case m' of {
          [] -> map0 (\e0 -> (,) (Prelude.Just e0) Prelude.Nothing) m;
          (:) p0 l' ->
           case p0 of {
            (,) k' e' ->
             case compare1 k k' of {
              LT -> (:) ((,) k ((,) (Prelude.Just e) Prelude.Nothing))
               (combine l m');
              EQ -> (:) ((,) k ((,) (Prelude.Just e) (Prelude.Just e')))
               (combine l l');
              GT -> (:) ((,) k' ((,) Prelude.Nothing (Prelude.Just e')))
               (combine_aux l')}}}}
      in combine_aux}}

fold_right_pair :: (a1 -> a2 -> a3 -> a3) -> ([] ((,) a1 a2)) -> a3 -> a3
fold_right_pair f l i =
  Data.List.foldr (\p -> f (Prelude.fst p) (Prelude.snd p)) i l

map2_alt :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe 
            a3) -> (T4 a1) -> (T4 a2) -> [] ((,) Key a3)
map2_alt f m m' =
  let {m0 = combine m m'} in
  let {m1 = map0 (\p -> f (Prelude.fst p) (Prelude.snd p)) m0} in
  fold_right_pair option_cons m1 []

at_least_one :: (Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe
                ((,) (Prelude.Maybe a1) (Prelude.Maybe a2))
at_least_one o o' =
  case o of {
   Prelude.Just _ -> Prelude.Just ((,) o o');
   Prelude.Nothing ->
    case o' of {
     Prelude.Just _ -> Prelude.Just ((,) o o');
     Prelude.Nothing -> Prelude.Nothing}}

at_least_one_then_f :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) ->
                       Prelude.Maybe a3) -> (Prelude.Maybe a1) ->
                       (Prelude.Maybe a2) -> Prelude.Maybe a3
at_least_one_then_f f o o' =
  case o of {
   Prelude.Just _ -> f o o';
   Prelude.Nothing ->
    case o' of {
     Prelude.Just _ -> f o o';
     Prelude.Nothing -> Prelude.Nothing}}

type T5 = Prelude.Int

compare4 :: Prelude.Int -> Prelude.Int -> Compare Prelude.Int
compare4 x y =
  case compare0 x y of {
   Prelude.EQ -> EQ;
   Prelude.LT -> LT;
   Prelude.GT -> GT}

eq_dec6 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eq_dec6 =
  eq_dec0

type Key0 = Prelude.Int

type Slist elt =
  T4 elt
  -- singleton inductive, whose constructor was Build_slist
  
this :: (Slist a1) -> T4 a1
this s =
  s

type T6 elt = Slist elt

empty0 :: T6 a1
empty0 =
  empty

is_empty0 :: (T6 a1) -> Prelude.Bool
is_empty0 m =
  is_empty (this m)

add1 :: Key0 -> a1 -> (T6 a1) -> T6 a1
add1 x e m =
  add0 x e (this m)

find0 :: Key0 -> (T6 a1) -> Prelude.Maybe a1
find0 x m =
  find x (this m)

remove0 :: Key0 -> (T6 a1) -> T6 a1
remove0 x m =
  remove x (this m)

mem0 :: Key0 -> (T6 a1) -> Prelude.Bool
mem0 x m =
  mem x (this m)

map1 :: (a1 -> a2) -> (T6 a1) -> T6 a2
map1 f m =
  map0 f (this m)

mapi0 :: (Key0 -> a1 -> a2) -> (T6 a1) -> T6 a2
mapi0 f m =
  mapi f (this m)

map3 :: ((Prelude.Maybe a1) -> (Prelude.Maybe a2) -> Prelude.Maybe a3) -> (T6
        a1) -> (T6 a2) -> T6 a3
map3 f m m' =
  map2 f (this m) (this m')

elements0 :: (T6 a1) -> [] ((,) Key0 a1)
elements0 m =
  elements (this m)

cardinal :: (T6 a1) -> Prelude.Int
cardinal m =
  (Data.List.length :: [a] -> Prelude.Int) (this m)

fold0 :: (Key0 -> a1 -> a2 -> a2) -> (T6 a1) -> a2 -> a2
fold0 f m i =
  fold f (this m) i

equal0 :: (a1 -> a1 -> Prelude.Bool) -> (T6 a1) -> (T6 a1) -> Prelude.Bool
equal0 cmp m m' =
  equal cmp (this m) (this m')

eqb3 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb3 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec m x =
  let {b = mem0 x m} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

uncurry :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry f p =
  f (Prelude.fst p) (Prelude.snd p)

of_list :: ([] ((,) Key0 a1)) -> T6 a1
of_list =
  Data.List.foldr (uncurry add1) empty0

to_list :: (T6 a1) -> [] ((,) Key0 a1)
to_list x =
  elements0 x

fold_rec0 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> () ->
             a3) -> (Key0 -> a1 -> a2 -> (T6 a1) -> (T6 a1) -> () -> () -> ()
             -> a3 -> a3) -> a3
fold_rec0 f i m hempty hstep =
  
    (let {f0 = uncurry f} in
     let {l = rev (elements0 m)} in
     let {
      hstep' = \k e a m' m'' x ->
       hstep (Prelude.fst ((,) k e)) (Prelude.snd ((,) k e)) a m' m'' __ __
         __ x}
     in
     list_rect (\_ _ m0 _ -> hempty m0 __) (\a l0 iHl hstep'0 _ m0 _ ->
       case a of {
        (,) k e ->
         hstep'0 k e (Data.List.foldr f0 i l0) (of_list l0) m0 __ __ __
           (iHl (\k0 e0 a0 m' m'' _ _ _ x ->
             hstep'0 k0 e0 a0 m' m'' __ __ __ x) __ (of_list l0) __)}) l
       (\k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) __ m __)

fold_rec_bis :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> (T6
                a1) -> a2 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 ->
                (T6 a1) -> () -> () -> a3 -> a3) -> a3
fold_rec_bis f i m pmorphism pempty pstep =
  fold_rec0 f i m (\m0 _ -> pmorphism empty0 m0 i __ pempty)
    (\k e a m' m'' _ _ _ x ->
    pmorphism (add1 k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

fold_rec_nodep :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> a3 -> (Key0 ->
                  a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rec_nodep f i m x x0 =
  fold_rec_bis f i m (\_ _ _ _ x1 -> x1) x (\k e a _ _ _ x1 ->
    x0 k e a __ x1)

fold_rec_weak :: (Key0 -> a1 -> a2 -> a2) -> a2 -> ((T6 a1) -> (T6 a1) -> a2
                 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 -> (T6 
                 a1) -> () -> a3 -> a3) -> (T6 a1) -> a3
fold_rec_weak f i x x0 x1 m =
  fold_rec_bis f i m x x0 (\k e a m' _ _ x2 -> x1 k e a m' __ x2)

fold_rel :: (Key0 -> a1 -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> a2 -> a3
            -> (T6 a1) -> a4 -> (Key0 -> a1 -> a2 -> a3 -> () -> a4 -> a4) ->
            a4
fold_rel f g i j m rempty rstep =
  
    (
      (let {l = rev (elements0 m)} in
       let {rstep' = \k e a b x -> rstep k e a b __ x} in
       list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 (Prelude.fst a) (Prelude.snd a)
           (Data.List.foldr (uncurry f) i l0)
           (Data.List.foldr (uncurry g) j l0) __
           (iHl (\k e a0 b _ x -> rstep'0 k e a0 b __ x))) l (\k e a b _ x ->
         rstep' k e a b x)))

map_induction :: ((T6 a1) -> () -> a2) -> ((T6 a1) -> (T6 a1) -> a2 -> Key0
                 -> a1 -> () -> () -> a2) -> (T6 a1) -> a2
map_induction x x0 m =
  fold_rec0 (\_ _ _ -> ()) () m x (\k e _ m' m'' _ _ _ x1 ->
    x0 m' m'' x1 k e __ __)

map_induction_bis :: ((T6 a1) -> (T6 a1) -> () -> a2 -> a2) -> a2 -> (Key0 ->
                     a1 -> (T6 a1) -> () -> a2 -> a2) -> (T6 a1) -> a2
map_induction_bis x x0 x1 m =
  fold_rec_bis (\_ _ _ -> ()) () m (\m0 m' _ _ x2 -> x m0 m' __ x2) x0
    (\k e _ m' _ _ x2 -> x1 k e m' __ x2)

cardinal_inv_2 :: (T6 a1) -> Prelude.Int -> ((,) Key0 a1)
cardinal_inv_2 m _ =
  let {l = elements0 m} in
  case l of {
   [] -> false_rect;
   (:) p _ -> p}

cardinal_inv_2b :: (T6 a1) -> ((,) Key0 a1)
cardinal_inv_2b m =
  let {n = cardinal m} in
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    false_rect (\x _ -> cardinal_inv_2 m x))
    (\n0 ->
    cardinal_inv_2 m n0)
    n

filter :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter f m =
  fold0 (\k e m0 ->
    case f k e of {
     Prelude.True -> add1 k e m0;
     Prelude.False -> m0}) m empty0

for_all :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> b;
     Prelude.False -> Prelude.False}) m Prelude.True

exists_ :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_ f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> Prelude.True;
     Prelude.False -> b}) m Prelude.False

partition :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition f m =
  (,) (filter f m) (filter (\k e -> Prelude.not (f k e)) m)

update :: (T6 a1) -> (T6 a1) -> T6 a1
update m1 m2 =
  fold0 add1 m2 m1

restrict :: (T6 a1) -> (T6 a1) -> T6 a1
restrict m1 m2 =
  filter (\k _ -> mem0 k m2) m1

diff :: (T6 a1) -> (T6 a1) -> T6 a1
diff m1 m2 =
  filter (\k _ -> Prelude.not (mem0 k m2)) m1

partition_In :: (T6 a1) -> (T6 a1) -> (T6 a1) -> Key0 -> Prelude.Bool
partition_In _ m1 _ k =
  in_dec m1 k

update_dec :: (T6 a1) -> (T6 a1) -> Key0 -> a1 -> Prelude.Bool
update_dec _ m' k _ =
  in_dec m' k

filter_dom :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_dom f =
  filter (\k _ -> f k)

filter_range :: (a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_range f =
  filter (\_ -> f)

for_all_dom :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_dom f =
  for_all (\k _ -> f k)

for_all_range :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_range f =
  for_all (\_ -> f)

exists_dom :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_dom f =
  exists_ (\k _ -> f k)

exists_range :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_range f =
  exists_ (\_ -> f)

partition_dom :: (Key0 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_dom f =
  partition (\k _ -> f k)

partition_range :: (a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_range f =
  partition (\_ -> f)

eqb4 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb4 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec0 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec0 m x =
  in_dec m x

take_first :: (Key0 -> a1 -> Prelude.Bool) -> Key0 -> a1 -> (Prelude.Maybe
              ((,) Key0 a1)) -> Prelude.Maybe ((,) Key0 a1)
take_first f k e x0 =
  case x0 of {
   Prelude.Just _ -> x0;
   Prelude.Nothing ->
    case f k e of {
     Prelude.True -> Prelude.Just ((,) k e);
     Prelude.False -> Prelude.Nothing}}

singleton :: Key0 -> a1 -> T6 a1
singleton k e =
  add1 k e empty0

keep_keys :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
keep_keys p =
  filter (\k _ -> p k)

eqb5 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb5 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec1 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec1 m x =
  in_dec m x

uncurry0 :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry0 f p =
  f (Prelude.fst p) (Prelude.snd p)

of_list0 :: ([] ((,) Key0 a1)) -> T6 a1
of_list0 =
  Data.List.foldr (uncurry0 add1) empty0

to_list0 :: (T6 a1) -> [] ((,) Key0 a1)
to_list0 x =
  elements0 x

fold_rec1 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> () ->
             a3) -> (Key0 -> a1 -> a2 -> (T6 a1) -> (T6 a1) -> () -> () -> ()
             -> a3 -> a3) -> a3
fold_rec1 f i m x x0 =
  fold_rec0 f i m x x0

fold_rec_bis0 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> (T6
                 a1) -> a2 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 ->
                 (T6 a1) -> () -> () -> a3 -> a3) -> a3
fold_rec_bis0 f i m x x0 x1 =
  fold_rec_bis f i m x x0 x1

fold_rec_nodep0 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> a3 -> (Key0
                   -> a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rec_nodep0 f i m x x0 =
  fold_rec_nodep f i m x x0

fold_rec_weak0 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> ((T6 a1) -> (T6 a1) -> a2
                  -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 -> (T6 
                  a1) -> () -> a3 -> a3) -> (T6 a1) -> a3
fold_rec_weak0 f i x x0 x1 m =
  fold_rec_weak f i x x0 x1 m

fold_rel0 :: (Key0 -> a1 -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> a2 -> a3
             -> (T6 a1) -> a4 -> (Key0 -> a1 -> a2 -> a3 -> () -> a4 -> a4)
             -> a4
fold_rel0 f g i j m x x0 =
  fold_rel f g i j m x x0

map_induction0 :: ((T6 a1) -> () -> a2) -> ((T6 a1) -> (T6 a1) -> a2 -> Key0
                  -> a1 -> () -> () -> a2) -> (T6 a1) -> a2
map_induction0 x x0 m =
  map_induction x x0 m

map_induction_bis0 :: ((T6 a1) -> (T6 a1) -> () -> a2 -> a2) -> a2 -> (Key0
                      -> a1 -> (T6 a1) -> () -> a2 -> a2) -> (T6 a1) -> a2
map_induction_bis0 x x0 x1 m =
  map_induction_bis x x0 x1 m

cardinal_inv_0 :: (T6 a1) -> Prelude.Int -> ((,) Key0 a1)
cardinal_inv_0 m n =
  cardinal_inv_2 m n

cardinal_inv_2b0 :: (T6 a1) -> ((,) Key0 a1)
cardinal_inv_2b0 m =
  cardinal_inv_2b m

filter0 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter0 f m =
  fold0 (\k e m0 ->
    case f k e of {
     Prelude.True -> add1 k e m0;
     Prelude.False -> m0}) m empty0

for_all0 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all0 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> b;
     Prelude.False -> Prelude.False}) m Prelude.True

exists_0 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_0 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> Prelude.True;
     Prelude.False -> b}) m Prelude.False

partition0 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition0 f m =
  (,) (filter0 f m) (filter0 (\k e -> Prelude.not (f k e)) m)

update0 :: (T6 a1) -> (T6 a1) -> T6 a1
update0 m1 m2 =
  fold0 add1 m2 m1

restrict0 :: (T6 a1) -> (T6 a1) -> T6 a1
restrict0 m1 m2 =
  filter0 (\k _ -> mem0 k m2) m1

diff0 :: (T6 a1) -> (T6 a1) -> T6 a1
diff0 m1 m2 =
  filter0 (\k _ -> Prelude.not (mem0 k m2)) m1

partition_In0 :: (T6 a1) -> (T6 a1) -> (T6 a1) -> Key0 -> Prelude.Bool
partition_In0 _ m1 _ k =
  in_dec1 m1 k

update_dec0 :: (T6 a1) -> (T6 a1) -> Key0 -> a1 -> Prelude.Bool
update_dec0 _ m' k _ =
  in_dec1 m' k

filter_dom0 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_dom0 f =
  filter0 (\k _ -> f k)

filter_range0 :: (a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_range0 f =
  filter0 (\_ -> f)

for_all_dom0 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_dom0 f =
  for_all0 (\k _ -> f k)

for_all_range0 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_range0 f =
  for_all0 (\_ -> f)

exists_dom0 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_dom0 f =
  exists_0 (\k _ -> f k)

exists_range0 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_range0 f =
  exists_0 (\_ -> f)

partition_dom0 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_dom0 f =
  partition0 (\k _ -> f k)

partition_range0 :: (a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_range0 f =
  partition0 (\_ -> f)

eqb6 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb6 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec2 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec2 m x =
  in_dec m x

data HeapState =
   Build_HeapState (T6 Size) (T6 Word)

heapState_rect :: ((T6 Size) -> (T6 Word) -> a1) -> HeapState -> a1
heapState_rect f h =
  case h of {
   Build_HeapState x x0 -> f x x0}

heapState_rec :: ((T6 Size) -> (T6 Word) -> a1) -> HeapState -> a1
heapState_rec =
  heapState_rect

resvs :: HeapState -> T6 Size
resvs h =
  case h of {
   Build_HeapState resvs1 _ -> resvs1}

bytes :: HeapState -> T6 Word
bytes h =
  case h of {
   Build_HeapState _ bytes1 -> bytes1}

newHeapState :: HeapState
newHeapState =
  Build_HeapState empty0 empty0

emptyS0 :: Prelude.String
emptyS0 =
  (:) 'e' ((:) 'm' ((:) 'p' ((:) 't' ((:) 'y' []))))

allocS :: Prelude.String
allocS =
  (:) 'a' ((:) 'l' ((:) 'l' ((:) 'o' ((:) 'c' []))))

freeS :: Prelude.String
freeS =
  (:) 'f' ((:) 'r' ((:) 'e' ((:) 'e' [])))

reallocS :: Prelude.String
reallocS =
  (:) 'r' ((:) 'e' ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'o' ((:) 'c' []))))))

peekS :: Prelude.String
peekS =
  (:) 'p' ((:) 'e' ((:) 'e' ((:) 'k' [])))

pokeS :: Prelude.String
pokeS =
  (:) 'p' ((:) 'o' ((:) 'k' ((:) 'e' [])))

memcpyS :: Prelude.String
memcpyS =
  (:) 'm' ((:) 'e' ((:) 'm' ((:) 'c' ((:) 'p' ((:) 'y' [])))))

memsetS :: Prelude.String
memsetS =
  (:) 'm' ((:) 'e' ((:) 'm' ((:) 's' ((:) 'e' ((:) 't' [])))))

readS :: Prelude.String
readS =
  (:) 'r' ((:) 'e' ((:) 'a' ((:) 'd' [])))

writeS :: Prelude.String
writeS =
  (:) 'w' ((:) 'r' ((:) 'i' ((:) 't' ((:) 'e' []))))

data PS =
   MakePS (Ptr Word) Size Size Size

pS_rect :: ((Ptr Word) -> Size -> Size -> Size -> a1) -> PS -> a1
pS_rect f p =
  case p of {
   MakePS x x0 x1 x2 -> f x x0 x1 x2}

pS_rec :: ((Ptr Word) -> Size -> Size -> Size -> a1) -> PS -> a1
pS_rec =
  pS_rect

psBuffer :: PS -> Ptr Word
psBuffer p =
  case p of {
   MakePS psBuffer1 _ _ _ -> psBuffer1}

psBufLen :: PS -> Size
psBufLen p =
  case p of {
   MakePS _ psBufLen1 _ _ -> psBufLen1}

psOffset :: PS -> Size
psOffset p =
  case p of {
   MakePS _ _ psOffset1 _ -> psOffset1}

psLength :: PS -> Size
psLength p =
  case p of {
   MakePS _ _ _ psLength1 -> psLength1}

simply_widen_region :: PS -> Prelude.Int -> PS
simply_widen_region r n =
  MakePS (psBuffer r) (psBufLen r) ((Prelude.-) (psOffset r) n)
    ((Prelude.+) (psLength r) n)

alloc_quantum :: Prelude.Int
alloc_quantum =
  (\x -> x) 1

type Bsrep = (,) Rep PS

type CHeapRep = CRep

type Crep = CRep

emptyHeap :: Crep
emptyHeap =
  unsafeCoerce ((,) 0 (Build_HeapState [] []))

eqb7 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb7 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec3 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec3 m x =
  let {b = mem0 x m} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

uncurry1 :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry1 f p =
  f (Prelude.fst p) (Prelude.snd p)

of_list1 :: ([] ((,) Key0 a1)) -> T6 a1
of_list1 =
  Data.List.foldr (uncurry1 add1) empty0

to_list1 :: (T6 a1) -> [] ((,) Key0 a1)
to_list1 x =
  elements0 x

fold_rec2 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> () ->
             a3) -> (Key0 -> a1 -> a2 -> (T6 a1) -> (T6 a1) -> () -> () -> ()
             -> a3 -> a3) -> a3
fold_rec2 f i m hempty hstep =
  
    (let {f0 = uncurry1 f} in
     let {l = rev (elements0 m)} in
     let {
      hstep' = \k e a m' m'' x ->
       hstep (Prelude.fst ((,) k e)) (Prelude.snd ((,) k e)) a m' m'' __ __
         __ x}
     in
     list_rect (\_ _ m0 _ -> hempty m0 __) (\a l0 iHl hstep'0 _ m0 _ ->
       case a of {
        (,) k e ->
         hstep'0 k e (Data.List.foldr f0 i l0) (of_list1 l0) m0 __ __ __
           (iHl (\k0 e0 a0 m' m'' _ _ _ x ->
             hstep'0 k0 e0 a0 m' m'' __ __ __ x) __ (of_list1 l0) __)}) l
       (\k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) __ m __)

fold_rec_bis1 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> (T6
                 a1) -> a2 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 ->
                 (T6 a1) -> () -> () -> a3 -> a3) -> a3
fold_rec_bis1 f i m pmorphism pempty pstep =
  fold_rec2 f i m (\m0 _ -> pmorphism empty0 m0 i __ pempty)
    (\k e a m' m'' _ _ _ x ->
    pmorphism (add1 k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

fold_rec_nodep1 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> a3 -> (Key0
                   -> a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rec_nodep1 f i m x x0 =
  fold_rec_bis1 f i m (\_ _ _ _ x1 -> x1) x (\k e a _ _ _ x1 ->
    x0 k e a __ x1)

fold_rec_weak1 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> ((T6 a1) -> (T6 a1) -> a2
                  -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 -> (T6 
                  a1) -> () -> a3 -> a3) -> (T6 a1) -> a3
fold_rec_weak1 f i x x0 x1 m =
  fold_rec_bis1 f i m x x0 (\k e a m' _ _ x2 -> x1 k e a m' __ x2)

fold_rel1 :: (Key0 -> a1 -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> a2 -> a3
             -> (T6 a1) -> a4 -> (Key0 -> a1 -> a2 -> a3 -> () -> a4 -> a4)
             -> a4
fold_rel1 f g i j m rempty rstep =
  
    (
      (let {l = rev (elements0 m)} in
       let {rstep' = \k e a b x -> rstep k e a b __ x} in
       list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 (Prelude.fst a) (Prelude.snd a)
           (Data.List.foldr (uncurry1 f) i l0)
           (Data.List.foldr (uncurry1 g) j l0) __
           (iHl (\k e a0 b _ x -> rstep'0 k e a0 b __ x))) l (\k e a b _ x ->
         rstep' k e a b x)))

map_induction1 :: ((T6 a1) -> () -> a2) -> ((T6 a1) -> (T6 a1) -> a2 -> Key0
                  -> a1 -> () -> () -> a2) -> (T6 a1) -> a2
map_induction1 x x0 m =
  fold_rec2 (\_ _ _ -> ()) () m x (\k e _ m' m'' _ _ _ x1 ->
    x0 m' m'' x1 k e __ __)

map_induction_bis1 :: ((T6 a1) -> (T6 a1) -> () -> a2 -> a2) -> a2 -> (Key0
                      -> a1 -> (T6 a1) -> () -> a2 -> a2) -> (T6 a1) -> a2
map_induction_bis1 x x0 x1 m =
  fold_rec_bis1 (\_ _ _ -> ()) () m (\m0 m' _ _ x2 -> x m0 m' __ x2) x0
    (\k e _ m' _ _ x2 -> x1 k e m' __ x2)

cardinal_inv_1 :: (T6 a1) -> Prelude.Int -> ((,) Key0 a1)
cardinal_inv_1 m _ =
  let {l = elements0 m} in
  case l of {
   [] -> false_rect;
   (:) p _ -> p}

cardinal_inv_2b1 :: (T6 a1) -> ((,) Key0 a1)
cardinal_inv_2b1 m =
  let {n = cardinal m} in
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    false_rect (\x _ -> cardinal_inv_1 m x))
    (\n0 ->
    cardinal_inv_1 m n0)
    n

filter1 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter1 f m =
  fold0 (\k e m0 ->
    case f k e of {
     Prelude.True -> add1 k e m0;
     Prelude.False -> m0}) m empty0

for_all1 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all1 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> b;
     Prelude.False -> Prelude.False}) m Prelude.True

exists_1 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_1 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> Prelude.True;
     Prelude.False -> b}) m Prelude.False

partition1 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition1 f m =
  (,) (filter1 f m) (filter1 (\k e -> Prelude.not (f k e)) m)

update1 :: (T6 a1) -> (T6 a1) -> T6 a1
update1 m1 m2 =
  fold0 add1 m2 m1

restrict1 :: (T6 a1) -> (T6 a1) -> T6 a1
restrict1 m1 m2 =
  filter1 (\k _ -> mem0 k m2) m1

diff1 :: (T6 a1) -> (T6 a1) -> T6 a1
diff1 m1 m2 =
  filter1 (\k _ -> Prelude.not (mem0 k m2)) m1

partition_In1 :: (T6 a1) -> (T6 a1) -> (T6 a1) -> Key0 -> Prelude.Bool
partition_In1 _ m1 _ k =
  in_dec3 m1 k

update_dec1 :: (T6 a1) -> (T6 a1) -> Key0 -> a1 -> Prelude.Bool
update_dec1 _ m' k _ =
  in_dec3 m' k

filter_dom1 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_dom1 f =
  filter1 (\k _ -> f k)

filter_range1 :: (a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_range1 f =
  filter1 (\_ -> f)

for_all_dom1 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_dom1 f =
  for_all1 (\k _ -> f k)

for_all_range1 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_range1 f =
  for_all1 (\_ -> f)

exists_dom1 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_dom1 f =
  exists_1 (\k _ -> f k)

exists_range1 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_range1 f =
  exists_1 (\_ -> f)

partition_dom1 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_dom1 f =
  partition1 (\k _ -> f k)

partition_range1 :: (a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_range1 f =
  partition1 (\_ -> f)

eqb8 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb8 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec4 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec4 m x =
  in_dec3 m x

take_first0 :: (Key0 -> a1 -> Prelude.Bool) -> Key0 -> a1 -> (Prelude.Maybe
               ((,) Key0 a1)) -> Prelude.Maybe ((,) Key0 a1)
take_first0 f k e x0 =
  case x0 of {
   Prelude.Just _ -> x0;
   Prelude.Nothing ->
    case f k e of {
     Prelude.True -> Prelude.Just ((,) k e);
     Prelude.False -> Prelude.Nothing}}

singleton0 :: Key0 -> a1 -> T6 a1
singleton0 k e =
  add1 k e empty0

keep_keys0 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
keep_keys0 p =
  filter1 (\k _ -> p k)

eqb9 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb9 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec5 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec5 m x =
  in_dec3 m x

uncurry2 :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry2 f p =
  f (Prelude.fst p) (Prelude.snd p)

of_list2 :: ([] ((,) Key0 a1)) -> T6 a1
of_list2 =
  Data.List.foldr (uncurry2 add1) empty0

to_list2 :: (T6 a1) -> [] ((,) Key0 a1)
to_list2 x =
  elements0 x

fold_rec3 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> () ->
             a3) -> (Key0 -> a1 -> a2 -> (T6 a1) -> (T6 a1) -> () -> () -> ()
             -> a3 -> a3) -> a3
fold_rec3 f i m x x0 =
  fold_rec2 f i m x x0

fold_rec_bis2 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> (T6
                 a1) -> a2 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 ->
                 (T6 a1) -> () -> () -> a3 -> a3) -> a3
fold_rec_bis2 f i m x x0 x1 =
  fold_rec_bis1 f i m x x0 x1

fold_rec_nodep2 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> a3 -> (Key0
                   -> a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rec_nodep2 f i m x x0 =
  fold_rec_nodep1 f i m x x0

fold_rec_weak2 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> ((T6 a1) -> (T6 a1) -> a2
                  -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 -> (T6 
                  a1) -> () -> a3 -> a3) -> (T6 a1) -> a3
fold_rec_weak2 f i x x0 x1 m =
  fold_rec_weak1 f i x x0 x1 m

fold_rel2 :: (Key0 -> a1 -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> a2 -> a3
             -> (T6 a1) -> a4 -> (Key0 -> a1 -> a2 -> a3 -> () -> a4 -> a4)
             -> a4
fold_rel2 f g i j m x x0 =
  fold_rel1 f g i j m x x0

map_induction2 :: ((T6 a1) -> () -> a2) -> ((T6 a1) -> (T6 a1) -> a2 -> Key0
                  -> a1 -> () -> () -> a2) -> (T6 a1) -> a2
map_induction2 x x0 m =
  map_induction1 x x0 m

map_induction_bis2 :: ((T6 a1) -> (T6 a1) -> () -> a2 -> a2) -> a2 -> (Key0
                      -> a1 -> (T6 a1) -> () -> a2 -> a2) -> (T6 a1) -> a2
map_induction_bis2 x x0 x1 m =
  map_induction_bis1 x x0 x1 m

cardinal_inv_3 :: (T6 a1) -> Prelude.Int -> ((,) Key0 a1)
cardinal_inv_3 m n =
  cardinal_inv_1 m n

cardinal_inv_2b2 :: (T6 a1) -> ((,) Key0 a1)
cardinal_inv_2b2 m =
  cardinal_inv_2b1 m

filter2 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter2 f m =
  fold0 (\k e m0 ->
    case f k e of {
     Prelude.True -> add1 k e m0;
     Prelude.False -> m0}) m empty0

for_all2 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all2 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> b;
     Prelude.False -> Prelude.False}) m Prelude.True

exists_2 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_2 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> Prelude.True;
     Prelude.False -> b}) m Prelude.False

partition2 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition2 f m =
  (,) (filter2 f m) (filter2 (\k e -> Prelude.not (f k e)) m)

update2 :: (T6 a1) -> (T6 a1) -> T6 a1
update2 m1 m2 =
  fold0 add1 m2 m1

restrict2 :: (T6 a1) -> (T6 a1) -> T6 a1
restrict2 m1 m2 =
  filter2 (\k _ -> mem0 k m2) m1

diff2 :: (T6 a1) -> (T6 a1) -> T6 a1
diff2 m1 m2 =
  filter2 (\k _ -> Prelude.not (mem0 k m2)) m1

partition_In2 :: (T6 a1) -> (T6 a1) -> (T6 a1) -> Key0 -> Prelude.Bool
partition_In2 _ m1 _ k =
  in_dec5 m1 k

update_dec2 :: (T6 a1) -> (T6 a1) -> Key0 -> a1 -> Prelude.Bool
update_dec2 _ m' k _ =
  in_dec5 m' k

filter_dom2 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_dom2 f =
  filter2 (\k _ -> f k)

filter_range2 :: (a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_range2 f =
  filter2 (\_ -> f)

for_all_dom2 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_dom2 f =
  for_all2 (\k _ -> f k)

for_all_range2 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_range2 f =
  for_all2 (\_ -> f)

exists_dom2 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_dom2 f =
  exists_2 (\k _ -> f k)

exists_range2 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_range2 f =
  exists_2 (\_ -> f)

partition_dom2 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_dom2 f =
  partition2 (\k _ -> f k)

partition_range2 :: (a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_range2 f =
  partition2 (\_ -> f)

eqb10 :: (Ptr Word) -> (Ptr Word) -> Prelude.Bool
eqb10 x y =
  case eq_dec3 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec6 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec6 m x =
  in_dec3 m x

data HeapState0 =
   Build_HeapState0 (T6 Size) (T6 Word)

heapState_rect0 :: ((T6 Size) -> (T6 Word) -> a1) -> HeapState0 -> a1
heapState_rect0 f h =
  case h of {
   Build_HeapState0 x x0 -> f x x0}

heapState_rec0 :: ((T6 Size) -> (T6 Word) -> a1) -> HeapState0 -> a1
heapState_rec0 =
  heapState_rect0

resvs0 :: HeapState0 -> T6 Size
resvs0 h =
  case h of {
   Build_HeapState0 resvs1 _ -> resvs1}

bytes0 :: HeapState0 -> T6 Word
bytes0 h =
  case h of {
   Build_HeapState0 _ bytes1 -> bytes1}

newHeapState0 :: HeapState0
newHeapState0 =
  Build_HeapState0 empty0 empty0

emptyS1 :: Prelude.String
emptyS1 =
  (:) 'e' ((:) 'm' ((:) 'p' ((:) 't' ((:) 'y' []))))

allocS0 :: Prelude.String
allocS0 =
  (:) 'a' ((:) 'l' ((:) 'l' ((:) 'o' ((:) 'c' []))))

freeS0 :: Prelude.String
freeS0 =
  (:) 'f' ((:) 'r' ((:) 'e' ((:) 'e' [])))

reallocS0 :: Prelude.String
reallocS0 =
  (:) 'r' ((:) 'e' ((:) 'a' ((:) 'l' ((:) 'l' ((:) 'o' ((:) 'c' []))))))

peekS0 :: Prelude.String
peekS0 =
  (:) 'p' ((:) 'e' ((:) 'e' ((:) 'k' [])))

pokeS0 :: Prelude.String
pokeS0 =
  (:) 'p' ((:) 'o' ((:) 'k' ((:) 'e' [])))

memcpyS0 :: Prelude.String
memcpyS0 =
  (:) 'm' ((:) 'e' ((:) 'm' ((:) 'c' ((:) 'p' ((:) 'y' [])))))

memsetS0 :: Prelude.String
memsetS0 =
  (:) 'm' ((:) 'e' ((:) 'm' ((:) 's' ((:) 'e' ((:) 't' [])))))

readS0 :: Prelude.String
readS0 =
  (:) 'r' ((:) 'e' ((:) 'a' ((:) 'd' [])))

writeS0 :: Prelude.String
writeS0 =
  (:) 'w' ((:) 'r' ((:) 'i' ((:) 't' ((:) 'e' []))))

data PS0 =
   MakePS0 (Ptr Word) Size Size Size

pS_rect0 :: ((Ptr Word) -> Size -> Size -> Size -> a1) -> PS0 -> a1
pS_rect0 f p =
  case p of {
   MakePS0 x x0 x1 x2 -> f x x0 x1 x2}

pS_rec0 :: ((Ptr Word) -> Size -> Size -> Size -> a1) -> PS0 -> a1
pS_rec0 =
  pS_rect0

psBuffer0 :: PS0 -> Ptr Word
psBuffer0 p =
  case p of {
   MakePS0 psBuffer1 _ _ _ -> psBuffer1}

psBufLen0 :: PS0 -> Size
psBufLen0 p =
  case p of {
   MakePS0 _ psBufLen1 _ _ -> psBufLen1}

psOffset0 :: PS0 -> Size
psOffset0 p =
  case p of {
   MakePS0 _ _ psOffset1 _ -> psOffset1}

psLength0 :: PS0 -> Size
psLength0 p =
  case p of {
   MakePS0 _ _ _ psLength1 -> psLength1}

simply_widen_region0 :: PS0 -> Prelude.Int -> PS0
simply_widen_region0 r n =
  MakePS0 (psBuffer0 r) (psBufLen0 r) ((Prelude.-) (psOffset0 r) n)
    ((Prelude.+) (psLength0 r) n)

alloc_quantum0 :: Prelude.Int
alloc_quantum0 =
  (\x -> x) 1

type Bsrep0 = (,) Rep PS0

eqb11 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb11 x y =
  case eq_dec2 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec7 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec7 m x =
  let {b = mem0 x m} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

uncurry3 :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
uncurry3 f p =
  f (Prelude.fst p) (Prelude.snd p)

of_list3 :: ([] ((,) Key0 a1)) -> T6 a1
of_list3 =
  Data.List.foldr (uncurry3 add1) empty0

to_list3 :: (T6 a1) -> [] ((,) Key0 a1)
to_list3 x =
  elements0 x

fold_rec4 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> () ->
             a3) -> (Key0 -> a1 -> a2 -> (T6 a1) -> (T6 a1) -> () -> () -> ()
             -> a3 -> a3) -> a3
fold_rec4 f i m hempty hstep =
  
    (let {f0 = uncurry3 f} in
     let {l = rev (elements0 m)} in
     let {
      hstep' = \k e a m' m'' x ->
       hstep (Prelude.fst ((,) k e)) (Prelude.snd ((,) k e)) a m' m'' __ __
         __ x}
     in
     list_rect (\_ _ m0 _ -> hempty m0 __) (\a l0 iHl hstep'0 _ m0 _ ->
       case a of {
        (,) k e ->
         hstep'0 k e (Data.List.foldr f0 i l0) (of_list3 l0) m0 __ __ __
           (iHl (\k0 e0 a0 m' m'' _ _ _ x ->
             hstep'0 k0 e0 a0 m' m'' __ __ __ x) __ (of_list3 l0) __)}) l
       (\k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) __ m __)

fold_rec_bis3 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> ((T6 a1) -> (T6
                 a1) -> a2 -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 ->
                 (T6 a1) -> () -> () -> a3 -> a3) -> a3
fold_rec_bis3 f i m pmorphism pempty pstep =
  fold_rec4 f i m (\m0 _ -> pmorphism empty0 m0 i __ pempty)
    (\k e a m' m'' _ _ _ x ->
    pmorphism (add1 k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

fold_rec_nodep3 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> (T6 a1) -> a3 -> (Key0
                   -> a1 -> a2 -> () -> a3 -> a3) -> a3
fold_rec_nodep3 f i m x x0 =
  fold_rec_bis3 f i m (\_ _ _ _ x1 -> x1) x (\k e a _ _ _ x1 ->
    x0 k e a __ x1)

fold_rec_weak3 :: (Key0 -> a1 -> a2 -> a2) -> a2 -> ((T6 a1) -> (T6 a1) -> a2
                  -> () -> a3 -> a3) -> a3 -> (Key0 -> a1 -> a2 -> (T6 
                  a1) -> () -> a3 -> a3) -> (T6 a1) -> a3
fold_rec_weak3 f i x x0 x1 m =
  fold_rec_bis3 f i m x x0 (\k e a m' _ _ x2 -> x1 k e a m' __ x2)

fold_rel3 :: (Key0 -> a1 -> a2 -> a2) -> (Key0 -> a1 -> a3 -> a3) -> a2 -> a3
             -> (T6 a1) -> a4 -> (Key0 -> a1 -> a2 -> a3 -> () -> a4 -> a4)
             -> a4
fold_rel3 f g i j m rempty rstep =
  
    (
      (let {l = rev (elements0 m)} in
       let {rstep' = \k e a b x -> rstep k e a b __ x} in
       list_rect (\_ -> rempty) (\a l0 iHl rstep'0 ->
         rstep'0 (Prelude.fst a) (Prelude.snd a)
           (Data.List.foldr (uncurry3 f) i l0)
           (Data.List.foldr (uncurry3 g) j l0) __
           (iHl (\k e a0 b _ x -> rstep'0 k e a0 b __ x))) l (\k e a b _ x ->
         rstep' k e a b x)))

map_induction3 :: ((T6 a1) -> () -> a2) -> ((T6 a1) -> (T6 a1) -> a2 -> Key0
                  -> a1 -> () -> () -> a2) -> (T6 a1) -> a2
map_induction3 x x0 m =
  fold_rec4 (\_ _ _ -> ()) () m x (\k e _ m' m'' _ _ _ x1 ->
    x0 m' m'' x1 k e __ __)

map_induction_bis3 :: ((T6 a1) -> (T6 a1) -> () -> a2 -> a2) -> a2 -> (Key0
                      -> a1 -> (T6 a1) -> () -> a2 -> a2) -> (T6 a1) -> a2
map_induction_bis3 x x0 x1 m =
  fold_rec_bis3 (\_ _ _ -> ()) () m (\m0 m' _ _ x2 -> x m0 m' __ x2) x0
    (\k e _ m' _ _ x2 -> x1 k e m' __ x2)

cardinal_inv_4 :: (T6 a1) -> Prelude.Int -> ((,) Key0 a1)
cardinal_inv_4 m _ =
  let {l = elements0 m} in
  case l of {
   [] -> false_rect;
   (:) p _ -> p}

cardinal_inv_2b3 :: (T6 a1) -> ((,) Key0 a1)
cardinal_inv_2b3 m =
  let {n = cardinal m} in
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ ->
    false_rect (\x _ -> cardinal_inv_4 m x))
    (\n0 ->
    cardinal_inv_4 m n0)
    n

filter3 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter3 f m =
  fold0 (\k e m0 ->
    case f k e of {
     Prelude.True -> add1 k e m0;
     Prelude.False -> m0}) m empty0

for_all3 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all3 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> b;
     Prelude.False -> Prelude.False}) m Prelude.True

exists_3 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_3 f m =
  fold0 (\k e b ->
    case f k e of {
     Prelude.True -> Prelude.True;
     Prelude.False -> b}) m Prelude.False

partition3 :: (Key0 -> a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition3 f m =
  (,) (filter3 f m) (filter3 (\k e -> Prelude.not (f k e)) m)

update3 :: (T6 a1) -> (T6 a1) -> T6 a1
update3 m1 m2 =
  fold0 add1 m2 m1

restrict3 :: (T6 a1) -> (T6 a1) -> T6 a1
restrict3 m1 m2 =
  filter3 (\k _ -> mem0 k m2) m1

diff3 :: (T6 a1) -> (T6 a1) -> T6 a1
diff3 m1 m2 =
  filter3 (\k _ -> Prelude.not (mem0 k m2)) m1

partition_In3 :: (T6 a1) -> (T6 a1) -> (T6 a1) -> Key0 -> Prelude.Bool
partition_In3 _ m1 _ k =
  in_dec7 m1 k

update_dec3 :: (T6 a1) -> (T6 a1) -> Key0 -> a1 -> Prelude.Bool
update_dec3 _ m' k _ =
  in_dec7 m' k

filter_dom3 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_dom3 f =
  filter3 (\k _ -> f k)

filter_range3 :: (a1 -> Prelude.Bool) -> (T6 a1) -> T6 a1
filter_range3 f =
  filter3 (\_ -> f)

for_all_dom3 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_dom3 f =
  for_all3 (\k _ -> f k)

for_all_range3 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
for_all_range3 f =
  for_all3 (\_ -> f)

exists_dom3 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_dom3 f =
  exists_3 (\k _ -> f k)

exists_range3 :: (a1 -> Prelude.Bool) -> (T6 a1) -> Prelude.Bool
exists_range3 f =
  exists_3 (\_ -> f)

partition_dom3 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_dom3 f =
  partition3 (\k _ -> f k)

partition_range3 :: (a1 -> Prelude.Bool) -> (T6 a1) -> (,) (T6 a1) (T6 a1)
partition_range3 f =
  partition3 (\_ -> f)

eqb12 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb12 x y =
  case eq_dec2 x y of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

in_dec8 :: (T6 a1) -> Key0 -> Prelude.Bool
in_dec8 m x =
  in_dec7 m x

take_first1 :: (Key0 -> a1 -> Prelude.Bool) -> Key0 -> a1 -> (Prelude.Maybe
               ((,) Key0 a1)) -> Prelude.Maybe ((,) Key0 a1)
take_first1 f k e x0 =
  case x0 of {
   Prelude.Just _ -> x0;
   Prelude.Nothing ->
    case f k e of {
     Prelude.True -> Prelude.Just ((,) k e);
     Prelude.False -> Prelude.Nothing}}

singleton1 :: Key0 -> a1 -> T6 a1
singleton1 k e =
  add1 k e empty0

keep_keys1 :: (Key0 -> Prelude.Bool) -> (T6 a1) -> T6 a1
keep_keys1 p =
  filter3 (\k _ -> p k)

reflect_ADT_DSL_computation_Pick :: ADTSig -> ADT ->
                                    (Reflect_ADT_DSL_computation a1) ->
                                    Reflect_ADT_DSL_computation a1
reflect_ADT_DSL_computation_Pick sig adt x =
  reflect_ADT_DSL_computation_simplify sig adt x

type IO a = Prelude.IO a

failIO :: IO a1
failIO =
  Prelude.error "AXIOM TO BE REALIZED"

type Offset = Size

ghcEmptyDSL' :: PS0
ghcEmptyDSL' =
  MakePS0
    (System.IO.Unsafe.unsafePerformIO (Foreign.ForeignPtr.newForeignPtr_ Foreign.Ptr.nullPtr))
    0 0 0

ghcPackDSL' :: ([] Word) -> PS0
ghcPackDSL' xs =
  System.IO.Unsafe.unsafeDupablePerformIO
    ((Data.Function.&) ( ((Data.List.length :: [a] -> Prelude.Int) xs))
      (\len ->
      (\c t e -> if c then t else e) ((Prelude.<) 0 len)
        ((GHC.Base.>>=) (GHC.ForeignPtr.mallocPlainForeignPtrBytes len)
          (\z ->
          (GHC.Base.>>=)
            ((\p off xs -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> HString.pokeArray' (Foreign.Ptr.plusPtr ptr off) xs))
              z 0 xs) (\_ -> Prelude.return (MakePS0 z len 0 len))))
        (Prelude.return (MakePS0
          (System.IO.Unsafe.unsafePerformIO (Foreign.ForeignPtr.newForeignPtr_ Foreign.Ptr.nullPtr))
          0 0 0))))

ghcUnpackDSL' :: PS0 -> [] Word
ghcUnpackDSL' p =
  System.IO.Unsafe.unsafeDupablePerformIO
    ((\p off len -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Marshal.Array.peekArray len (Foreign.Ptr.plusPtr ptr off)))
      (psBuffer0 p) (psOffset0 p) (psLength0 p))

ghcConsDSL' :: PS0 -> Word -> PS0
ghcConsDSL' p w =
  System.IO.Unsafe.unsafeDupablePerformIO
    (case (Prelude.<) 0 (psOffset0 p) of {
      Prelude.True ->
       Prelude.fmap (\_ -> MakePS0 (psBuffer0 p) (psBufLen0 p)
         ((Prelude.-) (psOffset0 p) ((\x -> x) 1))
         ((Prelude.+) (psLength0 p) ((\x -> x) 1)))
         ((\p off w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.pokeByteOff ptr off w))
           (psBuffer0 p) ((Prelude.-) (psOffset0 p) ((\x -> x) 1)) w);
      Prelude.False ->
       case (Prelude.<=) ((Prelude.+) (psLength0 p) ((\x -> x) 1))
              (psBufLen0 p) of {
        Prelude.True ->
         (GHC.Base.>>=)
           ((\p1 o1 p2 o2 sz -> Foreign.ForeignPtr.withForeignPtr p1 (\ptr1 -> Foreign.ForeignPtr.withForeignPtr p2 (\ptr2 -> Foreign.Marshal.Utils.copyBytes (Foreign.Ptr.plusPtr ptr1 o1) (Foreign.Ptr.plusPtr ptr2 o2) sz)))
             (psBuffer0 p) 0 (psBuffer0 p) ((\x -> x) 1) (psLength0 p))
           (\_ ->
           Prelude.fmap (\_ -> MakePS0 (psBuffer0 p) (psBufLen0 p) 0
             ((Prelude.+) (psLength0 p) ((\x -> x) 1)))
             ((\p off w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.pokeByteOff ptr off w))
               (psBuffer0 p) 0 w));
        Prelude.False ->
         case (Prelude.<) 0 (psBufLen0 p) of {
          Prelude.True ->
           (GHC.Base.>>=)
             (GHC.ForeignPtr.mallocPlainForeignPtrBytes
               ((Prelude.+) (psLength0 p) ((\x -> x) 1))) (\cod ->
             (GHC.Base.>>=)
               ((\p1 o1 p2 o2 sz -> Foreign.ForeignPtr.withForeignPtr p1 (\ptr1 -> Foreign.ForeignPtr.withForeignPtr p2 (\ptr2 -> Foreign.Marshal.Utils.copyBytes (Foreign.Ptr.plusPtr ptr1 o1) (Foreign.Ptr.plusPtr ptr2 o2) sz)))
                 (psBuffer0 p) 0 cod ((\x -> x) 1) (psLength0 p)) (\_ ->
               (GHC.Base.>>=)
                 ((\p off w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.pokeByteOff ptr off w))
                   cod 0 w) (\_ ->
                 Prelude.return (MakePS0 cod
                   ((Prelude.+) (psLength0 p) ((\x -> x) 1)) 0
                   ((Prelude.+) (psLength0 p) ((\x -> x) 1))))));
          Prelude.False ->
           (GHC.Base.>>=)
             (GHC.ForeignPtr.mallocPlainForeignPtrBytes ((\x -> x) 1))
             (\cod ->
             (GHC.Base.>>=)
               ((\p off w -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.pokeByteOff ptr off w))
                 cod 0 w) (\_ ->
               Prelude.return (MakePS0 cod ((\x -> x) 1) 0 ((\x -> x) 1))))}}})

ghcUnconsDSL' :: PS0 -> (,) PS0 (Prelude.Maybe Word)
ghcUnconsDSL' p =
  System.IO.Unsafe.unsafeDupablePerformIO
    (case (Prelude.<) 0 (psLength0 p) of {
      Prelude.True ->
       Prelude.fmap (\a -> (,) (MakePS0 (psBuffer0 p) (psBufLen0 p)
         (case eqb0 (psLength0 p) ((\x -> x) 1) of {
           Prelude.True -> 0;
           Prelude.False -> (Prelude.+) (psOffset0 p) ((\x -> x) 1)})
         ((Prelude.-) (psLength0 p) ((\x -> x) 1))) (Prelude.Just a))
         ((\p off -> Foreign.ForeignPtr.withForeignPtr p (\ptr -> Foreign.Storable.peekByteOff ptr off))
           (psBuffer0 p) (psOffset0 p));
      Prelude.False -> Prelude.return ((,) p Prelude.Nothing)})

ghcAppendDSL' :: PS0 -> PS0 -> PS0
ghcAppendDSL' p p0 =
  System.IO.Unsafe.unsafeDupablePerformIO
    (case (Prelude.<) 0 (psLength0 p) of {
      Prelude.True ->
       case (Prelude.<) 0 (psLength0 p0) of {
        Prelude.True ->
         (GHC.Base.>>=)
           (GHC.ForeignPtr.mallocPlainForeignPtrBytes
             ((Prelude.+) (psLength0 p) (psLength0 p0))) (\cod ->
           (GHC.Base.>>=)
             ((\p1 o1 p2 o2 sz -> Foreign.ForeignPtr.withForeignPtr p1 (\ptr1 -> Foreign.ForeignPtr.withForeignPtr p2 (\ptr2 -> Foreign.Marshal.Utils.copyBytes (Foreign.Ptr.plusPtr ptr1 o1) (Foreign.Ptr.plusPtr ptr2 o2) sz)))
               (psBuffer0 p) (psOffset0 p) cod 0 (psLength0 p)) (\_ ->
             (GHC.Base.>>=)
               ((\p1 o1 p2 o2 sz -> Foreign.ForeignPtr.withForeignPtr p1 (\ptr1 -> Foreign.ForeignPtr.withForeignPtr p2 (\ptr2 -> Foreign.Marshal.Utils.copyBytes (Foreign.Ptr.plusPtr ptr1 o1) (Foreign.Ptr.plusPtr ptr2 o2) sz)))
                 (psBuffer0 p0) (psOffset0 p0) cod (psLength0 p)
                 (psLength0 p0)) (\_ ->
               Prelude.return (MakePS0 cod
                 ((Prelude.+) (psLength0 p) (psLength0 p0)) 0
                 ((Prelude.+) (psLength0 p) (psLength0 p0))))));
        Prelude.False -> Prelude.return p};
      Prelude.False -> Prelude.return p0})

