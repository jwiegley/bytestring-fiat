#!/usr/bin/env perl

$imports = <<'END_IMPORTS';
import qualified Data.ByteString.Fiat.HString as HString
import qualified Data.Char
import qualified Data.Function
import qualified Data.List
import qualified Data.Maybe
import qualified Data.Ratio
import qualified Data.Word
import qualified Foreign.Marshal.Alloc
import qualified Foreign.Marshal.Utils
import qualified Foreign.Ptr
import qualified Foreign.Storable
import qualified GHC.Real
import qualified Prelude
import qualified System.IO.Unsafe
END_IMPORTS

while (<>) {
    next if /^ghcDenote ::/ .. /^$/;
    next if /^heapSpec0 ::/ .. /^$/;
    next if /^heapCanonical0 ::/ .. /^$/;
    next if /^byteStringHeap0 ::/ .. /^$/;

    next if /^emptyDSL ::/ .. /^$/;
    next if /^ghcEmptyDSL ::/ .. /^$/;
    next if /^packDSL ::/ .. /^$/;
    next if /^ghcPackDSL ::/ .. /^$/;
    next if /^unpackDSL ::/ .. /^$/;
    next if /^ghcUnpackDSL ::/ .. /^$/;
    next if /^consDSL ::/ .. /^$/;
    next if /^ghcConsDSL ::/ .. /^$/;
    next if /^unconsDSL ::/ .. /^$/;
    next if /^ghcUnconsDSL ::/ .. /^$/;
    next if /^appendDSL ::/ .. /^$/;
    next if /^ghcAppendDSL ::/ .. /^$/;

    s/'\\000'/0/g;
    s/ByteStringExt/Data.ByteString.Fiat.Internal/;
    s/import qualified Prelude/$imports/;
    s/unsafeCoerce :: a -> b/--unsafeCoerce :: a -> b/;
    s/\bfun /\\/;
    s/\brec\b/rec_/;
    s/\(=\)/(Prelude.==)/;
    s/\(<=\)/(Prelude.<=)/;
    s/\(<\)/(Prelude.<)/;
    s/\(>\)/(Prelude.>)/;
    s/\(\+\)/(Prelude.+)/;
    s/\(==\)/(Prelude.==)/;
    # s/type (Key0?) = .+/type $1 = Foreign.Ptr.Ptr Word/;
    # s/type Ptr a = Foreign\.Ptr\.Ptr Data\.Word\.Word8/type Ptr a = Prelude.Int/;
    s/Pervasives\.min/(Prelude.min)/;
    s/Pervasives\.max/(Prelude.max)/;
    s/if n>m then None else Some \(n<m\)/if n Prelude.> m then Prelude.Nothing else Prelude.Just \(n Prelude.< m\)/;
    s/b = \(Prelude\.<=\) \(\(Prelude.succ\)/b = ((Prelude.<=) :: Prelude.Double -> Prelude.Double -> Prelude.Bool) ((Prelude.succ)/;
    s/getcMethDef n' methSigs methDefs \(unsafeCoerce idx\)/getcMethDef n' methSigs (unsafeCoerce methDefs) (unsafeCoerce idx)/;
    s/Prelude.True -> seval_production_coords pt0 seval_productions0/Prelude.True -> unsafeCoerce seval_production_coords pt0 seval_productions0/;
    s/\(ilist2_tl \(HString\.nsucc/(unsafeCoerce (ilist2_tl (HString.nsucc/;
    s/          components\)\)}/          components)))}/;
    print;
}
