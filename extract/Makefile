all: Makefile.coq
	rm -f ByteStringExt.hs
	make -f Makefile.coq
	perl -i fixcode.pl ByteStringExt.hs
	nix-cabal-build

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f *.glob *.v.d *.vo *.hi *.o Main result *.hp .*.aux
	rm -f bytestring-fiat ByteStringExt.hs
